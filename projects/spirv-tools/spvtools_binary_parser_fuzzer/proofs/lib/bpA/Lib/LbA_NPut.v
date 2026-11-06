(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HArr HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface RtA_Td.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_Own.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_DiagStmt LbA_DStat LbA_DRep LbA_DKit LbA_DKitN.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PcStmt LbA_NSnp LbA_NKit LbA_NIf LbA_NStage.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_NOp64 LbA_NOp16 LbA_NOp32 LbA_NOpI.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition put_num_td {HCEIL : HeapCeil} (H : asr) (entry lo_x hi_x : Z) (enc : Z -> Z) : Prop :=
  put_num_stmtA H LINV_P5 ds_repA0 entry lo_x hi_x enc.

Section Put.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Hypothesis TDLAW : td_law H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Definition INT64 (R : bvmap 5 word) (M : mem) (sp ds ret nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop :=
    exists sv9 sv18 sv19 sv20 sv21,
      nmid R M sp ds LbA_NOp64.OP_FR PADRA_UL LbA_NOp64.OP_RET (Z_to_bv 64 32) (LbA_NOp64.SVOP R ds ret) sv9 sv18 sv19 sv20 sv21
           (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) nc R1 M1.

  Theorem put_u64_okA : put_num_td H APUT_U64 0 (2 ^ 64) (fun x => x).
  Proof.
    unfold put_num_td, put_num_stmtA. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len x DB PRE Ha0 Ha1 Hx REP PERM DSOB DSIN LEN BS BL.
    apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
    eapply (np_main H HHbp TDLAW APUT_U64 LbA_NOp64.OP_FR LbA_NOp64.op_xok INT64 ltac:(left; reflexivity));
      [ | | exact PRE | exact Ha0 | exact Ha1 | exact Hx | exact REPW | exact PERM | exact DSOB | exact DSIN | exact LEN | exact BS | exact BL].
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK.
      destruct (LbA_NOp64.ex_a H HH F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK) as (nc & R2 & M2 & sv9 & sv18 & sv19 & sv20 & sv21 & Hms & NM).
      exists nc, R2, M2. split; [exact Hms|]. split; [eapply nmidP_of_nmid; exact NM|]. exists sv9, sv18, sv19, sv20, sv21. exact NM.
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd nc R1 M1 R' M' NP XOK (sv9 & sv18 & sv19 & sv20 & sv21 & NM) NB.
      eapply LbA_NOp64.ex_b; eassumption.
  Qed.

  Definition INT16 (R : bvmap 5 word) (M : mem) (sp ds ret nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop :=
    exists sv9 sv18 sv19 sv20 sv21,
      nmid R M sp ds LbA_NOp16.OP_FR PADRA_UL LbA_NOp16.OP_RET (Z_to_bv 64 32) (LbA_NOp16.SVOP R ds ret) sv9 sv18 sv19 sv20 sv21
           (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) nc R1 M1.

  Theorem put_u16_okA : put_num_td H APUT_U16 0 (2 ^ 16) (fun x => x).
  Proof.
    unfold put_num_td, put_num_stmtA. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len x DB PRE Ha0 Ha1 Hx REP PERM DSOB DSIN LEN BS BL.
    apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
    eapply (np_main H HHbp TDLAW APUT_U16 LbA_NOp16.OP_FR LbA_NOp16.op_xok INT16 ltac:(left; reflexivity));
      [ | | exact PRE | exact Ha0 | exact Ha1 | exact Hx | exact REPW | exact PERM | exact DSOB | exact DSIN | exact LEN | exact BS | exact BL].
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK.
      destruct (LbA_NOp16.ex_a H HH F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK) as (nc & R2 & M2 & sv9 & sv18 & sv19 & sv20 & sv21 & Hms & NM).
      exists nc, R2, M2. split; [exact Hms|]. split; [eapply nmidP_of_nmid; exact NM|]. exists sv9, sv18, sv19, sv20, sv21. exact NM.
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd nc R1 M1 R' M' NP XOK (sv9 & sv18 & sv19 & sv20 & sv21 & NM) NB.
      eapply LbA_NOp16.ex_b; eassumption.
  Qed.

  Definition INT32 (R : bvmap 5 word) (M : mem) (sp ds ret nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop :=
    exists sv9 sv18 sv19 sv20 sv21,
      nmid R M sp ds LbA_NOp32.OP_FR PADRA_UL LbA_NOp32.OP_RET (Z_to_bv 64 32) (LbA_NOp32.SVOP R ds ret) sv9 sv18 sv19 sv20 sv21
           (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) nc R1 M1.

  Theorem put_u32_okA : put_num_td H APUT_U32 0 (2 ^ 32) sx32.
  Proof.
    unfold put_num_td, put_num_stmtA. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len x DB PRE Ha0 Ha1 Hx REP PERM DSOB DSIN LEN BS BL.
    apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
    eapply (np_main H HHbp TDLAW APUT_U32 LbA_NOp32.OP_FR LbA_NOp32.op_xok INT32 ltac:(left; reflexivity));
      [ | | exact PRE | exact Ha0 | exact Ha1 | exists x; split; [exact Hx | reflexivity] | exact REPW | exact PERM | exact DSOB | exact DSIN | exact LEN | exact BS | exact BL].
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK.
      destruct (LbA_NOp32.ex_a H HH F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK) as (nc & R2 & M2 & sv9 & sv18 & sv19 & sv20 & sv21 & Hms & NM).
      exists nc, R2, M2. split; [exact Hms|]. split; [eapply nmidP_of_nmid; exact NM|]. exists sv9, sv18, sv19, sv20, sv21. exact NM.
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd nc R1 M1 R' M' NP XOK (sv9 & sv18 & sv19 & sv20 & sv21 & NM) NB.
      eapply LbA_NOp32.ex_b; eassumption.
  Qed.

  Definition INTI (R : bvmap 5 word) (M : mem) (sp ds ret nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop :=
    exists sv9 sv18 sv19 sv20 sv21 sv22,
      nmid R M sp ds LbA_NOpI.OP_FR PADRA_L LbA_NOpI.OP_RET (Z_to_bv 64 32) (LbA_NOpI.SVOP R ds ret) sv9 sv18 sv19 sv20 sv21
           sv22 (PropExec.getr R 23%bv) nc R1 M1.

  Theorem put_int_okA : put_num_td H APUT_INT 0 (2 ^ 31) (fun x => x mod 2 ^ 64).
  Proof.
    unfold put_num_td, put_num_stmtA. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len x DB PRE Ha0 Ha1 Hx REP PERM DSOB DSIN LEN BS BL.
    apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
    eapply (np_main H HHbp TDLAW APUT_INT LbA_NOpI.OP_FR LbA_NOpI.op_xok INTI ltac:(right; reflexivity));
      [ | | exact PRE | exact Ha0 | exact Ha1 | unfold LbA_NOpI.op_xok; rewrite Z.mod_small by (clear - Hx; lia); exact Hx | exact REPW | exact PERM | exact DSOB | exact DSIN | exact LEN | exact BS | exact BL].
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK.
      destruct (LbA_NOpI.ex_a H HH F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK) as (nc & R2 & M2 & sv9 & sv18 & sv19 & sv20 & sv21 & sv22 & Hms & NM).
      exists nc, R2, M2. split; [exact Hms|]. split; [eapply nmidP_of_nmid; exact NM|]. exists sv9, sv18, sv19, sv20, sv21, sv22. exact NM.
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd nc R1 M1 R' M' NP XOK (sv9 & sv18 & sv19 & sv20 & sv21 & sv22 & NM) NB.
      eapply LbA_NOpI.ex_b; eassumption.
  Qed.

  Corollary put_u16_ok : put_u16_stmtA H LINV_P5 ds_repA0.   Proof. exact put_u16_okA. Qed.
  Corollary put_u32_ok : put_u32_stmtA H LINV_P5 ds_repA0.   Proof. exact put_u32_okA. Qed.
  Corollary put_u64_ok : put_u64_stmtA H LINV_P5 ds_repA0.   Proof. exact put_u64_okA. Qed.
  Corollary put_int_ok : put_int_stmtA H LINV_P5 ds_repA0.   Proof. exact put_int_okA. Qed.
End Put.
