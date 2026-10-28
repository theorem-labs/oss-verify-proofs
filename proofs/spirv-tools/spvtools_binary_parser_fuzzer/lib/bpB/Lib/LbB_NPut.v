(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt LbB_NSnp LbB_NKit LbB_NIf LbB_NStage.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_NOp64 LbB_NOp16 LbB_NOp32 LbB_NOpI.
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
      nmid R M sp ds LbB_NOp64.OP_FR PADRA_UL LbB_NOp64.OP_RET (Z_to_bv 64 32) (LbB_NOp64.SVOP R ds ret) sv9 sv18 sv19 sv20 sv21
           (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) nc R1 M1.

  Theorem put_u64_okA : put_num_td H APUT_U64 0 (2 ^ 64) (fun x => x).
  Proof.
    unfold put_num_td, put_num_stmtA. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len x DB PRE Ha0 Ha1 Hx REP PERM DSOB DSIN LEN BS BL.
    apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
    eapply (np_main H HHbp TDLAW APUT_U64 LbB_NOp64.OP_FR LbB_NOp64.op_xok INT64 ltac:(left; reflexivity));
      [ | | exact PRE | exact Ha0 | exact Ha1 | exact Hx | exact REPW | exact PERM | exact DSOB | exact DSIN | exact LEN | exact BS | exact BL].
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK.
      destruct (LbB_NOp64.ex_a H HH F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK) as (nc & R2 & M2 & sv9 & sv18 & sv19 & sv20 & sv21 & Hms & NM).
      exists nc, R2, M2. split; [exact Hms|]. split; [eapply nmidP_of_nmid; exact NM|]. exists sv9, sv18, sv19, sv20, sv21. exact NM.
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd nc R1 M1 R' M' NP XOK (sv9 & sv18 & sv19 & sv20 & sv21 & NM) NB.
      eapply LbB_NOp64.ex_b; eassumption.
  Qed.

  Definition INT16 (R : bvmap 5 word) (M : mem) (sp ds ret nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop :=
    exists sv9 sv18 sv19 sv20 sv21,
      nmid R M sp ds LbB_NOp16.OP_FR PADRA_UL LbB_NOp16.OP_RET (Z_to_bv 64 32) (LbB_NOp16.SVOP R ds ret) sv9 sv18 sv19 sv20 sv21
           (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) nc R1 M1.

  Theorem put_u16_okA : put_num_td H APUT_U16 0 (2 ^ 16) (fun x => x).
  Proof.
    unfold put_num_td, put_num_stmtA. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len x DB PRE Ha0 Ha1 Hx REP PERM DSOB DSIN LEN BS BL.
    apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
    eapply (np_main H HHbp TDLAW APUT_U16 LbB_NOp16.OP_FR LbB_NOp16.op_xok INT16 ltac:(left; reflexivity));
      [ | | exact PRE | exact Ha0 | exact Ha1 | exact Hx | exact REPW | exact PERM | exact DSOB | exact DSIN | exact LEN | exact BS | exact BL].
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK.
      destruct (LbB_NOp16.ex_a H HH F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK) as (nc & R2 & M2 & sv9 & sv18 & sv19 & sv20 & sv21 & Hms & NM).
      exists nc, R2, M2. split; [exact Hms|]. split; [eapply nmidP_of_nmid; exact NM|]. exists sv9, sv18, sv19, sv20, sv21. exact NM.
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd nc R1 M1 R' M' NP XOK (sv9 & sv18 & sv19 & sv20 & sv21 & NM) NB.
      eapply LbB_NOp16.ex_b; eassumption.
  Qed.

  Definition INT32 (R : bvmap 5 word) (M : mem) (sp ds ret nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop :=
    exists sv9 sv18 sv19 sv20 sv21,
      nmid R M sp ds LbB_NOp32.OP_FR PADRA_UL LbB_NOp32.OP_RET (Z_to_bv 64 32) (LbB_NOp32.SVOP R ds ret) sv9 sv18 sv19 sv20 sv21
           (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) nc R1 M1.

  Theorem put_u32_okA : put_num_td H APUT_U32 0 (2 ^ 32) sx32.
  Proof.
    unfold put_num_td, put_num_stmtA. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len x DB PRE Ha0 Ha1 Hx REP PERM DSOB DSIN LEN BS BL.
    apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
    eapply (np_main H HHbp TDLAW APUT_U32 LbB_NOp32.OP_FR LbB_NOp32.op_xok INT32 ltac:(left; reflexivity));
      [ | | exact PRE | exact Ha0 | exact Ha1 | exists x; split; [exact Hx | reflexivity] | exact REPW | exact PERM | exact DSOB | exact DSIN | exact LEN | exact BS | exact BL].
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK.
      destruct (LbB_NOp32.ex_a H HH F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK) as (nc & R2 & M2 & sv9 & sv18 & sv19 & sv20 & sv21 & Hms & NM).
      exists nc, R2, M2. split; [exact Hms|]. split; [eapply nmidP_of_nmid; exact NM|]. exists sv9, sv18, sv19, sv20, sv21. exact NM.
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd nc R1 M1 R' M' NP XOK (sv9 & sv18 & sv19 & sv20 & sv21 & NM) NB.
      eapply LbB_NOp32.ex_b; eassumption.
  Qed.

  Definition INTI (R : bvmap 5 word) (M : mem) (sp ds ret nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop :=
    exists sv9 sv18 sv19 sv20 sv21 sv22,
      nmid R M sp ds LbB_NOpI.OP_FR PADRA_L LbB_NOpI.OP_RET (Z_to_bv 64 32) (LbB_NOpI.SVOP R ds ret) sv9 sv18 sv19 sv20 sv21
           sv22 (PropExec.getr R 23%bv) nc R1 M1.

  Theorem put_int_okA : put_num_td H APUT_INT 0 (2 ^ 31) (fun x => x mod 2 ^ 64).
  Proof.
    unfold put_num_td, put_num_stmtA. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len x DB PRE Ha0 Ha1 Hx REP PERM DSOB DSIN LEN BS BL.
    apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
    eapply (np_main H HHbp TDLAW APUT_INT LbB_NOpI.OP_FR LbB_NOpI.op_xok INTI ltac:(right; reflexivity));
      [ | | exact PRE | exact Ha0 | exact Ha1 | unfold LbB_NOpI.op_xok; rewrite Z.mod_small by (clear - Hx; lia); exact Hx | exact REPW | exact PERM | exact DSOB | exact DSIN | exact LEN | exact BS | exact BL].
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK.
      destruct (LbB_NOpI.ex_a H HH F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd NP XOK) as (nc & R2 & M2 & sv9 & sv18 & sv19 & sv20 & sv21 & sv22 & Hms & NM).
      exists nc, R2, M2. split; [exact Hms|]. split; [eapply nmidP_of_nmid; exact NM|]. exists sv9, sv18, sv19, sv20, sv21, sv22. exact NM.
    - intros F' fc' R M sp' ds' xenc fl' fill' ret lo' shi' gd nc R1 M1 R' M' NP XOK (sv9 & sv18 & sv19 & sv20 & sv21 & sv22 & NM) NB.
      eapply LbB_NOpI.ex_b; eassumption.
  Qed.

  Corollary put_u16_ok : put_u16_stmtA H LINV_P5 ds_repA0.   Proof. exact put_u16_okA. Qed.
  Corollary put_u32_ok : put_u32_stmtA H LINV_P5 ds_repA0.   Proof. exact put_u32_okA. Qed.
  Corollary put_u64_ok : put_u64_stmtA H LINV_P5 ds_repA0.   Proof. exact put_u64_okA. Qed.
  Corollary put_int_ok : put_int_stmtA H LINV_P5 ds_repA0.   Proof. exact put_int_okA. Qed.
End Put.
