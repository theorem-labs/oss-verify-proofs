(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_core_exp_mod_working_limbs () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "exp_mod_working_limbs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_exp_mod_working_limbs_post"].


Definition U_MPI_CORE_EXP_MOD_WORKING_LIMBS : Z := 0x24558.

(* [comment removed for export] *)
Definition exp_mod_welem (en : Z) : Z := if 79 <? 32 * en then 8 else 2.
Definition exp_mod_working_limbs (an en : Z) : Z := exp_mod_welem en * an + an + (2 * an + 1).

Definition mpi_core_exp_mod_working_limbs_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (an en : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_exp_mod_working_limbs ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(3.(4.$0.R10.(5.(6.O15.O14.O13.O12.R?.R>.R=.O11.O10.R<.R;.R:.R9.R8.R7.R6.R5.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R4.R3.R2.R1.)O5.(7.O15.)O4.(8.(2.&40.))O1.(9.O16.)))(3.(:.(;.$<.)O1.O1.)(3.(=.O16.O1.O1.)(3.(>.O16.O1.)(4.(2.&40.)R<.(?.&40.(10.O3.O2.))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_exp_mod_working_limbs_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_exp_mod_working_limbs ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(11.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(12.(2.&8.))Pan,$13.Pen,$13.P,(3.(14.=R2.)(14.R2.+2710.))P,(3.(14.=R2.)(14.R2.+2710.))P,(>.O2.R5.)P,(4.(2.&40.)R1>.(?.&40.R5.))P,(4.(2.&40.)R1>.(?.&40.R5.))(15.O2.(16.O2.R29.R28.R27.R26.R22.R21.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R:.R9.R7.R6.R8.)(5.(6.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)R:.(?.&40.O1.)R9.(8.(2.&40.))R8.(9.O2.)))")
(* [comment removed for export] *).

Lemma U_mpi_core_exp_mod_working_limbs_spec : mpi_core_exp_mod_working_limbs_stmt usegs U_MPI_CORE_EXP_MOD_WORKING_LIMBS.
Proof.
  unfold mpi_core_exp_mod_working_limbs_stmt, U_MPI_CORE_EXP_MOD_WORKING_LIMBS.
  intros until en. intros Han Hen MI -> ->.
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
  zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  all: repeat (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) => fail | _ => zstep end).
  all: finish; unfold exp_mod_working_limbs, exp_mod_welem;
       first [ replace (79 <? 32 * en) with false by (symmetry; apply Z.ltb_ge; lia)
             | replace (79 <? 32 * en) with true by (symmetry; apply Z.ltb_lt; lia) ];
       f_equal; rewrite !Z.shiftl_mul_pow2 by lia; lia.
Qed.
