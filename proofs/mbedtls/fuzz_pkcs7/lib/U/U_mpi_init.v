(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_init () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_init_post"].


Definition U_MPI_INIT : Z := 0x1f488.

Definition mpi_init_post (segs : list Segment)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (X : Z) (pad : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_init ()) "Lms',$0.(1.(2.&40.)La1,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R3.(6.(7.O23.O22.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.R2.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)O5.(8.O23.)O4.(9.(2.&40.))R1.(:.O24.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.O3.(10.O3.+10.))(11.(=.$>.$>.)))O1.R1.)(4.(12.O24.O1.R1.)(4.(13.O24.R1.)(14.O24.R1.O3.(15.=(16.&40.+1.)=O2.))))))))")
(* [comment removed for export] *).

Definition mpi_init_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_init ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$>.Pp0,$>.Pn0,$>.Ps0w,(2.&40.)Ppad,(2.&40.)P,(14.O2.R6.R5.(15.R4.R2.R3.R1.))P,(5.$>.(18.R6.+8.)=)P,(19.=R7.)P,(13.O2.R9.)P,(5.(2.&40.)R22.(16.&40.R9.))(1:.O2.(1;.O2.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R:.R6.R;.)(6.(7.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(16.&40.O1.)R<.(9.(2.&40.))R;.(:.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma U_mpi_init_spec : mpi_init_stmt usegs U_MPI_INIT.
Proof.
  (* [comment removed for export] *)
  unfold mpi_init_stmt, U_MPI_INIT.
  intros until pad.
  intros CH AL XP MI ->.
  try (unfold mpi_cells in CH).
  pose proof (rw_cells_bound _ _ _ _ CH) as XB.
  cbn [cells_size csize Nat.add] in XB.
  pose proof (rw_cells_join_C2C2 usegs m X [C8 (Z_to_bv 64 p0)] s0w (Z_to_bv 64 n0) [C4 pad] CH) as CH4.
  try (cbn [app] in CH4).
  clear CH.
  pose proof (munch_refl [(X, X + 16)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  lxp_run (PLAN [] [] 24%N).
  lxp_ret.
  (* [comment removed for export] *)
Qed.
