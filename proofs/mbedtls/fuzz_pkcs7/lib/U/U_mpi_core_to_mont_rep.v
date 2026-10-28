(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_core_montmul.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_core_to_mont_rep () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_montmul.MPI_CORE_MONTMUL_STACK"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_montmul.mpi_core_montmul_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Definition U_MPI_CORE_TO_MONT_REP : Z := 0x24c30.

Definition mpi_core_to_mont_rep_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_to_mont_rep ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PX,$3.PA,$3.PRR,$3.PN,$3.Pan,$3.PT,$3.Plo,$3.Pxs,(4.(0.&40.))Pys,(4.(0.&40.))Prs,(4.(0.&40.))Pns,(4.(0.&40.))Pts,(4.(0.&40.))P,(5.O2.R=.R<.R5.)P,(6.O2.R>.R<.(7.R5.))P,(6.O2.R?.R<.(7.R5.))P,(6.O2.R10.R<.(7.R5.))P,(5.O2.R11.R;.R5.)P,(8.(9.+1.R=.)(9.R=.+1387.))P,(9.R>.(:.(;.(0.&40.)R;.)))P,(9.R?.(:.(;.(0.&40.)R;.)))P,(9.R10.(:.(;.(0.&40.)R;.)))P,(9.R11.(:.(;.(0.&40.)R;.)))P,(9.(<.(=.+2.R12.)+1.)(:.(;.(0.&40.)R;.)))P,(>.(9.(<.R17.(=.+4.(:.(;.(0.&40.)R10.))))R12.)(9.(<.R12.(=.+4.(:.(;.(0.&40.)R<.))))R17.))P,(>.(9.(<.R17.(=.+4.(:.(;.(0.&40.)R10.))))R13.)(9.(<.R13.(=.+4.(:.(;.(0.&40.)R=.))))R17.))P,(>.(9.(<.R17.(=.+4.(:.(;.(0.&40.)R10.))))R14.)(9.(<.R14.(=.+4.(:.(;.(0.&40.)R>.))))R17.))P,(>.(9.(<.R17.(=.+4.(:.(;.(0.&40.)R10.))))R15.)(9.(<.R15.(=.+4.(:.(;.(0.&40.)R?.))))R17.))P,(>.(9.(<.R18.(=.+4.(:.(;.(0.&40.)R11.))))R1;.)(9.(<.R1;.(=.+4.(:.(;.(0.&40.)R14.))))R18.))P,(?.$3.(10.R1<.+4.)=)P,(?.$3.(10.R1<.+4.)=)P,(?.$3.(10.R1<.+4.)=)P,(?.$3.(10.R1<.+4.)=)P,(?.$3.(10.R1;.+4.)=)P,(11.=R21.)P,(11.=R21.)P,(11.=R21.)P,(11.=R21.)P,(11.=R20.)P,(11.(<.R26.(=.+4.(:.(;.(0.&40.)R1?.))))(12.+2.+40.))P,(11.(<.R26.(=.+4.(:.(;.(0.&40.)R1?.))))(12.+2.+40.))P,(11.(<.R26.(=.+4.(:.(;.(0.&40.)R1?.))))(12.+2.+40.))P,(11.(<.R26.(=.+4.(:.(;.(0.&40.)R1?.))))(12.+2.+40.))P,(11.(<.R25.(=.+4.(:.(;.(0.&40.)R1?.))))(12.+2.+40.))P,(13.O2.R2<.R25.(14.&40.R4<.))P,(9.R26.(15.(14.&40.R4=.)$16.))P,(?.$3.(10.(14.&40.R4>.)+10.)=)P,(>.(9.(<.R2>.(=.+4.(:.(;.(0.&40.)R27.))))R28.)(9.(14.&40.R4?.)R2>.))P,(>.(9.(<.R2>.(=.+4.(:.(;.(0.&40.)R27.))))R29.)(9.(14.&40.R50.)R2>.))P,(>.(9.(<.R2>.(=.+4.(:.(;.(0.&40.)R27.))))R2:.)(9.(14.&40.R51.)R2>.))P,(>.(9.(<.R2>.(=.+4.(:.(;.(0.&40.)R27.))))R2;.)(9.(14.&40.R52.)R2>.))P,(>.(9.(<.R2=.(=.+4.(:.(;.(0.&40.)R27.))))R2<.)(9.(14.&40.R53.)R2=.))P,(17.O2.R34.)P,(?.$3.(10.(14.&40.R56.)+2.)=)P,(?.(0.&40.)R4>.(18.&40.R35.))P,(?.(0.&40.)R4>.(18.&40.R35.))P,(?.(0.&40.)R4>.(18.&40.R34.))P,(?.(0.&40.)R4>.(18.&40.R34.))P,(?.(0.&40.)R4=.(18.&40.R37.))P,(?.(0.&40.)R4=.(18.&40.R35.))(19.O2.(1:.O2.R5=.R5<.R5;.R5:.R56.R55.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R3>.R3=.R3;.R37.R36.R34.R30.R35.R3<.)(1;.(1<.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.)R3>.(18.&40.O1.)R3=.(1=.(0.&40.))R3<.(1>.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma U_mpi_core_to_mont_rep_spec : mpi_core_to_mont_rep_stmt usegs U_MPI_CORE_TO_MONT_REP.
Proof.
  unfold mpi_core_to_mont_rep_stmt, U_MPI_CORE_TO_MONT_REP.
  intros until ts. intros HX HA HR HN HT Han LX LA LR LN LT D1 D2 D3 D4 D5 AL1 AL2 AL3 AL4 AL5 NZ1 NZ2 NZ3 NZ4 NZ5 T1 T2 T3 T4 T5
         ST LO SPA S1 S2 S3 S4 S5 MI RA -> -> -> -> -> ->.
  zstep. zstep. zstep. zstep. zstep. zstep.
  pose proof U_mpi_core_montmul_spec as SP. unfold mpi_core_montmul_stmt, U_MPI_CORE_MONTMUL in SP.
  eapply SP with (B := RR) (bn := an) (zs := rs) (ys := ys) (ns := ns); try reflexivity; try eassumption; try lia.
Qed.
