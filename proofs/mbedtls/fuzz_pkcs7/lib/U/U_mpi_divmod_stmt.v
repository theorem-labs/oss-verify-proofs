(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_addsub.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_divmod_stmt () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "exp_mod_R"].


Definition MBEDTLS_ERR_MPI_DIVISION_BY_ZERO : Z := -12.

Notation MPI_DIV_MPI_STACK := 512 (only parsing).
Notation MPI_MOD_MPI_STACK := 576 (only parsing).

(* [comment removed for export] *)
Definition mod_mpi_R (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  ( (r = 0 -> 0 <= mpd_val dX' < mpd_abs dB) /\ -2^31 < r <= 0 )
  /\ binop_keep LB dX dX'.

(* [comment removed for export] *)
Definition mpi_binop_stmt_nb (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF STACK : Z)
    (R : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_divmod_stmt ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.O7.O6.O5.)PLB,(5.$6.)PdX,$7.PdA,$7.PdB,$7.Plo,$8.P,(9.O7.O6.O5.R6.R5.R8.R7.)P,(:.O7.R9.R6.R5.)P,(:.O7.R:.R7.R5.)P,(:.O7.R;.R8.R5.)P,(;.R8.R7.)P,(;.R9.R7.)P,(;.R9.R8.)P,(<.(=.$>.(?.R;.)$10.))P,(<.(=.$8.(11.R<.)(11.R:.)))P,(12.R=.R<.R:.(13.&40.R31.))P,(12.R>.R<.R;.(13.&40.R32.))P,(14.O6.R10.R<.(11.R>.)+10.)P,P,(=.$>.(?.R?.)$15.)(14.O6.R12.R>.(16.R10.)(17.+4.(18.R10.)))P,(14.O6.R12.R>.(11.R?.)+10.)P,P,(=.$>.(?.R10.)$15.)(14.O6.R14.R10.(16.R11.)(17.+4.(18.R11.)))P,(19.O6.R14.(13.&40.R37.)(1:.O7.O6.O5.R15.)R13.)P,P,(<.(=.$>.(?.R14.)$1;.))(1<.(1=.(1>.(16.R15.)(17.+4.(18.R15.)))R12.)(1=.(13.&40.R39.)(16.R15.)))P,(1?.O7.R19.R12.(13.&40.R39.))P,(1=.R13.(20.(20.(13.&40.R3:.)O2.)(21.O6.)))P,(1=.(22.O6.)R14.)P,(1=.(13.&40.R3<.)(1:.O7.O6.O5.R1:.))P,(=.$8.(23.(13.&40.R3=.)+10.)=)P,(1=.(24.O6.)(22.O6.))P,(=.(0.&40.)R3=.(25.&40.(26.O6.)))P,(27.O7.R20.)P,(28.O7.O6.R21.)P,(29.O6.O3.+8.)P,(=.(0.&40.)R3;.(25.&40.(11.R1?.)))P,(=.(0.&40.)R3;.(25.&40.(11.R1?.)))P,(=.(0.&40.)R3;.(25.&40.(11.R1?.)))(2:.O7.R25.(2;.O7.O6.O5.R47.R46.R45.R44.R40.R3?.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R28.R27.R24.R23.R22.A4.O1.R23.R22.R21.R20.R1?.R26.R25.)(2<.(2=.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)R28.(25.&40.O4.)R27.(2>.(0.&40.))R26.(2?.O7.)))")
(* [comment removed for export] *).

Definition mpi_mod_mpi_stmt segs L HI ENTRY MSF := mpi_binop_stmt_nb segs L HI ENTRY MSF MPI_MOD_MPI_STACK mod_mpi_R.

(* [comment removed for export] *)
Definition div_mpi_rem_R (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  ( -2^31 < r <= 0 /\ (r = 0 -> 0 < mpd_abs dB) )
  /\ binop_keep LB dX dX'.     (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation MPI_EXP_MOD_STACK := 720 (only parsing).
Definition MBEDTLS_ERR_MPI_BAD_INPUT_DATA : Z := -4.

(* [comment removed for export] *)
Definition exp_mod_R (LB : list blk) (dX dA dE dN : mpd) (r : Z) (dX' : mpd) : Prop :=
  -2^31 < r <= 0 /\ binop_keep LB dX dX'.

Definition mpi_exp_mod_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_divmod_stmt ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.O5.O4.O3.)PLB,(5.$6.)PdX,$7.PdA,$7.PdE,$7.PdN,$7.Plo,$8.P,(9.O5.O4.O3.R7.R6.R9.R8.)P,(:.O5.R:.R7.R6.)P,(:.O5.R;.R8.R6.)P,(:.O5.R<.R9.R6.)P,(:.O5.R=.R:.R6.)P,(;.R:.R9.)P,(<.(=.$8.(11.R;.)(11.R9.)))P,(<.(=.$8.(11.R<.)(11.R9.)))P,(<.(=.$>.(?.R=.)$10.))P,(12.R>.R=.R:.(13.&40.R32.))P,(12.R?.R=.R;.(13.&40.R33.))P,(12.R10.R=.R<.(13.&40.R34.))P,(14.O4.R12.R=.(11.R10.)+10.)P,P,(=.$>.(?.R11.)$15.)(14.O4.R14.R?.(16.R12.)(17.+4.(18.R12.)))P,(14.O4.R14.R?.(11.R11.)+10.)P,P,(=.$>.(?.R12.)$15.)(14.O4.R16.R11.(16.R13.)(17.+4.(18.R13.)))P,(14.O4.R16.R11.(11.R12.)+10.)P,P,(=.$>.(?.R13.)$15.)(14.O4.R18.R13.(16.R14.)(17.+4.(18.R14.)))P,(19.O4.R18.(13.&40.R3;.)(1:.O5.O4.O3.R19.)R17.)P,P,(<.(=.$>.(?.R18.)$1;.))(1<.(1=.(1>.(16.R19.)(17.+4.(18.R19.)))R15.)(1=.(13.&40.R3=.)(16.R19.)))P,(1?.O5.R1=.R15.(13.&40.R3=.))P,(1=.R16.(20.(20.(13.&40.R3>.)+2=0.)(21.O4.)))P,(1=.(22.O4.)R17.)P,(1=.(13.&40.R40.)(1:.O5.O4.O3.R1>.))P,(=.$8.(23.(13.&40.R41.)+10.)=)P,(1=.(24.O4.)(22.O4.))P,(=.(0.&40.)R41.(25.&40.(26.O4.)))P,(27.O5.R24.)P,(=.$8.(23.(13.&40.R46.)+2.)=)P,(28.O5.O4.R26.)P,(29.O4.O1.+8.)P,(=.(0.&40.)R40.(25.&40.(11.R24.)))P,(=.(0.&40.)R40.(25.&40.(11.R24.)))P,(=.(0.&40.)R40.(25.&40.(11.R24.)))P,(=.(0.&40.)R40.(25.&40.(11.R24.)))P,(=.(0.&40.)R40.(25.&40.=))(2:.O5.R2<.(2;.O5.O4.O3.R4>.R4=.R4<.R4;.R47.R46.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R2?.R2>.R2;.R2:.R29.(30.R2:.R29.R28.R27.R26.)R25.R2=.R2<.)(2<.(2=.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.)R2?.(25.&40.O2.)R2>.(2>.(0.&40.))R2=.(2?.O5.)))")
(* [comment removed for export] *).
