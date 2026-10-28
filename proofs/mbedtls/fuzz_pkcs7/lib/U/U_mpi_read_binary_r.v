(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_addsub U_mpi_read_binary.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_read_binary_r () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_read_binary.mpi_read_binary_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "mpi_read_binary_stmt_r"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_read_binary.mpi_read_binary_stmt"].


Lemma mpdr_at_munch : ltac2:(CDefT.buildp (gd_tbl_P_mpi_read_binary_r ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)Pd,$5.PW,(0.$6.)P,(7.R6.R5.R3.(8.R2.)(9.&40.(:.R2.))(;.R2.)(<.R2.)(=.R2.)(>.R2.)(?.R2.))P,(10.(11.$12.(?.R3.)$13.))P,(14.R3.R7.R6.)P,(15.R9.R8.R7.)P,(16.R5.(8.R6.)+10.)P,P,(11.$12.(?.R7.)$17.)(16.R7.(<.R8.)(18.+4.(;.R8.)))(7.R<.R:.R9.(8.R8.)(9.&40.(:.R8.))(;.R8.)(<.R8.)(=.R8.)(>.R8.)(?.R8.))")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB d W HA HNS MU WM HD1 HD2.
  flat constr:(HA) 6%nat. flclear HA. intros HR HAL HPOS HL HN HO.
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply rw_cells_transport; [exact HR| exact MU| exact WM| exact HD1].
  - destruct (md_own d); [exact HO| | exfalso; exact (HNS eq_refl)].
    flat constr:(HO) 4%nat. flclear HO. intros H1 H2 H3 H4. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    eapply u32arr_transport; [exact H4| exact MU| exact WM|]. rewrite HL. apply HD2. reflexivity.
Qed.


(* [comment removed for export] *)
Definition mpi_read_binary_stmt_r (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_read_binary_r ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(19.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$1:.Ph,(1;.O5.O4.O3.)PLB,(0.$4.)PdX,$5.PB,$1<.Pibs,(0.(2.&8.))Plo,$1<.P,(1=.O5.O4.O3.R6.R5.R8.R7.)P,(7.O5.R9.R6.(8.R5.)(9.&40.(:.R5.))(;.R5.)(<.R5.)(=.R5.)(>.R5.)(?.R5.))P,(10.(11.$12.(?.R6.)$13.))P,(1>.O4.R8.(1?.&40.R2;.)(20.O5.O4.O3.R9.)R7.)P,(21.O5.R<.R7.R6.)P,(22.=R8.)P,(22.(23.R9.(24.(25.(2.&8.)R8.)))(26.+2.+3?.))P,(27.O4.R<.R8.R:.(24.(25.(2.&8.)R9.)))P,(28.(29.(23.R;.(24.(25.(2.&8.)R:.)))(8.R<.))(29.(23.(8.R<.)+10.)R;.))P,P,(11.$12.(?.R=.)$17.)(28.(29.(23.R=.(24.(25.(2.&8.)R<.)))(<.R>.))(29.(23.(<.R>.)(18.+4.(;.R>.)))R=.))P,(28.(29.(23.R=.(24.(25.(2.&8.)R<.)))R;.)(29.(1?.&40.R32.)R=.))P,(2:.O5.R13.R<.(1?.&40.R33.))P,(29.R=.(2;.(2;.(1?.&40.R34.)+50.)(2<.O4.)))P,(29.(2=.O4.)R>.)P,(29.(1?.&40.R36.)(20.O5.O4.O3.R14.))P,(11.$1<.(2>.(1?.&40.R37.)+10.)=)P,(29.(2?.O4.)(2=.O4.))P,(11.(2.&40.)R37.(9.&40.(30.O4.)))P,(31.O5.R1:.)P,(11.$1<.(2>.(1?.&40.R3<.)+2.)=)P,(32.O5.O4.R1<.)P,(33.O4.O1.+8.)P,(11.(2.&40.)R36.(9.&40.(8.R1:.)))P,(11.(2.&40.)R36.(9.&40.R1:.))P,(11.(2.&40.)R36.(9.&40.(24.(25.(2.&8.)R1:.))))(34.O5.R20.(35.O5.O4.O3.R42.R41.R40.R3?.R3;.R3:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R23.R22.R1?.R1>.R1=.(24.(25.(2.&8.)R1;.))R1:.R21.R20.)(36.(37.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R23.(9.&40.O2.)R22.(38.(2.&40.))R21.(39.O5.)))")
(* [comment removed for export] *).

Lemma mpi_read_binary_stmt_of_r : ltac2:(CDefT.buildp (gd_tbl_P_mpi_read_binary_r ()) "Psegs,(0.$1.)PL,$3:.PHI,(3;.R2.R1.)PENTRY,$1<.PMSF,$1<.P,(3<.R5.R4.R3.R2.R1.)(3=.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof. intros segs L HI ENTRY MSF H. unfold mpi_read_binary_stmt. intros. eapply H; try eassumption. exact (proj1 H1). Qed.

