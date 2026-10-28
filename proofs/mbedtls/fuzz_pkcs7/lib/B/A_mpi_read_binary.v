(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_read_binary P_mpi_core_read_be P_mpi_resize_clear.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA
     A_mpi_core_read_be A_mpi_zeroize_and_free A_mpi_resize_clear.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_read_binary () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.MPI_RB_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpi_read_binary_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"].


(* [comment removed for export] *)
Definition mpi_read_binary_stmtA_r (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_read_binary ()) "Ph,(0.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PB,$8.Pibs,(1.(3.&8.))Plo,$8.Pd,$8.P,(9.O4.O3.O2.R2;.R2:.R29.R7.)P,(:.O4.O3.O2.R2<.R7.)P,(;.O4.R9.R2<.R7.)P,(<.(=.$>.(?.R8.)$10.))P,(11.O3.R2>.R2=.(12.&40.R2;.)(13.O4.O3.O2.R2?.)R9.)P,(14.O4.R<.R9.R8.)P,(15.=R:.)P,(15.(16.R;.(17.(18.(3.&8.)R:.)))(19.+2.+3?.))P,(1:.(1;.O3.)(1<.$2.R32.(1=.R31.))R:.R<.(17.(18.(3.&8.)R;.)))P,(1>.(1?.(16.R=.(17.(18.(3.&8.)R<.)))(20.R>.))(1?.(16.(20.R>.)+10.)R=.))P,P,(=.$>.(?.R?.)$21.)(1>.(1?.(16.R?.(17.(18.(3.&8.)R>.)))(22.R10.))(1?.(16.(22.R10.)(23.+4.(24.R10.)))R?.))P,(1>.(1?.(16.R?.(17.(18.(3.&8.)R>.)))R=.)(1?.(12.&40.R32.)R?.))P,(1>.(=.$8.(17.(18.(3.&8.)R?.))=)(1?.(16.(16.R10.(17.(18.(3.&8.)R?.)))+8.)(19.+2.+2?.)))P,(25.O4.R14.R?.(12.&40.R34.))P,(1?.(26.O3.)R10.)P,(1?.R11.(27.(27.(12.&40.R36.)+<0.)(28.O3.)))P,(1?.(12.&40.R37.)(13.O4.O3.O2.R3;.))P,(=.$8.(29.(12.&40.R38.)+10.)=)P,(=.(3.&40.)R37.(2:.&40.(2;.O3.)))P,(2<.O4.R1:.)P,(=.$8.(29.(12.&40.R3<.)+2.)=)P,(2=.O4.(2>.O3.)(2?.O4.O3.O2.R40.)R1<.(20.R1:.)+10.)P,(2=.O4.(2>.O3.)(2?.O4.O3.O2.R41.)R1=.R1:.(17.(18.(3.&8.)R19.)))P,(1?.(16.(30.O4.O3.O2.R42.)(31.(17.(18.(3.&8.)R1:.))))$32.)P,(33.O3.(20.R1=.)+10.R19.)P,(1?.(16.(34.O4.O3.O2.R44.)(35.R1:.))$36.)P,(=.(3.&40.)R39.(2:.&40.(20.R1?.)))P,(=.(3.&40.)R39.(2:.&40.R1?.))P,(=.(3.&40.)R39.(2:.&40.(17.(18.(3.&8.)R1?.))))(37.O4.(38.O4.O3.O2.R48.R47.R46.R45.R44.R43.R42.R3>.R3=.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R26.R25.R22.(17.(18.(3.&8.)R20.))R1?.R1>.R24.R23.)(39.(3:.(3;.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R26.(2:.&40.O1.)R25.(3<.(3.&40.))R24.(3=.O4.))R23.))")
(* [comment removed for export] *).

Lemma mpdr_at_rebuild : ltac2:(CDefT.buildp (gd_tbl_A_mpi_read_binary ()) "Psegs,(1.$3>.)Pm',P,(3.&40.)(5.(3.&8.))PLB,(1.(3?.$8.$8.))PX,$8.Psg,$8.Pn,$8.PP,$8.Plimbs,(1.(3.&40.))Ppad,(3.&40.)Pown,$>.P,(<.(=.$>.R1.$10.))P,(40.R;.R:.R8.(41.R5.(2:.&40.R7.)R6.R3.))P,(=.$8.(29.R9.+8.)=)P,(15.=R:.)P,(=.$8.(17.(18.(3.&40.)R7.))R9.)P,(42.(1?.=R:.)(1?.R:.$43.))P,P,(=.$>.R7.$44.)(42.(=.$8.R;.=)(=.$8.R<.=))P,P,(=.$>.R8.$21.)(42.(1?.+1.R=.)(42.(45.(3?.$8.$8.)(46.$8.$8.R<.(23.+4.R=.))R10.)(42.(=.$8.(29.R<.+10.)=)(47.R12.R11.R<.R;.))))(;.R12.R11.R10.(48.R?.R>.R=.R<.R;.R:.R9.))")
(* [comment removed for export] *).
Proof.
  intros segs m' LB X sg n P limbs pad own HNS HX AL X0 LL NR HN HHp. unfold mpdr_at.
  cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact HX|]. split; [exact AL|]. split; [exact X0|].
  split; [exact LL|]. split; [exact NR|]. destruct own; [exact (HN eq_refl)| exact (HHp eq_refl)| exfalso; exact (HNS eq_refl)].
Qed.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis RC : mpi_resize_clear_coreA_r asegs R HIA A_MPI_RESIZE_CLEAR.   (* [comment removed for export] *)
  Hypothesis RBE : mpi_core_read_be_stmtA asegs R HIA A_MPI_CORE_READ_BE.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  
  End Walk.



(* [comment removed for export] *)
