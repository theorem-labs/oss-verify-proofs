(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts MpiOpnd. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_copy U_mpi_shift_l U_mpi_cmp U_mpi_lset U_mpi_mul_int_W U_mpi_core_bitlen U_mpi_core_shift_r U_mpi_shift_r U_mpi_cmp_abs U_mpi_divmod_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_div_mpi () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.add_sub_mpi_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.mul_int_R"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_divmod_stmt.div_mpi_rem_R"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_shift_l.shift_l_n"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.bool"; "DivP.Walk.ALIAS"; "Corelib.Init.Datatypes.true"; "DivP.Walk.es"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.USpec.MpiClient.cstate"; "Corelib.Init.Datatypes.nil"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.MOK"; "DivP.Walk.locals_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Stdlib.ZArith.BinInt.Z.of_nat"; "DivP.Walk.frame"; "DivP.Walk.t2cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "DivP.Walk.loop_loc"; "DivP.Walk.set_limbs"; "DivP.Walk.lframe"; "DivP.Walk.KONT"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Stdlib.ZArith.BinInt.Z.to_nat"; "DivP.Walk.ISTATE"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.sxz"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_copy.copy_R"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_copy.copy_trim"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_cmp.SIGF"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"].


Definition U_MPI_DIV_MPI : Z := 0x20df4.
Definition U_ADD_SUB_MPI : Z := 0x20a04.
Definition U_MPI_GROW : Z := 0x1f1bc.
Definition U_MPI_SHIFT_L : Z := 0x20018.
Definition U_MPI_LSET : Z := 0x1f808.
Definition U_MPI_MUL_INT : Z := 0x1fbc0.

(* [comment removed for export] *)
Definition add_sub_mpi_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pflip,$0.P,(1.(2.$0.R1.+1.)(2.$0.R1.-1.))Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.Ph,(7.O5.O4.O3.)PLB,(8.$9.)PdX,$:.PdA,$:.PdB,$:.Plo,$0.P,(;.O5.O4.O3.R6.R5.R8.R7.)P,(<.O5.R9.R6.R5.)P,(<.O5.R:.R7.R5.)P,(<.O5.R;.R8.R5.)P,(=.R8.R7.)P,(=.R9.R7.)P,(=.R9.R8.)P,(>.(2.$?.(10.R;.)$11.))P,(12.R<.R;.R9.(13.&40.R2?.))P,(12.R=.R;.R:.(13.&40.R30.))P,(14.O4.R?.R;.(15.R=.)+10.)P,P,(2.$?.(10.R>.)$16.)(14.O4.R11.R=.(17.R?.)(18.+4.(19.R?.)))P,(14.O4.R11.R=.(15.R>.)+10.)P,P,(2.$?.(10.R?.)$16.)(14.O4.R13.R?.(17.R10.)(18.+4.(19.R10.)))P,(1:.O4.R13.(13.&40.R35.)(1;.O5.O4.O3.R14.)R12.)P,P,(>.(2.$?.(10.R13.)$1<.))(1.(1=.(1>.(17.R14.)(18.+4.(19.R14.)))R11.)(1=.(13.&40.R37.)(17.R14.)))P,(1?.O5.R18.R11.(13.&40.R37.))P,(1=.R12.(20.(20.(13.&40.R38.)+>0.)(21.O4.)))P,(1=.(22.O4.)R13.)P,(1=.(13.&40.R3:.)(1;.O5.O4.O3.R19.))P,(2.$0.(23.(13.&40.R3;.)+10.)=)P,(1=.(24.O4.)(22.O4.))P,(2.(3.&40.)R3;.(25.&40.(26.O4.)))P,(27.O5.R1?.)P,(28.O5.O4.R20.)P,(29.O4.O1.+8.)P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))(2:.O5.R24.(2;.O5.O4.O3.R45.R44.R43.R42.R3>.R3=.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.(2<.R47.R22.R21.R20.R1?.)R1>.R25.R24.)(2=.(2>.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.(25.&40.R47.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(25.&40.O2.)R26.(2?.(3.&40.))R25.(30.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_mul_int_stmt_g (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.Ph,(7.O5.O4.O3.)PLB,(8.$9.)PdX,$:.PdA,$:.Pb,$0.Plo,$0.P,(;.O5.O4.O3.R6.R5.R8.R7.)P,(<.O5.R9.R6.R5.)P,(<.O5.R:.R7.R5.)P,(=.R7.R6.)P,(>.(2.$?.(10.R8.)$11.))P,(12.R9.R8.R6.(13.&40.R2=.))P,(14.O4.R;.R7.(15.R9.)+10.)P,P,(2.$?.(10.R:.)$16.)(14.O4.R=.R9.(17.R;.)(18.+4.(19.R;.)))P,(1:.O4.R=.(13.&40.R30.)(1;.O5.O4.O3.R>.)R<.)P,P,(>.(2.$?.(10.R=.)$1<.))(1.(1=.(1>.(17.R>.)(18.+4.(19.R>.)))R;.)(1=.(13.&40.R32.)(17.R>.)))P,(1?.O5.R12.R;.(13.&40.R32.))P,(1=.R<.(20.(20.(13.&40.R33.)+:0.)(21.O4.)))P,(1=.(22.O4.)R=.)P,(1=.(13.&40.R35.)(1;.O5.O4.O3.R13.))P,(2.$0.(23.(13.&40.R36.)+10.)=)P,(1=.(24.O4.)(22.O4.))P,(2.(3.&40.)R36.(25.&40.(26.O4.)))P,(27.O5.R19.)P,(28.O5.O4.R1:.)P,(29.O4.O1.+8.)P,(31.(1=.=R16.)(32.R16.(33.+2.+20.)))P,(2.$0.(23.(13.&40.R33.)(33.+2.+20.))R17.)P,(34.(2.$0.(13.&40.R34.)=)(2.$0.R18.=))P,(2.(3.&40.)R37.(25.&40.(15.R1;.)))P,(2.(3.&40.)R37.(25.&40.(15.R1;.)))(2:.O5.R20.(2;.O5.O4.O3.R42.R41.R40.R3?.R3;.R3:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R23.R22.R1?.R1>.R1=.(35.R1;.R1>.R1=.R1<.)R1:.R21.R20.)(2=.(2>.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R23.(25.&40.O2.)R22.(2?.(3.&40.))R21.(30.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_div_mpi_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.Ph,(7.O5.O4.O3.)PLB,(8.$9.)PdX,$:.PdA,$:.PdB,$:.Plo,$0.P,(;.O5.O4.O3.R6.R5.R8.R7.)P,(<.O5.R9.R6.R5.)P,(<.O5.R:.R7.R5.)P,(<.O5.R;.R8.R5.)P,(=.R8.R7.)P,(=.R9.R7.)P,(=.R9.R8.)P,(>.(2.$?.(10.R;.)$11.))P,(>.(2.$0.(15.R<.)(15.R:.)))P,(12.R=.R<.R:.(13.&40.R30.))P,(12.R>.R<.R;.(13.&40.R31.))P,(14.O4.R10.R<.(15.R>.)+10.)P,P,(2.$?.(10.R?.)$16.)(14.O4.R12.R>.(17.R10.)(18.+4.(19.R10.)))P,(14.O4.R12.R>.(15.R?.)+10.)P,P,(2.$?.(10.R10.)$16.)(14.O4.R14.R10.(17.R11.)(18.+4.(19.R11.)))P,(1:.O4.R14.(13.&40.R36.)(1;.O5.O4.O3.R15.)R13.)P,P,(>.(2.$?.(10.R14.)$1<.))(1.(1=.(1>.(17.R15.)(18.+4.(19.R15.)))R12.)(1=.(13.&40.R38.)(17.R15.)))P,(1?.O5.R19.R12.(13.&40.R38.))P,(1=.R13.(20.(20.(13.&40.R39.)+200.)(21.O4.)))P,(1=.(22.O4.)R14.)P,(1=.(13.&40.R3;.)(1;.O5.O4.O3.R1:.))P,(2.$0.(23.(13.&40.R3<.)+10.)=)P,(1=.(24.O4.)(22.O4.))P,(2.(3.&40.)R3<.(25.&40.(26.O4.)))P,(27.O5.R20.)P,(28.O5.O4.R21.)P,(29.O4.O1.+8.)P,(2.(3.&40.)R3:.(25.&40.(15.R1?.)))P,(2.(3.&40.)R3:.(25.&40.(15.R1?.)))P,(2.(3.&40.)R3:.(25.&40.(15.R1?.)))(2:.O5.R25.(2;.O5.O4.O3.R46.R45.R44.R43.R3?.R3>.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R28.R27.R24.R23.R22.(36.R23.R22.R21.R20.)R1?.R26.R25.)(2=.(2>.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.(25.&40.=)R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)R28.(25.&40.O2.)R27.(2?.(3.&40.))R26.(30.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L32407069278.5L32407185111.5L44021394330.3L46609801519.200000:00D00J00KS1i2Hi1D1eS1i2Hi1M1nS1i2HiS". (* [comment removed for export] *)
Lemma limbs_of_bits_spec : forall i, 0 <= i -> 32 * limbs_of_bits i - 32 < i <= 32 * limbs_of_bits i.
Proof.
  intros i Hi. unfold limbs_of_bits. pose proof (Z.div_mod i 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound i 32 ltac:(lia)) as M.
  destruct (Z.eqb_spec (i mod 32) 0); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L27394378476.500000:S1i1m2Hm1H". (* [comment removed for export] *)
Lemma limbs_of_bits_le : forall i m, 0 <= i -> i <= 32 * m -> limbs_of_bits i <= m.
Proof. intros i m Hi Hm. pose proof (limbs_of_bits_spec i Hi). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L8294964459.500000:S1i1m2Hm1H". (* [comment removed for export] *)
Lemma limbs_of_bits_ge : forall i m, 0 <= i -> 32 * m < i -> m + 1 <= limbs_of_bits i.
Proof. intros i m Hi Hm. pose proof (limbs_of_bits_spec i Hi). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L10357883337.3L43191327048.5L45272746084.400000700D00KS1i1j1HS1i1j1H2H02H1S1i1j1H". (* [comment removed for export] *)
Lemma limbs_of_bits_mono : forall i j, 0 <= i <= j -> limbs_of_bits i <= limbs_of_bits j.
Proof. intros i j H. pose proof (limbs_of_bits_spec i ltac:(lia)). pose proof (limbs_of_bits_spec j ltac:(lia)). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L19732499450.13L59568340337.13L59574694765.14L61713947134.15L61713947134.8 L9544766530.15 00000K00c01201A01I01US2xs1n2ys2n'2LE2B12B22C12C3S2xs1n2ys2n'2LE2B12B22Z0S2xs1n2ys2n'2LTS2xs1n2ys2n'2C1S2xs1n1HS2xs1n2ys2n'". (* [comment removed for export] *)
Lemma core_bitlen_mono_val : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pxs,(8.(3.&40.))Pn,$0.Pys,(8.(3.&40.))Pn',$0.P,(1=.=R3.)P,(1=.=R2.)P,(1=.(37.R4.R3.)(37.R6.R5.))(1=.(38.R5.R4.)(38.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros xs n ys n' Hn Hn' LE.
  destruct (core_bitlen_val ys n' Hn') as [[-> _]|(B1 & B2 & B3)]; [pose proof (core_bitlen_range xs n Hn); lia|].
  destruct (core_bitlen_val xs n Hn) as [[E Z0]|(C1 & C2 & C3)]; [pose proof (Z.pow_pos_nonneg 2 (core_bitlen ys n' - 1)); lia|].
  assert (LT : 2 ^ (core_bitlen ys n' - 1) < 2 ^ core_bitlen xs n) by lia.
  apply Z.pow_lt_mono_r_iff in LT; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L26213218539.6L36238129595.6L54650863185.600000900C00FS1s1d1R1HS1s1d2Hs1RS1d". (* [comment removed for export] *)
Lemma shift_l_n_le_succ : forall s d, 0 <= s <= 31 -> 0 <= md_n d -> shift_l_n s d <= md_n d + 1.
Proof.
  intros s d Hs Hn. unfold shift_l_n. pose proof (core_bitlen_range (md_limbs d) (md_n d) Hn) as R.
  destruct (Z.ltb_spec (md_n d * 32) (core_bitlen (md_limbs d) (md_n d) + s)); [| lia].
  apply limbs_of_bits_le; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L26213218539.6L44339584084.6L48145496896.7L8623374620.6 00000900<00D00KS1s1d1R1HS1dS1s1d2H0S1s1d1H". (* [comment removed for export] *)
Lemma shift_l_n_ge : forall s d, 0 <= s -> 0 <= md_n d -> md_n d <= shift_l_n s d.
Proof.
  intros s d Hs Hn. unfold shift_l_n. pose proof (core_bitlen_range (md_limbs d) (md_n d) Hn) as R.
  destruct (Z.ltb_spec (md_n d * 32) (core_bitlen (md_limbs d) (md_n d) + s)); [| lia].
  pose proof (limbs_of_bits_ge (core_bitlen (md_limbs d) (md_n d) + s) (md_n d) ltac:(lia) ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L26206913747.10L31528019175.7 L4300307136.10 L49456610872.10L50571772338.6 L5495603669.10 L63501662847.10L64789019588.1100000G00Q00Z00i01301=01R01aS1s2dY2RY1H2dX2BL2RX2H0S2dX2dY2HNS1s2dX2H0S1s2dX2dY2BL2H0S2dX2dY2HNS2dX2dY2HNS1s2dX2dY2BL2RX2RY2H0S1s2dX2dY2HN2H1". (* [comment removed for export] *)
Lemma shift_l_n_mono : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Ps,$0.PdX,$:.PdY,$:.P,(1=.=R3.)P,(31.(1=.=(19.R2.))(1=.(19.R2.)(19.R3.)))P,(1=.(38.(39.R3.)(19.R3.))(38.(39.R4.)(19.R4.)))(1=.(3:.R6.R4.)(3:.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros s dX dY Hs HN BL. unfold shift_l_n.
  pose proof (core_bitlen_range (md_limbs dX) (md_n dX) ltac:(lia)) as RX. pose proof (core_bitlen_range (md_limbs dY) (md_n dY) ltac:(lia)) as RY.
  destruct (Z.ltb_spec (md_n dY * 32) (core_bitlen (md_limbs dY) (md_n dY) + s)); [| ].
  - destruct (Z.ltb_spec (md_n dX * 32) (core_bitlen (md_limbs dX) (md_n dX) + s)).
    + apply limbs_of_bits_mono. lia.
    + apply limbs_of_bits_le; lia.
  - destruct (Z.ltb_spec (md_n dX * 32) (core_bitlen (md_limbs dX) (md_n dX) + s)); [| lia].
    pose proof (limbs_of_bits_ge (core_bitlen (md_limbs dX) (md_n dX) + s) (md_n dX) ltac:(lia) ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L15470930615.2L22502704494.2L29317571254.1L29317571254.2L50607698618.2L56087813952.3L56093676630.2L57099268171.300000100400500600<00D00J00PSS1xSSS1x2HxS1x2Hx1nS1x2HxS1x2Hx". (* [comment removed for export] *)
Lemma lxor_ones5 : forall x, 0 <= x < 32 -> Z.lxor x 31 = 31 - x.
Proof.
  intros x Hx. change 31 with (Z.ones 5).
  rewrite <- Z.ldiff_ones_l_low; [| lia | ].
  2:{ destruct (Z.eq_dec x 0) as [->|]. cbn; lia. apply Z.log2_lt_pow2; lia. }
  rewrite Z.ldiff_land, Z.land_comm, Z.land_ones by lia. unfold Z.lnot.
  rewrite <- (Z.mod_add _ 1) by lia. change (Z.ones 5) with (2^5 - 1). rewrite Z.mod_small; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29317571254.2000001S". (* [comment removed for export] *)
Lemma land_31 : forall x, 0 <= x -> Z.land x 31 = x mod 32.
Proof. intros x Hx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma zx16_m1 : zx16 (Z_to_bv 64 (-1)) = Z_to_bv 64 65535.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rw_cells_C2_mod16 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Psegs,(8.$3;.)Pm,P,(3.&40.)(5.(3.&8.))PA,$0.Ppre,(8.$3<.)Pz,$0.Ppost,(8.$3<.)P,(3=.R6.R5.R4.(3>.$3<.R3.(3?.$3<.(40.(25.&40.R2.))R1.)))(3=.R7.R6.R5.(3>.$3<.R4.(3?.$3<.(40.(25.&40.(23.R3.(33.+2.+10.))))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre z post H. eapply rw_cells_reshape; [exact H| |].
  - flat constr:(H) 2%nat. flclear H. intros (Hwf & _) _. apply cells_wf_app in Hwf. flat constr:(Hwf) 2%nat. flclear Hwf. intros H1 (_ & H3). apply cells_wf_app. split; [exact H1|]. cbn. auto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !le2_of_Z. rewrite <- (Z_to_le_bytes_mod 2 z). change (8 * Z.of_nat 2) with 16. reflexivity.
Qed.

Section DivP.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr usegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variable MSF : Z.
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.
  (* [comment removed for export] *)
  Hypothesis HCOPY : mpi_copy_stmt_x usegs L HI U_MPI_COPY MSF.
  Hypothesis HGROW : mpi_grow_stmt usegs L HI U_MPI_GROW MSF.
  Hypothesis HSHL : mpi_shift_l_stmt usegs L HI U_MPI_SHIFT_L MSF.
  Hypothesis HCMP : mpi_cmp_mpi_stmt usegs U_MPI_CMP_MPI.
  Hypothesis HAS : add_sub_mpi_stmt usegs L HI U_ADD_SUB_MPI MSF.
  Hypothesis HLSET : mpi_lset_stmt usegs L HI U_MPI_LSET MSF.
  Hypothesis HMULI : mpi_mul_int_stmt_g usegs L HI U_MPI_MUL_INT MSF.
  Hypothesis HCBL : mpi_core_bitlen_stmt usegs U_MPI_CORE_BITLEN.
  Hypothesis HCMPO : mpi_cmp_mpi_stmt_o usegs U_MPI_CMP_MPI.
  Hypothesis HSHR : mpi_shift_r_stmt usegs U_MPI_SHIFT_R.
  Hypothesis HCABS : mpi_cmp_abs_stmt usegs U_MPI_CMP_ABS.
  Hypothesis HZF : zeroize_and_free_stmt usegs L HI U_ZEROIZE_AND_FREE MSF.
  Hypothesis HPZ : platform_zeroize_stmt usegs L U_PLATFORM_ZEROIZE MSF.

  (* [comment removed for export] *)
  Ltac take S n S0 :=
    lazymatch type of S with rw_cells ?sg ?m ?a ?cs =>
      let c1 := eval cbn [firstn] in (firstn n cs) in
      let c2 := eval cbn [skipn] in (skipn n cs) in
      let S1 := fresh "S" in
      pose proof (proj1 (rw_cells_app sg m a c1 c2) S) as [S0 S1]; clear S; rename S1 into S;
      cbn [cells_size csize Nat.add] in S;
      repeat match type of S with context [Z.of_nat ?k] => let z := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with z in S end;
      lazymatch type of S with
      | rw_cells _ _ (?base + ?x + ?y) _ => let v := eval vm_compute in (x + y)%Z in replace (base + x + y) with (base + v) in S by lia
      | _ => idtac
      end
    end.

  Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dR dA dB : mpd) (lo : Z).
  Hypothesis HH0 : HEAP usegs L HI h LB m mo.
  Hypothesis MR0 : mpd_at usegs m LB dR.
  Hypothesis MA0 : mpd_at usegs m LB dA.
  Hypothesis MB0 : mpd_at usegs m LB dB.
  Hypothesis SRA : mpd_sep dR dA.
  Hypothesis SRB : mpd_sep dR dB.
  Hypothesis SAB : mpd_sep dA dB.
  Hypothesis NSR : md_own dR <> LStatic.
  Hypothesis NEB : md_addr dR <> md_addr dB.
  Hypothesis OPA : opnd_sep dR dA lo (bv_unsigned sp).
  Hypothesis OPB : opnd_sep dR dB lo (bv_unsigned sp).
  Hypothesis CRA : client_range L LB lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L LB lo (md_p dA) (4 * md_n dA).
  Hypothesis CRB : client_range L LB lo (md_addr dB) 16.
  Hypothesis CRBL : md_own dB = LHeap -> client_range L LB lo (md_p dB) (4 * md_n dB).
  Hypothesis WRR : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dR.
  Hypothesis RLO : md_own dR <> LNull -> md_p dR + 4 * md_n dR <= lo \/ bv_unsigned sp <= md_p dR.
  Hypothesis ST0 : stk usegs m lo (bv_unsigned sp).
  Hypothesis SLO : lo <= bv_unsigned sp - 512 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv usegs m.
  Hypothesis SOK0 : statics_ok usegs L m.
  Hypothesis CA : const_at L MSF 8.

  Notation SP := (bv_unsigned sp).
  Notation SPc := (bv_unsigned sp + -288).
  Notation POST := (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo).

  (* [comment removed for export] *)
  Definition ALIAS : bool := Z.eqb (md_addr dR) (md_addr dA).
  Definition es : list mpd := if ALIAS then [dB] else [dA; dB].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L43782101083.89L54965713378.2 L59314955108.91L65499856427.89L774698616.89  00000;00B00Z00a01>S2sp2dR3SPBS1L3ACPS2sp2dR2dA4HPOS3SPB2AL1ES2sp2dRS1L3HLS2sp2dR2lo3SLO4HPOS3SPB". (* [comment removed for export] *)
  Lemma facts0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "(31.(32.=(15.VdR,))(31.(2.$0.(23.(15.VdR,)+8.)=)(31.(1.(1=.(1>.(15.VdR,)+10.)Vlo,)(1=.(13.&40.Vsp,)(15.VdR,)))(31.P,(2.$?.(10.VdR,)$16.)(31.(41.(42.$0.$0.)(43.$0.$0.(17.VdR,)(18.+4.(19.VdR,)))VLB,)(1=.+1.(19.VdR,)))(31.(44.(42.$0.$0.)Lb,(42.$0.$0.)(45.VL,(46.$0.$0.R1.)(47.$0.$0.R1.))VLB,)(31.(32.=(22.VL,))(31.(32.(13.&40.Vsp,)(33.+2.+40.))P,(2.$48.$49.$4:.)(2.$:.VdA,VdR,))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(MR0) 2%nat. intros FLt1 SG. flat constr:(FLt1) 6%nat. flclear FLt1. intros HR HAL HPOS HL HN HO.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros BR _. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(WRR) 3%nat. flclear WRR. intros WW1 WW2 WW3.
    split; [exact HPOS|]. split; [exact HAL|].
    split; [exact (client_wrange_where L _ _ _ _ 16 lo WW1 ltac:(lia) BR DHI ACL ltac:(lia))|].
    split. { intros O. rewrite O in HO. flat constr:(HO) 3%nat. flclear HO. intros N1 IN _. auto. }
    split; [exact BR|]. split; [clear -ACP; lia|]. split; [lia|].
    intros AL. unfold ALIAS in AL. apply Z.eqb_eq in AL. destruct SRA as [E|E]; [symmetry; exact E| exfalso; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma ESF_ok : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "(44.$:.Le,$:.(31.(14.VL,VLB,Vlo,(15.R1.)+10.)(31.P,(2.$?.(10.R1.)$16.)(41.(42.$0.$0.)(43.$0.$0.(17.R2.)(18.+4.(19.R2.)))VLB,)(31.(1.(1=.(1>.(15.R1.)+10.)Vlo,)(1=.(13.&40.Vsp,)(15.R1.)))(31.P,(2.$?.(10.VdR,)$16.)(1.(1=.(1>.(15.R2.)+10.)(17.VdR,))(1=.(1>.(17.VdR,)(18.+4.(19.VdR,)))(15.R2.)))(31.(1.(>.(2.$?.(10.VdR,)$16.))(1.(2.$?.(10.R1.)$1<.)(1.(1=.(1>.(17.VdR,)(18.+4.(19.VdR,)))(17.R1.))(1=.(1>.(17.R1.)(18.+4.(19.R1.)))(17.VdR,)))))(31.(1.(1=.(1>.(15.VdR,)+10.)(15.R1.))(1=.(1>.(15.R1.)+10.)(15.VdR,)))P,(>.(2.$?.(10.R1.)$1<.))(1.(1=.(1>.(15.VdR,)+10.)(17.R2.))(1=.(1>.(17.R2.)(18.+4.(19.R2.)))(15.VdR,)))))))))$4;.)")
(* [comment removed for export] *).
  Proof.
    assert (FB : client_range L LB lo (md_addr dB) 16 /\ (md_own dB = LHeap -> In (md_p dB, 4 * md_n dB) LB)
                 /\ (md_addr dB + 16 <= lo \/ SP <= md_addr dB)
                 /\ (md_own dR = LHeap -> md_addr dB + 16 <= md_p dR \/ md_p dR + 4 * md_n dR <= md_addr dB)
                 /\ (md_own dR <> LHeap \/ md_own dB = LNull \/ md_p dR + 4 * md_n dR <= md_p dB \/ md_p dB + 4 * md_n dB <= md_p dR)
                 /\ (md_addr dR + 16 <= md_addr dB \/ md_addr dB + 16 <= md_addr dR)
                 /\ (md_own dB <> LNull -> md_addr dR + 16 <= md_p dB \/ md_p dB + 4 * md_n dB <= md_addr dR)).
    { flat constr:(OPB) 5%nat. flclear OPB. intros O1 O2 O3 O4 O5. flat constr:(MB0) 2%nat. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ _ HOB.
      split; [exact CRB|]. split; [intros O; rewrite O in HOB; exact (proj1 (proj2 HOB))|]. split; [exact O4|]. split; [exact O2|].
      split. { destruct O3 as [E|X]; [exfalso; apply NEB; rewrite E; reflexivity| exact X]. }
      split. { destruct SRB as [E|X]; [exfalso; apply NEB; rewrite E; reflexivity| exact X]. }
      exact O1. }
    unfold es, ALIAS. destruct (Z.eqb_spec (md_addr dR) (md_addr dA)) as [AL|NAL]; [constructor; [exact FB| constructor]|].
    constructor; [| constructor; [exact FB| constructor]].
    flat constr:(OPA) 5%nat. flclear OPA. intros O1 O2 O3 O4 O5. flat constr:(MA0) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros _ _ _ _ _ HOA.
    split; [exact CRA|]. split; [intros O; rewrite O in HOA; exact (proj1 (proj2 HOA))|]. split; [exact O4|]. split; [exact O2|].
    split. { destruct O3 as [E|X]; [exfalso; apply NAL; rewrite E; reflexivity| exact X]. }
    split. { destruct SRA as [E|X]; [exfalso; apply NAL; rewrite E; reflexivity| exact X]. }
    exact O1.
  Qed.

  Lemma opndA : In dA es \/ dA = dR.
  Proof.
    unfold es. destruct ALIAS eqn:AL; [right; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0)))))) AL)| left; left; reflexivity].
  Qed.
  Lemma opndB : In dB es.
  Proof. unfold es. destruct ALIAS; [left; reflexivity| right; left; reflexivity]. Qed.

  (* [comment removed for export] *)
  Notation CST := (cstate usegs L HI h LB mo m SP lo SPc dR es).
  Local Ltac mc_inst H :=
    exact (H usegs L HI HLS DIMG HND IMGC SW ROIMG h LB mo m SP lo SPc dR es
             ACL ltac:(lia) ltac:(lia) HTOP (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0)))))) ) DHI NSR WRR
             (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok).
  Definition mc_init := ltac:(mc_inst @cs_init).
  Definition mc_final := ltac:(mc_inst @cs_final).
  Definition mc_binop_l := ltac:(mc_inst @cs_binop_l).
  Definition mc_binop_w := ltac:(mc_inst @cs_binop_w).
  Definition mc_munch := ltac:(mc_inst @cs_munch).
  Definition mc_hi_write := ltac:(mc_inst @cs_hi_write).
  Definition mc_sign_w := ltac:(mc_inst @cs_sign_w).
  Definition mc_calloc_attach := ltac:(mc_inst @cs_calloc_attach).
  Definition mc_release := ltac:(mc_inst @cs_release).
  Definition mc_heap_nop := ltac:(mc_inst @cs_heap_nop).
  Definition mc_local_facts := ltac:(mc_inst @cs_local_facts).
  Definition mc_w_facts := ltac:(mc_inst @cs_w_facts).
  Definition mc_ext_facts := ltac:(mc_inst @cs_ext_facts).
  Definition mc_opnd_sep_ll := ltac:(mc_inst @cs_opnd_sep_ll).
  Definition mc_opnd_sep_le := ltac:(mc_inst @cs_opnd_sep_le).
  Definition mc_opnd_sep_lw := ltac:(mc_inst @cs_opnd_sep_lw).
  Definition mc_opnd_sep_wl := ltac:(mc_inst @cs_opnd_sep_wl).
  Definition mc_opnd_sep_we := ltac:(mc_inst @cs_opnd_sep_we).
  Definition mc_opnd_sep_ww := ltac:(mc_inst @cs_opnd_sep_ww).
  Definition mc_ivs_local := ltac:(mc_inst @cs_ivs_local).
  Definition mc_ivs_w := ltac:(mc_inst @cs_ivs_w).

  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -288)).
  Local Ltac dest_cs H :=
    (flat constr:(H) 21%nat; flclear H; intros HH HTc MF LOK SA LA MW WOK EXOK SUB COV FRS EXT PX SOK MI ST CH CHS CXH CXS).
  (* [comment removed for export] *)
  Notation REGS := ([C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).
  (* [comment removed for export] *)
  Definition locals_at (ls : list mpd) : Prop := map md_addr ls = [SP + -144; SP + -160; SP + -176; SP + -192].

  Lemma struct_cells : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PCS,(8.(42.$0.(8.$3<.)))Pi,$4=.Pd,$:.P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R9.R8.R7.R6.R5.R4.(4?.$9.)R3.(4?.(42.$0.(8.$3<.))))P,(2.(5.$:.)(50.$:.R6.R3.)(51.$:.R2.))(31.(3=.$4<.R;.(15.R3.)(52.(17.R3.)(25.&40.(53.R3.))(19.R3.)(54.R3.)))(31.(1.(2.$0.(53.R3.)+1.)(2.$0.(53.R3.)-1.))(31.(31.(1=.=(19.R3.))(1=.(19.R3.)$55.))(31.P,(2.$?.(10.R3.)$1<.)(31.(2.$0.(17.R4.)=)(2.$0.(19.R4.)=))P,(2.$?.(10.R3.)$16.)(31.(32.=(17.R4.))(1=.+1.(19.R4.)))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW CS i d CS_ Hi. flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS_ Hi)) 8%nat. intros FLt4 _ _ _ _ _ HF _. flat constr:(FLt4) 2%nat. flclear FLt4. intros FLt5 SG. flat constr:(FLt5) 6%nat. flclear FLt5. intros HR HAL HPOS HL HN HO.
    split; [exact HR|]. split; [exact SG|]. split; [exact HN|]. split.
    - intros O. rewrite O in HO. exact HO.
    - intros O. flat constr:((HF O)) 5%nat. intros P0 _ _ N1 _. auto.
  Qed.

  Lemma cs_parts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PCS,(8.(42.$0.(8.$3<.)))P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R7.R6.R5.R4.R3.R2.(4?.$9.)R1.(4?.(42.$0.(8.$3<.))))(31.(;.$4<.VL,VHI,R6.R5.R8.R7.)(31.(2.$0.(1;.$4<.VL,VHI,R6.)(1;.$4<.VL,VHI,Vh,))(31.(56.Vmo,R7.)(31.(28.$4<.VL,R8.)(31.(27.$4<.R8.)(31.(1?.$4<.R8.Vlo,(1>.(13.&40.Vsp,)-120.))(31.(44.(42.$0.(8.$3<.))Lac,(42.$0.(8.$3<.))(3=.$4<.R9.(46.$0.(8.$3<.)R1.)(47.$0.(8.$3<.)R1.))R2.)(57.R7.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW CS CS_. dest_cs CS_. split; [exact HH|]. split; [exact HTc|]. split; [exact MF|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split; [exact CH|]. exact (heap_mok _ _ HI _ _ _ _ HH).
  Qed.

  (* [comment removed for export] *)
  Definition t2cells (j68 : word) : list cell := [C8 (Z_to_bv 64 (SP + -220)); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 3); C4 j68].
  Definition tcells (t0 t1 t2 t3 t4 : word) : list cell := [C4 t0; C4 t1; C8 t2; C4 t3; C4 t4].
  (* [comment removed for export] *)
  Definition frame (cs0 tpc : list cell) (j68 : word) (tcs : list cell) : list (Z * list cell) :=
    [(SP + -288, cs0); (SP + -220, tpc); (SP + -208, t2cells j68); (SP + -128, tcs); (SP + -104, REGS)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L10800830378.88L16435922218.88L21566674473.85L22400390908.90L23735888298.88L25493088151.85L30501055831.85L31515330346.88L32330368554.88L35258791594.88L36769830679.85L39832349482.88L40150063014.90L40893948970.88L41869470441.85L42471414250.88L43292874986.88L48193915050.88L48389638442.88L4851888106.88 L49211099178.88L50404971497.85L5666926314.88 L5956705431.85 L64281987626.88L64949258857.85L65208125669.90L7841565491.90 00000D00X00l01F01Z01n02B02V02j03>03R03f04@04T04h05<05P05d06806L06`07407H07\08008D08^098S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2m13cs03tpc2E23SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2m33cs03tpc2E43SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2m23cs03tpc2E33SZ03SZ1S2sp2m03cs03tpc2E13SZ03SZ1". (* [comment removed for export] *)
  Lemma frame_chs : forall (ls : list mpd) (cs0 tpc : list cell) (j68 : word) (tcs : list cell),
    locals_at ls -> cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> cells_size tcs = 24%nat ->
    Forall (fun ac : Z * list cell => SP + -288 <= fst ac /\ fst ac + Z.of_nat (cells_size (snd ac)) <= SP /\
              (forall d, In d ls -> fst ac + Z.of_nat (cells_size (snd ac)) <= md_addr d \/ md_addr d + 16 <= fst ac))
           (frame cs0 tpc j68 tcs)
(* [comment removed for export] *).
  Proof.
    intros ls cs0 tpc j68 tcs ADDRS SZ0 SZ1 SZ2.
    assert (LOC : forall d, In d ls -> md_addr d = SP + -144 \/ md_addr d = SP + -160 \/ md_addr d = SP + -176 \/ md_addr d = SP + -192).
    { intros d Hd. unfold locals_at in ADDRS. destruct ls as [|? [|? [|? [|? [|]]]]]; try discriminate ADDRS. cbn [map] in ADDRS. injection ADDRS as E1 E2 E3 E4.
      destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; lia. }
    unfold frame, t2cells.
    constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd cells_size csize Nat.add]; rewrite ?SZ0, ?SZ1, ?SZ2;
      (split; [lia| split; [lia| intros d Hd; destruct (LOC d Hd) as [E|[E|[E|E]]]; rewrite E; lia]]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma cs_frame : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (ls : list mpd) (dW : mpd)
      (cs0 tpc : list cell) (j68 : word) (tcs : list cell),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq ls dW [] (frame cs0 tpc j68 tcs) [] ->
    rw_cells usegs mq (SP + -288) cs0 /\ rw_cells usegs mq (SP + -220) tpc /\ rw_cells usegs mq (SP + -208) (t2cells j68) /\
    rw_cells usegs mq (SP + -128) tcs /\ rw_cells usegs mq (SP + -104) REGS
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW cs0 tpc j68 tcs CS_. flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros _ _ _ _ _ _ CH _.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CHT.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CHT, CHR. auto.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L14875175892.110L26179885524.110L29208397524.110L40150326919.111L46443921620.110L47457479516.106L49655371559.106L63139635821.106L65207861700.111L68135966630.111L7841301010.111 00000Q01201S01o02P03103N03k04G04c05?S2sp3flo3fhi4cs0'4tpc'2F23SZ03SZ1S2sp3flo3fhi4cs0'4tpc'2F23SZ03SZ1S2sp3flo3fhi4cs0'4tpc'2F23SZ03SZ1S2sp2m34cs0'4tpc'2Ec3SZ03SZ1S2sp3flo3fhi4cs0'4tpc'2F23SZ03SZ1S2sp3flo3fhi4cs0'4tpc'2F23SZ03SZ1S2sp3fhi4cs0'4tpc'2F23SZ03SZ1S2sp3flo4cs0'4tpc'2F13SZ03SZ1S2sp2m24cs0'4tpc'2Eb3SZ03SZ1S2sp2m44cs0'4tpc'2Ed3SZ03SZ1S2sp2m04cs0'4tpc'2Ea3SZ03SZ1". (* [comment removed for export] *)
  Lemma cs_frame_upd : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (ls : list mpd) (dW : mpd)
      (cs0 tpc : list cell) (j68 : word) (tcs : list cell) (flo fhi : Z) (m1 : mem) (cs0' tpc' : list cell),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq ls dW [] (frame cs0 tpc j68 tcs) [] ->
    locals_at ls -> munch [(flo, fhi)] mq m1 -> wmono usegs mq m1 -> mem_inv usegs m1 -> stk usegs m1 lo SPc ->
    SP + -288 <= flo -> fhi <= SP + -208 ->
    rw_cells usegs m1 (SP + -288) cs0' -> cells_size cs0' = 68%nat -> rw_cells usegs m1 (SP + -220) tpc' -> cells_size tpc' = 12%nat ->
    cells_size tcs = 24%nat ->
    cstate usegs L HI h LB mo m SP lo SPc dR es m1 moq hq LBq ls dW [] (frame cs0' tpc' j68 tcs) []
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW cs0 tpc j68 tcs flo fhi m1 cs0' tpc' CS_ ADDRS MU WM MI1 ST1 F1 F2 C0 SZ0 C1 SZ1 SZ2.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros _ _ CH2 CHT CHR.
    assert (LOC : forall d, In d ls -> md_addr d = SP + -144 \/ md_addr d = SP + -160 \/ md_addr d = SP + -176 \/ md_addr d = SP + -192).
    { intros d Hd. unfold locals_at in ADDRS. destruct ls as [|? [|? [|? [|? [|]]]]]; try discriminate ADDRS. cbn [map] in ADDRS. injection ADDRS as Ea Eb Ec Ed.
      destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; lia. }
    eapply (mc_hi_write _ _ _ _ _ _ _ _ _ flo fhi []); [exact CS_| exact MU| exact WM| exact MI1| exact ST1| lia| lia| constructor| reflexivity| | |].
    - intros j d d' Hj Hj'. rewrite Hj in Hj'. injection Hj' as <-. left. split; [| reflexivity]. destruct (LOC d (nth_error_In _ _ Hj)) as [E|[E|[E|E]]]; rewrite E; lia.
    - unfold frame. constructor; [exact C0| constructor; [exact C1| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd].
      + eapply rw_cells_transport; [exact CH2| exact MU| exact WM| unfold t2cells; cbn; lia].
      + eapply rw_cells_transport; [exact CHT| exact MU| exact WM| rewrite SZ2; cbn; lia].
      + eapply rw_cells_transport; [exact CHR| exact MU| exact WM| cbn; lia].
    - apply frame_chs; [exact ADDRS| exact SZ0| exact SZ1| exact SZ2].
  Qed.

  Lemma cs_frame_updT : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (ls : list mpd) (dW : mpd)
      (cs0 tpc : list cell) (j68 : word) (tcs : list cell) (flo fhi : Z) (m1 : mem) (tcs' : list cell),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq ls dW [] (frame cs0 tpc j68 tcs) [] ->
    locals_at ls -> munch [(flo, fhi)] mq m1 -> wmono usegs mq m1 -> mem_inv usegs m1 -> stk usegs m1 lo SPc ->
    SP + -128 <= flo -> fhi <= SP + -104 ->
    rw_cells usegs m1 (SP + -128) tcs' -> cells_size tcs' = 24%nat ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat ->
    cstate usegs L HI h LB mo m SP lo SPc dR es m1 moq hq LBq ls dW [] (frame cs0 tpc j68 tcs') [].
  Proof.
    intros mq moq hq LBq ls dW cs0 tpc j68 tcs flo fhi m1 tcs' CS_ ADDRS MU WM MI1 ST1 F1 F2 CT SZ2 SZ0 SZ1.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CH0 CH1 CH2 _ CHR.
    assert (LOC : forall d, In d ls -> md_addr d = SP + -144 \/ md_addr d = SP + -160 \/ md_addr d = SP + -176 \/ md_addr d = SP + -192).
    { intros d Hd. unfold locals_at in ADDRS. destruct ls as [|? [|? [|? [|? [|]]]]]; try discriminate ADDRS. cbn [map] in ADDRS. injection ADDRS as Ea Eb Ec Ed.
      destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; lia. }
    eapply (mc_hi_write _ _ _ _ _ _ _ _ _ flo fhi []); [exact CS_| exact MU| exact WM| exact MI1| exact ST1| lia| lia| constructor| reflexivity| | |].
    - intros j d d' Hj Hj'. rewrite Hj in Hj'. injection Hj' as <-. left. split; [| reflexivity]. destruct (LOC d (nth_error_In _ _ Hj)) as [E|[E|[E|E]]]; rewrite E; lia.
    - unfold frame. constructor; [| constructor; [| constructor; [| constructor; [exact CT| constructor; [| constructor]]]]]; cbn [fst snd].
      + eapply rw_cells_transport; [exact CH0| exact MU| exact WM| rewrite SZ0; cbn; lia].
      + eapply rw_cells_transport; [exact CH1| exact MU| exact WM| rewrite SZ1; cbn; lia].
      + eapply rw_cells_transport; [exact CH2| exact MU| exact WM| unfold t2cells; cbn; lia].
      + eapply rw_cells_transport; [exact CHR| exact MU| exact WM| cbn; lia].
    - apply frame_chs; [exact ADDRS| exact SZ0| exact SZ1| exact SZ2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L14183320444.145L16383529852.141L20768697212.144L20886428674.148L22163852504.149L22972055896.149L25741856728.149L31421052760.149L33232266840.149L34987518552.149L38933900164.144L40381826456.140L42453240196.142L42842486707.149L46207024836.147L48958709976.149L50418110332.142L50880469597.147L50971899524.143L52536714200.149L54485996676.141L55456219004.143L57408231128.149L60968405464.149L63021424004.146L6337837188.145 L64900869464.149L67838020445.146L68463140952.14900000D00X00l01Q01e02902M02a03503I03n04B04g05;05`06406H06`07E07Y08>08R08f09:09_0:D0:X0;00;DS2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ13SPBS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1". (* [comment removed for export] *)
  Lemma L_ret : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (ls : list mpd) (dW : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word) (r : Z)
      (xra x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq ls dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    Forall (fun d : mpd => md_own d = LNull) ls -> locals_at ls ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> -2^31 < r <= 0 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x10 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21120) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ NUL ADDRS SZ0 SZ1 Hr VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    destruct ls as [|dX [|dY [|dZ [|dT [|]]]]]; try discriminate ADDRS. unfold locals_at in ADDRS. cbn [map] in ADDRS. injection ADDRS as EX EY EZ ET.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 2%nat. intros CX _. flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 2%nat. intros CY _.
    flat constr:((struct_cells _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 2%nat. intros CZ _. flat constr:((struct_cells _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 2%nat. intros CT _.
    rewrite EX in CX. rewrite EY in CY. rewrite EZ in CZ. rewrite ET in CT. unfold mpi_cells in CX, CY, CZ, CT.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ NUL)) 11%nat. intros HH HT MF MW OUT BK PX SOK MI ST CH.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CH3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CH3, CHR. clear CH. unfold t2cells in CH2. unfold tcells in CH3.
    do 14 zstep.
    release_frame CH0 ST (bv_unsigned sp + -220). release_frame CH1 ST (bv_unsigned sp + -208). release_frame CH2 ST (bv_unsigned sp + -192).
    release_frame CT ST (bv_unsigned sp + -176). release_frame CZ ST (bv_unsigned sp + -160).
    release_frame CY ST (bv_unsigned sp + -144). release_frame CX ST (bv_unsigned sp + -128).
    release_frame CH3 ST (bv_unsigned sp + -104). release_frame CHR ST (bv_unsigned sp).
    zstep. zstep.
    apply aevtM_done. unfold mpi_binop_post. do 14 eexists. exists mq, moq, hq, LBq, dW, r.
    split; [rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|]. split; [exact HH|]. split; [exact MW|]. split; [exact OUT|].
    split; [exact PX|]. split; [exact SOK|]. split; [split; [exact Hr| intros _; exact VB]| exact BK].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L13659511229.173L13669996316.152L1580607933.13  L17212449742.13 L19560486331.13 L21569116183.173L24510991059.50 L25076085156.173L28880104979.179L30175564334.173L34212198041.13 L4418925311.179 L46452486793.13 L49854881245.179L52151142969.173L56996652244.13 L62491849196.173L63451487318.17900000]01J01_01c02@02T02U02i03G03l04304Q04n05L05`06A06U073S1L3HLS2sp2lo3SLO3ACL3cs03tpc3SZ03SZ13SPB3ACPS1L3HLS2sp2lo3SLO3ACL3cs03tpc3SZ03SZ13SPB3ACPS1L3HLS2sp2lo3SLO3SPBS2spS1L3HLS2sp2lo3SLO3ACL3DHI3SPBS2sp3cs03tpc3SZ03SZ1FS2sp3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc2EX3SZ03SZ13SPBS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPBS2sp2loS2sp2dT3cs03tpc2ET3SZ03SZ13SPBS1L3HLS2sp2lo3SLO3ACL3SPB3ACPS2sp2dZ3cs03tpc2EZ3SZ03SZ13SPBS2sp3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2sp3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc2EY3SZ03SZ13SPB". (* [comment removed for export] *)
  Lemma L_c4 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (ls : list mpd) (dW : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word) (r : Z)
      (xra x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq ls dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    Forall (fun d : mpd => md_own d = LNull) ls -> locals_at ls ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> -2^31 < r <= 0 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x10 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21114) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ NUL ADDRS SZ0 SZ1 Hr VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof CS_ as CS2. dest_cs CS2.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CH3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CH3, CHR.
    flat constr:((rw_cells_forget _ _ _ _ CH1)) 2%nat. intros jk HTP. rewrite SZ1 in HTP.
    zstep. zstep. zstep.
    pose proof HPZ as SPZ. unfold platform_zeroize_stmt, U_PLATFORM_ZEROIZE in SPZ.
    eapply aevtM_cut_evt; [exact MK| eapply SPZ with (A := bv_unsigned sp + -220) (n := 12) (lo := lo);
      rewrite ?unsigned_lit by lia; try eassumption; try reflexivity|].
    all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP; lia).
    clear SPZ. cbv beta. intros ms' PO. unfold platform_zeroize_post in PO. destruct_exs PO.
    flat constr:(PO) 7%nat. flclear PO. intros -> MU WM MI9 HZ ST9 SOK9. rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in ST9 by lia.
    lazymatch type of MI9 with mem_inv _ ?mx => rename mx into m9 end.
    change (Z.to_nat 12) with 12%nat in HZ.
    replace (ret_pc (Z_to_bv 64 0x21120)) with (Z_to_bv 64 0x21120) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CS9 : CST m9 moq hq LBq ls dW [] (frame cs0 [CB 12 (repeat (Z_to_bv 8 0) 12)] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -220) (bv_unsigned sp + -220 + 12) [(bv_unsigned sp + -288 - 16, bv_unsigned sp + -288)]);
        [exact CS_| exact MU| exact WM| exact MI9| exact ST9| lia| lia| constructor; [cbn; lia| constructor]| reflexivity| | |].
      - intros j d d' Hj Hj'. rewrite Hj in Hj'. injection Hj' as <-. left. split; [| reflexivity].
        destruct ls as [|dX [|dY [|dZ [|dT [|]]]]]; try discriminate ADDRS. unfold locals_at in ADDRS. cbn [map] in ADDRS. injection ADDRS as EX EY EZ ET.
        destruct j as [|[|[|[|j]]]]; cbn in Hj; [injection Hj as <-; lia| injection Hj as <-; lia| injection Hj as <-; lia| injection Hj as <-; lia| destruct j; discriminate Hj].
      - unfold frame. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd].
        + eapply rw_cells_transport; [exact CH0| exact MU| exact WM| cbn; lia].
        + exact HZ.
        + eapply rw_cells_transport; [exact CH2| exact MU| exact WM| cbn; lia].
        + eapply rw_cells_transport; [exact CH3| exact MU| exact WM| cbn; lia].
        + eapply rw_cells_transport; [exact CHR| exact MU| exact WM| cbn; lia].
      - apply frame_chs; [exact ADDRS| exact SZ0| reflexivity| reflexivity]. }
    eapply L_ret; [exact CS9| exact NUL| exact ADDRS| exact SZ0| reflexivity| exact Hr| exact VB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma struct_cells4 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PCS,(8.(42.$0.(8.$3<.)))Pi,$4=.Pd,$:.P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R9.R8.R7.R6.R5.R4.(4?.$9.)R3.(4?.(42.$0.(8.$3<.))))P,(2.(5.$:.)(50.$:.R6.R3.)(51.$:.R2.))(3=.$4<.R;.(15.R3.)(3?.$3<.(5=.(25.&40.(17.R3.)))(3?.$3<.(62.(25.&40.(1>.(23.(13.&40.(25.&40.(53.R3.)))(33.+2.+10.))(18.(33.+2.+10.)(13.&40.(25.&40.(19.R3.)))))))(3?.$3<.(62.(54.R3.))(4?.$3<.)))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW CS i d CS_ Hi. flat constr:((struct_cells _ _ _ _ _ _ _ _ _ CS_ Hi)) 2%nat. intros HR _.
    exact (rw_cells_join_C2C2 usegs _ _ [C8 (Z_to_bv 64 (md_p d))] _ _ [C4 (md_pad d)] HR).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0120@D10908883426.171D10908883426.205D15025413049.170D15025413049.204D25171652884.170D25171652884.171D5082246559.204 D5082246559.205 L11256634148.17 L11803372707.198L11803467811.197L13659511220.196L13669995008.172L18995400495.171L18995400495.205L21566755998.198L22664147823.172L26305953715.167L26305953715.201L27686886378.172L28352298078.203L28666111625.17 L29261381519.169L29261381519.170L29261381519.203L29261381519.204L31316368120.171L38219033343.17 L39841611158.170L39841611158.204L40294144274.169L41417906040.172L41869551710.198L44622288685.170L44622288685.171L44622288685.204L44622288685.205L49698585326.170L49698585326.171L49698585326.204L49698585326.205L502283462.172  L50329172952.168L50329172952.202L50404856158.198L53725336461.169L54655697231.169L54655697231.170L54655697231.203L54655697231.204L56998505552.17 L59308628179.11 L59308628179.166L59453988272.196L60904343898.17 L62441238750.197L62441274457.169L64949111006.198L67574626780.170L67576843498.172L67771692925.169L68433886131.169L8015720451.167 L8015720451.201 L9862353012.168 L9862353012.202 00000d01[02O03F04@05:06>07B07]08L09;09k0:[0;>0;d0<;0<R0<f0==0=W0=n0=o0>R0?50?[0@A0@X0@e0AH0An0BL0Bc0C:0D60E20F10G00GW0H>0Hh0IR0J30JG0J^0K50KI0Kl0LO0M50M[0N<0NF0N`0O70OE0O\0P00PG0Q<0QV0R40RR0Rf0S=0SQ0ShS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dT3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dT3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3cs03tpc3SZ03SZ13SPB3HTc2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3cs03tpc3SZ03SZ13SPB3HTc2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dT3cs03tpc3SZ03SZ13SPB3HTc2h23HT22HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dT3cs03tpc3SZ03SZ13SPB3HTc2h23HT22HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3SPB3HTcS1L3HLS2sp2lo3SLO3ACL2dT3cs03tpc3SZ03SZ13SPB2P4S1L3HLS2sp2lo3SLO3ACL2dT3cs03tpc3SZ03SZ13SPB2P4S1L3HLS2sp2lo3SLO3ACL2dT3cs03tpc3SZ03SZ13SPB3ACPS1L3HLS2sp2lo3SLO3ACL2dT3cs03tpc3SZ03SZ13SPB3ACPS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ12NTS2sp2dT3cs03tpc3SZ03SZ1FS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ1S1L2sp2lo3SLOS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ13SPB2EYS2sp2dT3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dT3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dT3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ13SPB2N12HLS2sp3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dT3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2dT2P02K0S2sp2dT3cs03tpc3SZ03SZ12K0S2sp2dT3cs03tpc3SZ03SZ1S2sp2dT3SPB2NTS2sp2dT3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL2dT3cs03tpc3SZ03SZ13SPB2P02N12P4S2sp2dT3cs03tpc3SZ03SZ12NTS2sp2dZ3cs03tpc3SZ03SZ13SPB2EZS2sp2dX3cs03tpc3SZ03SZ13SPB2EXS2sp3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ1". (* [comment removed for export] *)
  Lemma L_c3 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT dW : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word) (r : Z)
      (xra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    md_own dX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> locals_at [dX; dY; dZ; dT] ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> -2^31 < r <= 0 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 1) x1 (Z_to_bv 64 (md_p dT)) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x10 t3 t4 t5 t6)
          F (Z_to_bv 64 0x210fc) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ OX OY OZ ADDRS SZ0 SZ1 Hr VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as EX EY EZ ET.
    pose proof CS_ as CS2. dest_cs CS2. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CH3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CH3, CHR. unfold t2cells in CH2.
    flat constr:((struct_cells _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 5%nat. intros CT SGT NT TNUL THEAP. rewrite ET in CT.
    pose proof (struct_cells4 _ _ _ _ _ _ _ 3 dT CS_ eq_refl) as CT4. rewrite ET in CT4.
    destruct (md_own dT) eqn:OT; [| | exfalso; exact (proj1 (proj2 (proj1 (Forall_forall _ _) LOK dT ltac:(right; right; right; left; reflexivity))) OT)].
    - (* [comment removed for export] *)
      flat constr:((TNUL eq_refl)) 2%nat. intros P0 N0. rewrite P0.
      zstep; if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
      pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp + -176)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
      clear CT. rewrite P0, N0 in CT4.
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells usegs m3 (bv_unsigned sp + -192) _ |- _ =>
        pose proof (rw_cells_split_C4 usegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 (md_pad dT)] H) as CT3 end.
      assert (CS3 : CST m3 moq hq LBq [dX; dY; dZ; set_sg dT 1] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -192) (bv_unsigned sp + -176) []);
          [exact CS_| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| | |].
        - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
            [left; split; [lia| reflexivity]| left; split; [lia| reflexivity]| left; split; [lia| reflexivity]|].
          right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. rewrite ET, P0, N0. unfold mpi_cells. exact CT3.
        - unfold frame, t2cells. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd]; assumption.
        - apply frame_chs; [| exact SZ0| exact SZ1| reflexivity]. unfold locals_at. cbn [map set_sg md_addr]. rewrite EX, EY, EZ, ET. reflexivity. }
      eapply L_c4; [exact CS3| | | exact SZ0| exact SZ1| exact Hr| exact VB].
      + constructor; [exact OX| constructor; [exact OY| constructor; [exact OZ| constructor; [cbn; exact OT| constructor]]]].
      + unfold locals_at. cbn [map set_sg md_addr]. rewrite EX, EY, EZ, ET. reflexivity.
    - (* [comment removed for export] *)
      flat constr:((THEAP eq_refl)) 2%nat. intros P0 N1.
      flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 8%nat. intros FLt6 _ _ _ _ _ HF _. flat constr:(FLt6) 2%nat. flclear FLt6. intros FLt7 _. flat constr:(FLt7) 6%nat. flclear FLt7. intros _ _ _ HL _ HO.
      rewrite OT in HO. flat constr:(HO) 4%nat. flclear HO. intros _ INT _ U32. flat constr:((HF OT)) 5%nat. intros _ P4 _ _ _.
      zstep; if_cases K0; zify_cond K0; [exfalso; clear - K0 P0 P4 ACL SLO SPB HLS; rewrite ?Z.mod_small in K0 by lia; lia|].
      unfold mpi_cells in CT. zstep. zstep. zstep.
      apply u32arr_cells in U32.
      pose proof HZF as SZF. unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE in SZF.
      eapply aevtM_cut.
      { eapply SZF with (buf := md_p dT) (len := 4 * md_n dT) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc NT; unfold MPI_MAX_LIMBS in *; lia).
        all: try (right; split; [exact INT| replace (Z.to_nat (4 * md_n dT)) with (4 * length (md_limbs dT))%nat by lia; exact U32]).
        all: unfold MPI_MAX_LIMBS in NT; rewrite zx16_small by lia; rewrite unsigned_lit by lia; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia. }
      clear SZF. cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 26%nat. flclear PO. intros y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 E MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
      injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
      replace (ret_pc (Z_to_bv 64 0x2110c)) with (Z_to_bv 64 0x2110c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      (* [comment removed for export] *)
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 CT4 ltac:(apply client_range_stack; cbn; lia) ltac:(cbn; lia)) as CT2.
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH0; [| apply client_range_stack; cbn; lia| cbn; rewrite SZ0; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH1; [| apply client_range_stack; cbn; lia| cbn; rewrite SZ1; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH2; [| apply client_range_stack; cbn; lia| cbn; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CHR; [| apply client_range_stack; cbn; lia| cbn; lia].
      pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp + -176)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj HH2 I) as HH2c. pose proof (conj SOK2 I) as SOK2c. pose proof (conj MI2 I) as MI2c. pose proof (conj ST2 I) as ST2c.
      clear CT CT4 U32.
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells usegs m3 (bv_unsigned sp + -192) _ |- _ =>
        pose proof (rw_cells_split_C4 usegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 (md_pad dT)] H) as CT3 end.
      flat constr:(HH2c) 2%nat. flclear HH2c. intros HH2' _. flat constr:(SOK2c) 2%nat. flclear SOK2c. intros SOK2' _. flat constr:(MI2c) 2%nat. flclear MI2c. intros MI2' _. flat constr:(ST2c) 2%nat. flclear ST2c. intros ST2' _.
      assert (MU' : munch [(md_addr dT, md_addr dT + 16)] m2 m3) by (rewrite ET; replace (bv_unsigned sp + -192 + 16) with (bv_unsigned sp + -176) by lia; exact MU).
      assert (CS3 : CST m3 mo2 h2 (lb_remove (md_p dT) LBq) (set_nth 3 [dX; dY; dZ; dT] (mkMPD (md_addr dT) 1 0 0 [] (md_pad dT) LNull)) dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_release _ _ _ _ _ _ _ _ _ 3 dT m2); [exact CS_| reflexivity| exact OT| exact HH2'| exact HT2| exact MF2| exact PX2| exact SOK2'| exact MI2'| exact ST2'| exact MU'| exact WM| assumption|].
        rewrite ET. unfold mpi_cells. exact CT3. }
      cbn [set_nth] in CS3.
      eapply L_c4; [exact CS3| | | exact SZ0| exact SZ1| exact Hr| exact VB].
      + constructor; [exact OX| constructor; [exact OY| constructor; [exact OZ| constructor; [cbn; reflexivity| constructor]]]].
      + unfold locals_at. cbn [map md_addr]. rewrite EX, EY, EZ, ET. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0160@D25171652884.170D25171652884.171D41386762978.171D41386762978.205D5082246559.204 D5082246559.205 D53128511161.170D53128511161.204L11256634148.17 L11803372707.198L11803467811.197L13082847747.167L13082847747.201L13659511220.196L13669995008.172L17592780024.171L19064786548.168L19064786548.202L20618429872.196L21566755998.198L26305953715.167L26305953715.201L26330050393.169L26330211294.197L28613692238.172L28666111625.17 L29150155311.171L29150155311.205L29261381519.169L29261381519.170L29261381519.203L29261381519.204L29613760150.170L29613760150.204L32170603598.172L32172556664.170L32530317453.169L36605650392.168L36605650392.202L38219033343.17 L38448898255.169L40871966482.169L41381347763.169L41417906040.172L4173929907.167 L4173929907.201 L41869551710.198L44622288685.170L44622288685.171L44622288685.204L44622288685.205L49698585326.170L49698585326.171L49698585326.204L49698585326.205L502283462.172  L50404856158.198L54655697231.169L54655697231.170L54655697231.203L54655697231.204L56966996062.203L56998505552.17 L59308628179.11 L59308628179.166L60904343898.17 L62441274462.198L62608923839.172L64949111006.198L67073866621.16900000j01d02X03O04S05W06K07B07]08L09;09O09f0:V0;F0;]0<10<H0<_0=60=J0=a0>50>L0>f0>g0?J0@00@S0A60A\0BB0Be0CK0Ce0DZ0Dn0EB0EY0Ef0F@0F^0G<0GS0Gg0H>0HU0IQ0JM0KL0LK0M20MY0NC0Nm0ON0Oe0PH0Pk0QQ0R70RN0Ro0S90SS0Sa0T80TO0Tf0TgS1L2HI2sp1h4HTOP2hq3cs03tpc3SZ03SZ13SPB3HTc2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3cs03tpc3SZ03SZ13SPB3HTc2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dZ3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dZ3cs03tpc3SZ03SZ13SPB3HTc2h23HT22HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dZ3cs03tpc3SZ03SZ13SPB3HTc2h23HT22HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dZ3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3SPB3HTcS1L3HLS2sp2lo3SLO3ACL2dZ3cs03tpc3SZ03SZ13SPB2P4S1L3HLS2sp2lo3SLO3ACL2dZ3cs03tpc3SZ03SZ13SPB2P4S2sp3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL2dZ3cs03tpc3SZ03SZ13SPB3ACPS1L3HLS2sp2lo3SLO3ACL2dZ3cs03tpc3SZ03SZ13SPB3ACPS2sp2dZ3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ12NTFS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ12NTS1L3HLS2sp2lo3SLO3ACL2dZ3cs03tpc3SZ03SZ13SPB2P02N12P4S2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S1L2sp2lo3SLOS2sp2dT3cs03tpc3SZ03SZ12E3S2sp2dY3cs03tpc3SZ03SZ13SPB2E1S2sp2dX3cs03tpc3SZ03SZ13SPB2E0S2sp2dZ3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dZ3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dZ3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ13SPB2N12HLS2sp2dZ3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2dZ2P02K0S2sp2dZ3cs03tpc3SZ03SZ12K0S2sp2dZ3SPB2NTS2sp2dZ3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ1F". (* [comment removed for export] *)
  Lemma L_c2 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT dW : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word) (r : Z)
      (xra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    md_own dX = LNull -> md_own dY = LNull -> locals_at [dX; dY; dZ; dT] ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> -2^31 < r <= 0 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 1) x1 (Z_to_bv 64 (md_p dZ)) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x10 t3 t4 t5 t6)
          F (Z_to_bv 64 0x210dc) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ OX OY ADDRS SZ0 SZ1 Hr VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    pose proof CS_ as CS2. dest_cs CS2. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CH3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CH3, CHR. unfold t2cells in CH2.
    flat constr:((struct_cells _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 5%nat. intros CT SGT NT TNUL THEAP. rewrite E2 in CT.
    pose proof (struct_cells4 _ _ _ _ _ _ _ 2 dZ CS_ eq_refl) as CT4. rewrite E2 in CT4.
    flat constr:((struct_cells _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 2%nat. intros CN _. rewrite E3 in CN. unfold mpi_cells in CN.
    destruct (md_own dZ) eqn:OT; [| | exfalso; exact (proj1 (proj2 (proj1 (Forall_forall _ _) LOK dZ ltac:(cbn; tauto))) OT)].
    - (* [comment removed for export] *)
      flat constr:((TNUL eq_refl)) 2%nat. intros P0 N0. rewrite P0.
      zstep; if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
      pose proof (munch_refl [(bv_unsigned sp + -176, bv_unsigned sp + -160)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
      clear CT. rewrite P0, N0 in CT4.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells usegs m3 (bv_unsigned sp + -176) _ |- _ =>
        pose proof (rw_cells_split_C4 usegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 (md_pad dZ)] H) as CT3 end.
      assert (CS3 : CST m3 moq hq LBq [dX; dY; set_sg dZ 1; dT] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -176) (bv_unsigned sp + -160) []);
          [exact CS_| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| | |].
        - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
            try (left; split; [lia| reflexivity]).
          right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. rewrite E2, P0, N0. unfold mpi_cells. exact CT3.
        - unfold frame, t2cells. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd]; assumption.
        - apply frame_chs; [| exact SZ0| exact SZ1| reflexivity]. unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity. }
      eapply L_c3; [exact CS3| exact OX| exact OY| cbn; exact OT| | exact SZ0| exact SZ1| exact Hr| exact VB].
      unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity.
    - (* [comment removed for export] *)
      flat constr:((THEAP eq_refl)) 2%nat. intros P0 N1.
      flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 8%nat. intros FLt8 _ _ _ _ _ HF _. flat constr:(FLt8) 2%nat. flclear FLt8. intros FLt9 _. flat constr:(FLt9) 6%nat. flclear FLt9. intros _ _ _ HL _ HO.
      rewrite OT in HO. flat constr:(HO) 4%nat. flclear HO. intros _ INT _ U32. flat constr:((HF OT)) 5%nat. intros _ P4 _ _ _.
      zstep; if_cases K0; zify_cond K0; [exfalso; clear - K0 P0 P4 ACL SLO SPB HLS; rewrite ?Z.mod_small in K0 by lia; lia|].
      unfold mpi_cells in CT. zstep. zstep. zstep.
      apply u32arr_cells in U32.
      pose proof HZF as SZF. unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE in SZF.
      eapply aevtM_cut.
      { eapply SZF with (buf := md_p dZ) (len := 4 * md_n dZ) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc NT; unfold MPI_MAX_LIMBS in *; lia).
        all: try (right; split; [exact INT| replace (Z.to_nat (4 * md_n dZ)) with (4 * length (md_limbs dZ))%nat by lia; exact U32]).
        all: unfold MPI_MAX_LIMBS in NT; rewrite zx16_small by lia; rewrite unsigned_lit by lia; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia. }
      clear SZF. cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 26%nat. flclear PO. intros y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 E MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
      injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
      replace (ret_pc (Z_to_bv 64 0x210ec)) with (Z_to_bv 64 0x210ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 CT4 ltac:(apply client_range_stack; cbn; lia) ltac:(cbn; lia)) as CT2.
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CN; [| apply client_range_stack; cbn; lia| cbn; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH0; [| apply client_range_stack; cbn; lia| cbn; rewrite SZ0; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH1; [| apply client_range_stack; cbn; lia| cbn; rewrite SZ1; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH2; [| apply client_range_stack; cbn; lia| cbn; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CHR; [| apply client_range_stack; cbn; lia| cbn; lia].
      pose proof (munch_refl [(bv_unsigned sp + -176, bv_unsigned sp + -160)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj HH2 I) as HH2c. pose proof (conj SOK2 I) as SOK2c. pose proof (conj MI2 I) as MI2c. pose proof (conj ST2 I) as ST2c.
      clear CT CT4 U32.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells usegs m3 (bv_unsigned sp + -176) _ |- _ =>
        pose proof (rw_cells_split_C4 usegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 (md_pad dZ)] H) as CT3 end.
      flat constr:(HH2c) 2%nat. flclear HH2c. intros HH2' _. flat constr:(SOK2c) 2%nat. flclear SOK2c. intros SOK2' _. flat constr:(MI2c) 2%nat. flclear MI2c. intros MI2' _. flat constr:(ST2c) 2%nat. flclear ST2c. intros ST2' _.
      assert (MU' : munch [(md_addr dZ, md_addr dZ + 16)] m2 m3) by (rewrite E2; replace (bv_unsigned sp + -176 + 16) with (bv_unsigned sp + -160) by lia; exact MU).
      assert (CS3 : CST m3 mo2 h2 (lb_remove (md_p dZ) LBq) (set_nth 2 [dX; dY; dZ; dT] (mkMPD (md_addr dZ) 1 0 0 [] (md_pad dZ) LNull)) dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_release _ _ _ _ _ _ _ _ _ 2 dZ m2); [exact CS_| reflexivity| exact OT| exact HH2'| exact HT2| exact MF2| exact PX2| exact SOK2'| exact MI2'| exact ST2'| exact MU'| exact WM| assumption|].
        rewrite E2. unfold mpi_cells. exact CT3. }
      cbn [set_nth] in CS3.
      eapply L_c3; [exact CS3| exact OX| exact OY| cbn; reflexivity| | exact SZ0| exact SZ1| exact Hr| exact VB].
      unfold locals_at. cbn [map md_addr]. rewrite E0, E1, E2, E3. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0160@D25171652884.169D25171652884.170D31233843170.170D31233843170.204D5082246559.203 D5082246559.204 D63331163577.169D63331163577.203L11256634148.17 L11803372707.197L11803467811.196L1348784222.202 L13659511220.195L13669995008.171L14165749133.168L17301622520.170L18411264003.166L18411264003.200L19427622806.169L19427622806.203L20329969712.195L21566755998.197L22881030104.167L22881030104.201L24949834288.171L26330050398.197L28506356230.169L28508311344.171L28666111625.17 L29156352274.168L29261381519.168L29261381519.169L29261381519.202L29261381519.203L38219033343.17 L38366464601.168L38366496478.196L38756668111.168L39319860527.170L39319860527.204L41417906040.171L4173929907.166 L4173929907.200 L41869551710.197L43066521523.168L44594781145.171L44622288685.169L44622288685.170L44622288685.203L44622288685.204L49698585326.169L49698585326.170L49698585326.203L49698585326.204L502283462.171  L50404856158.197L50764594099.166L50764594099.200L54655697231.168L54655697231.169L54655697231.202L54655697231.203L56633909117.168L56998505552.17 L58666067060.167L58666067060.201L59308628179.11 L59308628179.165L60904343898.17 L64949111006.19700000j01d02X03O04S05W06K07B07]08L09;09R0:B0;20;F0;]0<10<H0<k0=Q0=h0>?0>S0>j0?D0?[0@P0@j0@k0@l0AO0B20BX0C>0CK0C_0D60DP0E30EY0F00FD0F[0G20GP0Gg0Hc0I_0J^0K]0LD0Lk0MU0N?0N`0O70OK0Ob0PE0Ph0QN0R40RN0Ro0SC0SZ0Sd0T>0TL0TcS1L2HI2sp1h4HTOP2hq3cs03tpc3SZ03SZ13SPB3HTc2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3cs03tpc3SZ03SZ13SPB3HTc2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dY3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dY3cs03tpc3SZ03SZ13SPB3HTc2h23HT22HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dY3cs03tpc3SZ03SZ13SPB3HTc2h23HT22HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dY3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3SPB3HTcS1L3HLS2sp2lo3SLO3ACL2dY3cs03tpc3SZ03SZ13SPB2P4S1L3HLS2sp2lo3SLO3ACL2dY3cs03tpc3SZ03SZ13SPB2P4S2sp2dY3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL2dY3cs03tpc3SZ03SZ13SPB3ACPS1L3HLS2sp2lo3SLO3ACL2dY3cs03tpc3SZ03SZ13SPB3ACPS2sp3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ12NTS2sp2dY3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL2dY3cs03tpc3SZ03SZ13SPB2P02N12P4S2sp2dY3cs03tpc3SZ03SZ12NTFFS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS1L2sp2lo3SLOS2sp3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ12E3S2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ13SPB2E0S2sp2dY3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dY3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dY3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ13SPB2N12HLS2sp2dY3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dZ3cs03tpc3SZ03SZ12E2S1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2sp3cs03tpc3SZ03SZ1S2sp2dY3cs03tpc3SZ03SZ1S2dY2P02K0S2sp2dY3cs03tpc3SZ03SZ12K0S2sp2dY3SPB2NTS2sp2dY3cs03tpc3SZ03SZ1". (* [comment removed for export] *)
  Lemma L_c1 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT dW : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word) (r : Z)
      (xra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    md_own dX = LNull -> locals_at [dX; dY; dZ; dT] ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> -2^31 < r <= 0 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 1) x1 (Z_to_bv 64 (md_p dY)) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x10 t3 t4 t5 t6)
          F (Z_to_bv 64 0x210c0) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ OX ADDRS SZ0 SZ1 Hr VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    pose proof CS_ as CS2. dest_cs CS2. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CH3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CH3, CHR. unfold t2cells in CH2.
    flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 5%nat. intros CT SGT NT TNUL THEAP. rewrite E1 in CT.
    pose proof (struct_cells4 _ _ _ _ _ _ _ 1 dY CS_ eq_refl) as CT4. rewrite E1 in CT4.
    flat constr:((struct_cells _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 2%nat. intros CN _. rewrite E2 in CN. unfold mpi_cells in CN.
    destruct (md_own dY) eqn:OT; [| | exfalso; exact (proj1 (proj2 (proj1 (Forall_forall _ _) LOK dY ltac:(cbn; tauto))) OT)].
    - (* [comment removed for export] *)
      flat constr:((TNUL eq_refl)) 2%nat. intros P0 N0. rewrite P0.
      zstep; if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
      pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -144)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
      clear CT. rewrite P0, N0 in CT4.
      zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells usegs m3 (bv_unsigned sp + -160) _ |- _ =>
        pose proof (rw_cells_split_C4 usegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 (md_pad dY)] H) as CT3 end.
      assert (CS3 : CST m3 moq hq LBq [dX; set_sg dY 1; dZ; dT] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -160) (bv_unsigned sp + -144) []);
          [exact CS_| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| | |].
        - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
            try (left; split; [lia| reflexivity]).
          right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. rewrite E1, P0, N0. unfold mpi_cells. exact CT3.
        - unfold frame, t2cells. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd]; assumption.
        - apply frame_chs; [| exact SZ0| exact SZ1| reflexivity]. unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity. }
      eapply L_c2; [exact CS3| exact OX| cbn; exact OT| | exact SZ0| exact SZ1| exact Hr| exact VB].
      unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity.
    - (* [comment removed for export] *)
      flat constr:((THEAP eq_refl)) 2%nat. intros P0 N1.
      flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 8%nat. intros FLt10 _ _ _ _ _ HF _. flat constr:(FLt10) 2%nat. flclear FLt10. intros FLt11 _. flat constr:(FLt11) 6%nat. flclear FLt11. intros _ _ _ HL _ HO.
      rewrite OT in HO. flat constr:(HO) 4%nat. flclear HO. intros _ INT _ U32. flat constr:((HF OT)) 5%nat. intros _ P4 _ _ _.
      zstep; if_cases K0; zify_cond K0; [exfalso; clear - K0 P0 P4 ACL SLO SPB HLS; rewrite ?Z.mod_small in K0 by lia; lia|].
      unfold mpi_cells in CT. zstep. zstep. zstep.
      apply u32arr_cells in U32.
      pose proof HZF as SZF. unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE in SZF.
      eapply aevtM_cut.
      { eapply SZF with (buf := md_p dY) (len := 4 * md_n dY) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc NT; unfold MPI_MAX_LIMBS in *; lia).
        all: try (right; split; [exact INT| replace (Z.to_nat (4 * md_n dY)) with (4 * length (md_limbs dY))%nat by lia; exact U32]).
        all: unfold MPI_MAX_LIMBS in NT; rewrite zx16_small by lia; rewrite unsigned_lit by lia; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia. }
      clear SZF. cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 26%nat. flclear PO. intros y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 E MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
      injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
      replace (ret_pc (Z_to_bv 64 0x210d0)) with (Z_to_bv 64 0x210d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 CT4 ltac:(apply client_range_stack; cbn; lia) ltac:(cbn; lia)) as CT2.
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CN; [| apply client_range_stack; cbn; lia| cbn; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH0; [| apply client_range_stack; cbn; lia| cbn; rewrite SZ0; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH1; [| apply client_range_stack; cbn; lia| cbn; rewrite SZ1; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH2; [| apply client_range_stack; cbn; lia| cbn; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CHR; [| apply client_range_stack; cbn; lia| cbn; lia].
      pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -144)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj HH2 I) as HH2c. pose proof (conj SOK2 I) as SOK2c. pose proof (conj MI2 I) as MI2c. pose proof (conj ST2 I) as ST2c.
      clear CT CT4 U32.
      zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells usegs m3 (bv_unsigned sp + -160) _ |- _ =>
        pose proof (rw_cells_split_C4 usegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 (md_pad dY)] H) as CT3 end.
      flat constr:(HH2c) 2%nat. flclear HH2c. intros HH2' _. flat constr:(SOK2c) 2%nat. flclear SOK2c. intros SOK2' _. flat constr:(MI2c) 2%nat. flclear MI2c. intros MI2' _. flat constr:(ST2c) 2%nat. flclear ST2c. intros ST2' _.
      assert (MU' : munch [(md_addr dY, md_addr dY + 16)] m2 m3) by (rewrite E1; replace (bv_unsigned sp + -160 + 16) with (bv_unsigned sp + -144) by lia; exact MU).
      assert (CS3 : CST m3 mo2 h2 (lb_remove (md_p dY) LBq) (set_nth 1 [dX; dY; dZ; dT] (mkMPD (md_addr dY) 1 0 0 [] (md_pad dY) LNull)) dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_release _ _ _ _ _ _ _ _ _ 1 dY m2); [exact CS_| reflexivity| exact OT| exact HH2'| exact HT2| exact MF2| exact PX2| exact SOK2'| exact MI2'| exact ST2'| exact MU'| exact WM| assumption|].
        rewrite E1. unfold mpi_cells. exact CT3. }
      cbn [set_nth] in CS3.
      eapply L_c2; [exact CS3| exact OX| cbn; reflexivity| | exact SZ0| exact SZ1| exact Hr| exact VB].
      unfold locals_at. cbn [map md_addr]. rewrite E0, E1, E2, E3. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@D25171652884.170D25171652884.171D36655585506.171D36655585506.205D5082246559.204 D5082246559.205 D58585641145.170D58585641145.204L11256634148.17 L11803372707.198L11803467811.197L13659511220.196L13669995008.172L14437957682.172L16962092547.167L16962092547.201L19158930680.171L21566755998.198L24418977839.171L24418977839.205L25640717784.168L25640717784.202L26904339663.169L28666111625.17 L29261381519.169L29261381519.170L29261381519.203L29261381519.204L29831040345.169L29831070174.197L29997040734.203L31212100019.169L32362796660.168L32362796660.202L35068792982.170L35068792982.204L37079340467.157L37079340467.167L37079340467.201L38219033343.17 L38366464606.198L40663242775.172L41417906040.172L41869551710.198L44622288685.170L44622288685.171L44622288685.204L44622288685.205L44915514130.169L49698585326.170L49698585326.171L49698585326.204L49698585326.205L502283462.172  L50404856158.198L50764594099.167L50764594099.201L52942226301.169L54326083588.170L54327801138.172L54655697231.169L54655697231.170L54655697231.203L54655697231.204L56998505552.17 L59308628179.11 L59308628179.166L60904343898.17 L6459626125.169 L64949111006.198L8393545776.196 00000j01d02X03O04S05W06K07B07]08L09;09k0:[0;50;I0;`0<70<N0=10=W0=k0>B0>\0>]0?@0?c0@I0@o0AC0AZ0B10B20BF0B]0C@0Cf0D:0DN0De0E20EI0E`0F70FN0GJ0HF0IE0JD0J^0KE0Kl0LV0M@0Ma0N80NL0Nc0O=0P20PL0Po0QR0R80R^0S?0SI0Sc0T10TE0T\0U3S1L2HI2sp1h4HTOP2hq3cs03tpc3SZ03SZ13SPB3HTc2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3cs03tpc3SZ03SZ13SPB3HTc2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dX3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dX3cs03tpc3SZ03SZ13SPB3HTc2h23HT22HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dX3cs03tpc3SZ03SZ13SPB3HTc2h23HT22HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dX3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3SPB3HTcS1L3HLS2sp2lo3SLO3ACL2dX3cs03tpc3SZ03SZ13SPB2P4S1L3HLS2sp2lo3SLO3ACL2dX3cs03tpc3SZ03SZ13SPB2P4S1L3HLS2sp2lo3SLO3ACL2dX3cs03tpc3SZ03SZ13SPB3ACPS1L3HLS2sp2lo3SLO3ACL2dX3cs03tpc3SZ03SZ13SPB3ACPS2sp2dX3cs03tpc3SZ03SZ12NTS2sp3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp2dT3cs03tpc3SZ03SZ12E3FS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1FS2sp3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S1L2sp2lo3SLOS2sp2dX3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S1L3HLS2sp2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dX3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dX3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dY3cs03tpc3SZ03SZ12E1S2sp3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ13SPB2N12HLS2sp2dX3cs03tpc3SZ03SZ1S2sp3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp2dZ3cs03tpc3SZ03SZ12E2S1L3HLS2sp2lo3SLO3ACL2dX3cs03tpc3SZ03SZ13SPB2P02N12P4S2sp2dX3cs03tpc3SZ03SZ12NTS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dX3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2dX2P02K0S2sp2dX3cs03tpc3SZ03SZ12K0S2sp2dX3SPB2NTS2sp3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1S2sp2dX3cs03tpc3SZ03SZ1". (* [comment removed for export] *)
  Lemma L_c0 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT dW : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word) (r : Z)
      (xra x0 xa0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> -2^31 < r <= 0 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 x0 x1 xa0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x10 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2109c) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_  ADDRS SZ0 SZ1 Hr VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    pose proof CS_ as CS2. dest_cs CS2. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CH3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CH3, CHR. unfold t2cells in CH2.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 2%nat. intros C0 _. rewrite E0 in C0. unfold mpi_cells in C0.
    zstep. clear C0.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 5%nat. intros CT SGT NT TNUL THEAP. rewrite E0 in CT.
    pose proof (struct_cells4 _ _ _ _ _ _ _ 0 dX CS_ eq_refl) as CT4. rewrite E0 in CT4.
    flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 2%nat. intros CN _. rewrite E1 in CN. unfold mpi_cells in CN.
    destruct (md_own dX) eqn:OT; [| | exfalso; exact (proj1 (proj2 (proj1 (Forall_forall _ _) LOK dX ltac:(cbn; tauto))) OT)].
    - (* [comment removed for export] *)
      flat constr:((TNUL eq_refl)) 2%nat. intros P0 N0. rewrite P0.
      zstep; if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
      pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -128)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
      clear CT. rewrite P0, N0 in CT4.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells usegs m3 (bv_unsigned sp + -144) _ |- _ =>
        pose proof (rw_cells_split_C4 usegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 (md_pad dX)] H) as CT3 end.
      assert (CS3 : CST m3 moq hq LBq [set_sg dX 1; dY; dZ; dT] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -144) (bv_unsigned sp + -128) []);
          [exact CS_| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| | |].
        - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
            try (left; split; [lia| reflexivity]).
          right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. rewrite E0, P0, N0. unfold mpi_cells. exact CT3.
        - unfold frame, t2cells. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd]; assumption.
        - apply frame_chs; [| exact SZ0| exact SZ1| reflexivity]. unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity. }
      eapply L_c1; [exact CS3| cbn; exact OT| | exact SZ0| exact SZ1| exact Hr| exact VB].
      unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity.
    - (* [comment removed for export] *)
      flat constr:((THEAP eq_refl)) 2%nat. intros P0 N1.
      flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 8%nat. intros FLt12 _ _ _ _ _ HF _. flat constr:(FLt12) 2%nat. flclear FLt12. intros FLt13 _. flat constr:(FLt13) 6%nat. flclear FLt13. intros _ _ _ HL _ HO.
      rewrite OT in HO. flat constr:(HO) 4%nat. flclear HO. intros _ INT _ U32. flat constr:((HF OT)) 5%nat. intros _ P4 _ _ _.
      zstep; if_cases K0; zify_cond K0; [exfalso; clear - K0 P0 P4 ACL SLO SPB HLS; rewrite ?Z.mod_small in K0 by lia; lia|].
      unfold mpi_cells in CT. zstep. zstep. zstep.
      apply u32arr_cells in U32.
      pose proof HZF as SZF. unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE in SZF.
      eapply aevtM_cut.
      { eapply SZF with (buf := md_p dX) (len := 4 * md_n dX) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc NT; unfold MPI_MAX_LIMBS in *; lia).
        all: try (right; split; [exact INT| replace (Z.to_nat (4 * md_n dX)) with (4 * length (md_limbs dX))%nat by lia; exact U32]).
        all: unfold MPI_MAX_LIMBS in NT; rewrite zx16_small by lia; rewrite unsigned_lit by lia; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia. }
      clear SZF. cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 26%nat. flclear PO. intros y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 E MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
      injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
      replace (ret_pc (Z_to_bv 64 0x210b0)) with (Z_to_bv 64 0x210b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 CT4 ltac:(apply client_range_stack; cbn; lia) ltac:(cbn; lia)) as CT2.
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CN; [| apply client_range_stack; cbn; lia| cbn; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH0; [| apply client_range_stack; cbn; lia| cbn; rewrite SZ0; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH1; [| apply client_range_stack; cbn; lia| cbn; rewrite SZ1; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CH2; [| apply client_range_stack; cbn; lia| cbn; lia].
      apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2) in CHR; [| apply client_range_stack; cbn; lia| cbn; lia].
      pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -128)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj HH2 I) as HH2c. pose proof (conj SOK2 I) as SOK2c. pose proof (conj MI2 I) as MI2c. pose proof (conj ST2 I) as ST2c.
      clear CT CT4 U32.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells usegs m3 (bv_unsigned sp + -144) _ |- _ =>
        pose proof (rw_cells_split_C4 usegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 (md_pad dX)] H) as CT3 end.
      flat constr:(HH2c) 2%nat. flclear HH2c. intros HH2' _. flat constr:(SOK2c) 2%nat. flclear SOK2c. intros SOK2' _. flat constr:(MI2c) 2%nat. flclear MI2c. intros MI2' _. flat constr:(ST2c) 2%nat. flclear ST2c. intros ST2' _.
      assert (MU' : munch [(md_addr dX, md_addr dX + 16)] m2 m3) by (rewrite E0; replace (bv_unsigned sp + -144 + 16) with (bv_unsigned sp + -128) by lia; exact MU).
      assert (CS3 : CST m3 mo2 h2 (lb_remove (md_p dX) LBq) (set_nth 0 [dX; dY; dZ; dT] (mkMPD (md_addr dX) 1 0 0 [] (md_pad dX) LNull)) dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_release _ _ _ _ _ _ _ _ _ 0 dX m2); [exact CS_| reflexivity| exact OT| exact HH2'| exact HT2| exact MF2| exact PX2| exact SOK2'| exact MI2'| exact ST2'| exact MU'| exact WM| assumption|].
        rewrite E0. unfold mpi_cells. exact CT3. }
      cbn [set_nth] in CS3.
      eapply L_c1; [exact CS3| cbn; reflexivity| | exact SZ0| exact SZ1| exact Hr| exact VB].
      unfold locals_at. cbn [map md_addr]. rewrite E0, E1, E2, E3. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  Definition set_limbs (d : mpd) (xs : list word) : mpd := mkMPD (md_addr d) (md_sg d) (md_n d) (md_p d) xs (md_pad d) (md_own d).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L26983617546.8900000=S2sp1d1H1a2Ha". (* [comment removed for export] *)
  Lemma copy_sep_of_opnd : forall dX d lo' SP', opnd_sep dX d lo' SP' -> 0 <= md_addr d -> copy_sep dX d lo' SP'.
  Proof. intros dX d lo' SP' (O1 & O2 & O3 & O4 & O5) H. repeat (split; [assumption|]). intros a Ha. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma w_cells : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PCS,(8.(42.$0.(8.$3<.)))P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R7.R6.R5.R4.R3.R2.(4?.$9.)R1.(4?.(42.$0.(8.$3<.))))(31.(3=.$4<.R8.(15.VdR,)(52.(17.R3.)(25.&40.(53.R3.))(19.R3.)(54.R3.)))(1.(2.$0.(53.R3.)+1.)(2.$0.(53.R3.)-1.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW CS CS_. flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 4%nat. intros ((HR & _) & SG) _ EA _. rewrite <- EA. split; [exact HR| exact SG].
  Qed.

  (* [comment removed for export] *)
  Lemma a_cells : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PCS,(8.(42.$0.(8.$3<.)))P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R6.R5.R4.R3.R2.VdR,(4?.$9.)R1.(4?.(42.$0.(8.$3<.))))(31.(3=.$4<.R7.(15.VdA,)(52.(17.VdA,)(25.&40.(53.VdA,))(19.VdA,)(54.VdA,)))(1.(2.$0.(53.VdA,)+1.)(2.$0.(53.VdA,)-1.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls CS CS_. destruct opndA as [IN| E].
    - flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ _ CS_ IN)) 2%nat. intros ((HR & _) & SG) _. split; [exact HR| exact SG].
    - rewrite E. exact (w_cells _ _ _ _ _ _ _ CS_).
  Qed.

  (* [comment removed for export] *)
  Lemma L_err : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT dW : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word) (r : Z)
      (xra x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> -2^31 < r <= 0 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 x0 x1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21098) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ ADDRS SZ0 SZ1 Hr VB.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    zstep. eapply L_c0; [exact CS_| exact ADDRS| exact SZ0| exact SZ1| exact Hr| exact VB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00_0@D25171652884.165D36655585506.165L11254569731.15 L13659429513.218L13669995826.230L13669996291.188L13669996301.212L14556395849.164L14663433941.51 L15320268189.202L16075584073.224L1708597535.163 L1757360398.221 L18488752909.218L23820113652.163L24251438683.18 L24418977839.165L25299033648.163L25640717403.161L26736792481.230L27133795837.16 L29010565666.196L29261381519.163L30643776732.188L32362797047.161L34793580623.7  L39208609841.214L42807770878.163L43969051919.16 L44622288685.165L49698585326.165L50784042690.163L53134281077.4  L54655697231.163L56996506737.15 L56996506743.15 L58263820824.15 L61272441834.235L61274419438.231L61303316184.15 L61486577777.15 L62256779294.17 L64450501233.17 L66151410442.202L6963552950.230 L8069655616.163 L8518083130.16  00001302002K03>04504h05_05`05a06M06N06k07Y08008G08H09109N09e0:T0:U0:V0;?0<20<I0<W0=40=50=60>;0>h0?E0?S0@<0@]0A>0AS0An0BI0BV0BZ0B[0B\0C^0D90DP0DQS1L2HI2sp1h2dR2dA4HTOP2hq3cs03tpc3SZ03SZ13SPB2R03HTc2HB5Ha_st5Hl_stS1L3HLS2sp2dR2dA2lo3SLO3cs03tpc3SZ03SZ13SPB2R02HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq3SPB3HT1S1L3HLS2sp2dR2lo3SLO3ACL3cs03tpc3SZ03SZ13SPB3ACP2R0S1L3HLS2sp2dR2lo3SLO3ACL3cs03tpc3SZ03SZ13SPB3ACP2R03dW2S1L3HLS2sp2dR2lo3SLO3ACL3cs03tpc3SZ03SZ13SPB3ACP2R0S1L3HLS2sp2dR2lo3SLO3ACL3cs03tpc3SZ03SZ13SPB3ACP2R03dW2FFS2sp2dR2dA2dX3cs03tpc3SZ03SZ13SPB2R01r2Hr2K0FS2sp2dR2dY3cs03tpc3SZ03SZ12E1S2sp2dR2dA2dX3cs03tpc3SZ03SZ13dW22NB3SPB2R02ENS2sp2dR3cs03tpc3SZ03SZ1S2sp2dR3cs03tpc3SZ03SZ1FS2sp2dR2dA3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS2sp2dR2dZ3cs03tpc3SZ03SZ12E2S2sp2dR3cs03tpc3SZ03SZ1S1L3HLS2sp2dR2lo3SLO3cs03tpc3SZ03SZ13SPB2R03dW2FFS2sp2dR2dA3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS1L3HLS2sp2dR2lo3SLO3ACL3cs03tpc3SZ03SZ13SPB3ACP2R0S2sp2dR3cs03tpc3SZ03SZ1S2sp2dR2lo3RASS2sp2dR3cs03tpc3SZ03SZ13dW21HFFS1L3HLS2sp2dR2dA2lo3SLO3ACL3DHI3cs03tpc3SZ03SZ13SPB2R02HB5Ha_st5Hl_stS2sp2dR2dA3cs03tpc3SZ03SZ13SPB2HB5Ha_st5Hl_stS2sp2dR2dT3cs03tpc3SZ03SZ12E3S1L2lo3ACL3ACPS2sp2dR2dA3cs03tpc3SZ03SZ12HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2sp2lo3SLO3SPBS2sp2dR3cs03tpc3SZ03SZ13dW2S2sp2dR3cs03tpc3SZ03SZ13dW2S1L2sp2lo3SLOS2spFFS1L3HLS2sp2dR2dA2lo3SLO2dX3cs03tpc3SZ03SZ13SPB2R03RAS4ASW11r2Hr2K0S2sp2dR3cs03tpc3SZ03SZ13dW2S2sp2dR3cs03tpc3SZ03SZ1F". (* [comment removed for export] *)
  Lemma L_fin2 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word)
      (xra x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] -> cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x215ac) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ ADDRS SZ0 SZ1 VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:(facts0) 8%nat. intros R0 R8 RAS RBLK HBR _ _ _.
    pose proof CS_ as CS2. dest_cs CS2. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CH3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CH3, CHR. unfold t2cells in CH2.
    flat constr:((a_cells _ _ _ _ _ _ CS_)) 2%nat. intros CA_ SGA. unfold mpi_cells in CA_.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 4%nat. intros CX SGX NX _. rewrite E0 in CX. unfold mpi_cells in CX.
    (* [comment removed for export] *)
    zstep. rewrite (sx16_sign _ SGA).
    pose proof (munch_refl [(bv_unsigned sp + -136, bv_unsigned sp + -134)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CS1 : CST m1 moq hq LBq [set_sg dX (md_sg dA); dY; dZ; dT] dR [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -136) (bv_unsigned sp + -134) []);
        [exact CS_| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| | |].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          try (left; split; [lia| reflexivity]).
        right. exists (md_sg dA). split; [reflexivity|]. split; [exact SGA|]. rewrite E0. unfold mpi_cells. assumption.
      - unfold frame, t2cells. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd]; assumption.
      - apply frame_chs; [| exact SZ0| exact SZ1| reflexivity]. unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity. }
    clear MU WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS1)) 10%nat. intros MW1 NSW1 EA1 WR1 LW1 CRW1 CRWL1 HFW1 ASW1 WA8.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 _ CS1 eq_refl)) 8%nat. intros MX1 NSX1 _ LX1 CRX1 CRXL1 HFX1 _.
    flat constr:((mc_opnd_sep_wl _ _ _ _ _ _ _ _ _ 0 _ CS1 eq_refl)) 2%nat. intros SEP1 OPS1.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS1)) 8%nat. intros HH1 HT1 MF1 SOK1 MI1 ST1 _ MK1.
    pose proof HCOPY as SPC. unfold mpi_copy_stmt_x, U_MPI_COPY in SPC.
    eapply aevtM_cut.
    { eapply SPC with (dX := dR) (dY := set_sg dX (md_sg dA)) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HT1; lia).
      - apply copy_sep_of_opnd; [exact OPS1| cbn [set_sg md_addr]; rewrite E0; lia].
      - cbn [set_sg md_addr]. rewrite E0. reflexivity. }
    clear SPC. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 31%nat. flclear PO. intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 (CR & TRIM).
    injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
    replace (ret_pc (Z_to_bv 64 0x215c0)) with (Z_to_bv 64 0x215c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(CR) 4%nat. flclear CR. intros CR1 CAD CPD CFR.
    assert (CS3 : CST m2 mo2 h2 LB2 [set_sg dX (md_sg dA); dY; dZ; dT] dW2 [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_w; [exact CS1| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact CFR| exact CPD|].
      destruct CR1 as [(_ & _ & NB)|(_ & EN & _)]; lia. }
    assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct CR1 as [(Hr0 & _)|(HrF & _)]; [left; exact Hr0| right; exact HrF]).
    clear CS1 CS_ MX1 MW1 HH HTc MF LOK SA LA MW WOK EXOK SUB COV FRS EXT PX SOK CH CHS CXH CXS MK HH1 HT1 MF1 SOK1 MK1.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS3)) 8%nat. intros HH3 HT3 MF3 SOK3 MI3 ST3 _ MK3.
    zstep; if_cases K0; zify_cond K0.
    - eapply L_err; [exact CS3| | exact SZ0| exact SZ1| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB].
      unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity.
    - assert (Hr0 : r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r.
      assert (ADDRS3 : locals_at [set_sg dX (md_sg dA); dY; dZ; dT]) by (unfold locals_at; cbn [map set_sg md_addr]; rewrite E0, E1, E2, E3; reflexivity).
      flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS3)) 10%nat. intros MW3 NSW3 EA3 WR3 LW3 CRW3 CRWL3 HFW3 ASW3 WA83.
      flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS3)) 5%nat. intros FC0 FC1 FC2 FCT FCR. unfold tcells in FCT.
      pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp + -104)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      zstep. zstep.
      match type of FCT with rw_cells _ _ _ ?tc =>
        assert (CS4 : CST m4 mo2 h2 LB2 [set_sg dX (md_sg dA); dY; dZ; dT] dW2 [] (frame cs0 tpc j68 tc) [])
          by (eapply cs_frame_updT; [exact CS3| exact ADDRS3| exact MU| exact WM| assumption| assumption| lia| lia| exact FCT| reflexivity| exact SZ0| exact SZ1])
      end.
      clear CS3 MU WM HH3 HT3 MF3 SOK3 MK3 MW3 NSW3 EA3 WR3 LW3 CRW3 CRWL3 HFW3 ASW3 WA83.
      flat constr:((cs_parts _ _ _ _ _ _ _ CS4)) 8%nat. intros HH4 HT4 MF4 SOK4 MI4 ST4 _ MK4.
      flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS4)) 10%nat. intros MW4 NSW4 EA4 WR4 LW4 CRW4 CRWL4 HFW4 ASW4 WA84.
      destruct (rw_cells_split3 _ _ _ [C4 t160] [C4 (Z_to_bv 64 0)] _ FCT) as (FT0 & FL & FS).
      change (Z.of_nat (cells_size [C4 t160])) with 4 in FL, FS. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4 in FS.
      replace (bv_unsigned sp + -128 + 4) with (bv_unsigned sp + -124) in FL, FS by lia.
      replace (bv_unsigned sp + -124 + 4) with (bv_unsigned sp + -120) in FS by lia.
      pose proof FL as BL. destruct BL as [[_ BL] _].
      pose proof HCMPO as SPC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in SPC.
      eapply aevtM_cut_evt; [exact MK4| eapply SPC with (LB := LB2) (dX := dW2)
          (dY := mkMPD (bv_unsigned sp + -120) 1 1 (bv_unsigned sp + -124) [Z_to_bv 64 0] t180 LStatic);
          rewrite ?unsigned_lit by lia; try eassumption; try reflexivity|].
      all: try (rewrite ?EA4; reflexivity).
      { left. exact MW4. }
      { right. unfold stack_opnd. cbn [md_own md_addr md_sg md_n md_p md_limbs md_pad].
        split; [reflexivity|]. split.
        { unfold mpi_cells.
          pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 (bv_unsigned sp + -124))] _ [C4 t180] FS) as FS2.
          cbn [app] in FS2. rewrite unsigned_lit in FS2 by lia. change (65537 / 2 ^ 16) with 1 in FS2.
          refine (rw_cells_C2_congr _ _ _ [_] _ _ _ FS2 _). reflexivity. }
        cbn -[Z.modulo Z.pow Z.add Z.mul MPI_MAX_LIMBS u32s bytes_at].
        split; [Stdlib.micromega.Lia.lia|]. split; [Stdlib.micromega.Lia.lia|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; Stdlib.micromega.Lia.lia|].
        split; [Stdlib.micromega.Lia.lia|]. split; [Stdlib.micromega.Lia.lia|]. split; [Stdlib.micromega.Lia.lia|]. split; [exact BL|]. split; [Stdlib.micromega.Lia.lia|]. split; [Stdlib.micromega.Lia.lia|].
        left; reflexivity. }
      { intros O. flat constr:((HFW4 O)) 2%nat. intros P0 _. exact P0. }
      { cbn. intros E. discriminate E. }
      clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO.
      flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
      replace (mpd_val (mkMPD (bv_unsigned sp + -120) 1 1 (bv_unsigned sp + -124) [Z_to_bv 64 0] t180 LStatic)) with 0
        by (unfold mpd_val; cbn [md_sg md_limbs limbs_val]; rewrite ?unsigned_lit by lia; reflexivity).
      replace (ret_pc (Z_to_bv 64 0x215e8)) with (Z_to_bv 64 0x215e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep; if_cases K1; zify_cond K1.
      + zstep. zstep; if_cases KA; zify_cond KA;
        [ exfalso; rewrite <- EA4 in KA; change 7 with (Z.ones 3) in KA; rewrite Z.land_ones in KA by Stdlib.micromega.Lia.lia;
          apply KA; change (2^3) with 8; clear - WA84; Stdlib.micromega.Lia.lia |].
        flat constr:((w_cells _ _ _ _ _ _ _ CS4)) 2%nat. intros CW4 SGW. unfold mpi_cells in CW4.
        zstep.
        pose proof (munch_refl [(md_addr dR, md_addr dR + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
        clear HH4 SOK4.
        zstep. zstep.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        match type of CS4 with context [frame cs0 tpc j68 ?tc4] =>
          assert (CS5 : CST m5 mo2 h2 LB2 [set_sg dX (md_sg dA); dY; dZ; dT] (set_sg dW2 1) [] (frame cs0 tpc j68 tc4) [])
            by (eapply mc_sign_w; [exact CS4| rewrite EA4; exact MU| exact WM| assumption| rewrite EA4; unfold mpi_cells; assumption| left; reflexivity])
        end.
        zstep.
        eapply L_c0; [exact CS5| exact ADDRS3| exact SZ0| exact SZ1| lia| exact VB].
      + zstep. zstep.
        eapply L_c0; [exact CS4| exact ADDRS3| exact SZ0| exact SZ1| lia| exact VB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L1133773802.23  L13669995828.180L13669996307.158L14437958945.158L14440461318.147L19158930811.145L24509182583.56 L24510886384.42 L24897143244.3  L24897143244.42 L24897143244.5  L26736795524.5  L27937054984.3  L34070288688.180L34070289175.158L36767584348.23 L36950922632.2  L37079340080.156L38643945643.144L39572645029.23 L49966973991.23 L54326083846.147L56998993008.23 L57750334761.23 L58263967292.5  L59308546259.153L59308628179.1  L59308628304.4  L61480980804.23 L64858652715.1  00000J01O02K02k03K03e03f03g03k03o04304D04M05305P05Q05R05o06L06M06N06n07R07_08008\08`08m09;09?S1L2sp2lo3ACL2dX3SPB2HL2P4S1L3HLS2sp2dR2lo3SLO3ACL2dX3cs03tpc3SZ03SZ13SPB3ACP2R02WB2P03x234LEN2S1L3HLS2sp2dR2lo3SLO3ACL2dX3cs03tpc3SZ03SZ13SPB3ACP2R02WB2P0S2sp2dR2dX3cs03tpc3SZ03SZ12NX2WBS2sp2dR2dX3cs03tpc3SZ03SZ12NX2WBS2sp2dR3cs03tpc3SZ03SZ12WBFFS2dXS2dXS2dXS1L3HLS2sp2lo3SLOS2dX1q2HqS2sp2dR2dX3cs03tpc3SZ03SZ12WB3xs24LEN2S2sp2dR2dX3cs03tpc3SZ03SZ12WBFSS2sp2dR2dX3cs03tpc3SZ03SZ12WBS2sp2dR3cs03tpc3SZ03SZ12R02WBFFS2sp2dR2dX3cs03tpc3SZ03SZ12NX2WBS1L3HLS2sp2lo3SLO3ACL3SPA2dX3SPB3ACPS2sp2dX2NX2K2S1L3HLS2sp2lo3SLOS2sp2dR2dX3cs03tpc3SZ03SZ12R02NX2WB2K12K22HOS2K0S2dR2R02WB2K1S2sp2dX3SPB2HLS2dX". (* [comment removed for export] *)
  Lemma L_fin : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (j0 : list byte) (w8 w16 w24 w40 w48 w56 : word) (j64 : list byte) (tpc : list cell)
      (j68 t160 t164 t168 t176 t180 : word) (k : Z)
      (xra x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 w56; CB 4 j64]
         tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] -> cells_size tpc = 12%nat -> 0 <= k < 2^64 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21564) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ ADDRS SZ1 Hk VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:(facts0) 8%nat. intros R0 R8 RAS RBLK HBR _ _ _.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 5%nat. intros CX SGX NX XNUL XHEAP.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CF0 CF1 CF2 CFT CFR.
    zstep; if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; clear - K0; Stdlib.micromega.Lia.lia].
    flat constr:((w_cells _ _ _ _ _ _ _ CS_)) 2%nat. intros CW _. pose proof (rw_cells_bound _ _ _ _ CW) as WB. unfold mpi_cells in WB. cbn [cells_size csize Nat.add] in WB. clear CW.
    zstep; if_cases K1; zify_cond K1; [exfalso; clear - K1 R0 WB; rewrite ?Z.mod_small in K1 by Stdlib.micromega.Lia.lia; Stdlib.micromega.Lia.lia|].
    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 8%nat. intros MX NSX _ _ _ _ HF _.
    pose proof HSHR as SSH. unfold mpi_shift_r_stmt, U_MPI_SHIFT_R in SSH.
    eapply aevtM_cut_evt; [exact MK| eapply SSH with (LB := LBq) (dX := dX) (count := k) (lo := lo);
      rewrite ?unsigned_lit by lia; try eassumption; try reflexivity|].
    all: try (intros O; flat constr:((HF O)) 5%nat; intros P0 P4 _ _ _; split; clear - P0 P4 ACL; Stdlib.micromega.Lia.lia).
    all: try (rewrite E0; first [left; clear - SLO HLS SPB SPA ACL; Stdlib.micromega.Lia.lia| right; clear - SLO HLS SPB SPA ACL; Stdlib.micromega.Lia.lia]).
    all: try (intros O; flat constr:((HF O)) 5%nat; intros P0 P4 _ _ _; right; rewrite E0; clear - P4 SLO HLS SPB ACL; Stdlib.micromega.Lia.lia).
    all: try (rewrite E0; f_equal; clear; Stdlib.micromega.Lia.lia).
    all: try (clear - SLO HLS SPB SPA ACL; Stdlib.micromega.Lia.lia).
    clear SSH. cbv beta. intros ms' PO. unfold mpi_shift_r_post in PO.
    flat constr:(PO) 24%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 ys2 -> MU WM MI2 ST2 MA2 LEN2 _.
    rewrite ?unsigned_lit in MU, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x215ac)) with (Z_to_bv 64 0x215ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (md_own dX) eqn:OX; [| | exfalso; exact (NSX eq_refl)].
    - flat constr:((XNUL eq_refl)) 2%nat. intros _ N0.
      match type of MU with munch (?r1 :: _) _ _ =>
        assert (MU' : munch [r1] mq m2) by (eapply munch_weaken; [| exact MU]; intros x [Hx _]; cbn [outside]; rewrite N0; split; [exact Hx| split; [Stdlib.micromega.Lia.lia| exact I]])
      end.
      match type of CS_ with context [frame ?a ?b ?c ?d] =>
        assert (CS2 : CST m2 moq hq LBq [dX; dY; dZ; dT] dR [] (frame a b c d) [])
      end.
      { eapply (mc_munch _ _ _ _ _ _ _ _ _ None false false); [exact CS_| exact MU'| exact WM| exact MI2| exact ST2| | reflexivity| | | reflexivity| discriminate].
        - constructor; [left; cbn [fst snd]; clear - SLO HLS; Stdlib.micromega.Lia.lia| constructor].
        - intros j d d' Hj Hj'. rewrite Hj in Hj'. injection Hj' as <-. do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C].
        - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
      eapply L_fin2; [exact CS2| exact ADDRS| reflexivity| exact SZ1| exact VB].
    - pose proof (proj1 MA2) as MA2'. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in MA2'. try rewrite OX in MA2'.
      destruct MA2' as (_ & _ & _ & HL2 & _ & _ & _ & _ & U2).
      match type of CS_ with context [frame ?a ?b ?c ?d] =>
        assert (CS2 : CST m2 moq hq LBq [set_limbs dX ys2; dY; dZ; dT] dR [] (frame a b c d) [])
      end.
      { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 0%nat) false false); [exact CS_| exact MU| exact WM| exact MI2| exact ST2| | reflexivity| | | reflexivity| discriminate].
        - constructor; [left; cbn [fst snd]; clear - SLO HLS; Stdlib.micromega.Lia.lia| constructor; [right; left; exists 0%nat, dX; split; [reflexivity|]; split; [reflexivity|]; split; [exact OX|]; cbn [fst snd]; clear; Stdlib.micromega.Lia.lia| constructor]].
        - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
            [ | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
              | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
              | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
          cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OX]|].
          intros _ _. split; [exact U2| exact HL2].
        - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
      assert (ADDRS2 : locals_at [set_limbs dX ys2; dY; dZ; dT]) by (unfold locals_at; cbn [map set_limbs md_addr]; rewrite E0, E1, E2, E3; reflexivity).
      eapply L_fin2; [exact CS2| exact ADDRS2| reflexivity| exact SZ1| exact VB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition loop_loc (dX dY dZ dT : mpd) (n t zp : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "(31.(2.$?.(10.O7.)$16.)(31.(1=.(1>.O3.+1.)(19.O7.))(31.(2.$?.(10.O6.)$16.)(31.(1=.(1>.O2.+1.)(19.O6.))(31.(2.$?.(10.O5.)$16.)(31.(2.$0.(17.O5.)O1.)(31.(1=.(1>.O3.+2.)(19.O5.))(31.(2.$?.(10.O4.)$16.)(31.(1=.+2.(19.O4.))(32.=(61.VdB,)))))))))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Definition lframe (j0 : list byte) (w24 w32 w48 w56 : word) (j64 : list byte) (u0 u1 u2 j68 : word) (tcs : list cell) :=
    frame [CB 8 j0; C8 (Z_to_bv 64 65537); C8 (Z_to_bv 64 4294967295); C8 w24; C8 w32; C8 (Z_to_bv 64 (2^61)); C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 tcs
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40436988320.9800000CS2sp2dX1n3dX'2LE2H2". (* [comment removed for export] *)
  Lemma loop_loc_X : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "PdX,$:.PdY,$:.PdZ,$:.PdT,$:.Pn,$0.Pt,$0.Pzp,$0.PdX',$:.P,(64.R8.R7.R6.R5.R4.R3.R2.)P,(2.$?.(10.R2.)$16.)P,(1=.(19.R:.)(19.R3.))(64.R4.R:.R9.R8.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof. intros * H O LE. unfold loop_loc in *. decompose [and] H. repeat split; auto; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L44500370933.9800000AS2sp2dT3dT'2LE2H8". (* [comment removed for export] *)
  Lemma loop_loc_T : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "PdX,$:.PdY,$:.PdZ,$:.PdT,$:.Pn,$0.Pt,$0.Pzp,$0.PdT',$:.P,(64.R8.R7.R6.R5.R4.R3.R2.)P,(2.$?.(10.R2.)$16.)P,(1=.(19.R7.)(19.R3.))(64.R;.R:.R9.R4.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof. intros * H O LE. unfold loop_loc in *. decompose [and] H. repeat split; auto; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma loop_loc_Z : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "PdX,$:.PdY,$:.PdZ,$:.PdT,$:.Pn,$0.Pt,$0.Pzp,$0.Pzs,(8.(3.&40.))P,(64.R8.R7.R6.R5.R4.R3.R2.)(64.R9.R8.(65.R7.R2.)R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof. intros * H. unfold loop_loc in *. decompose [and] H. cbn. repeat split; auto. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24928467276.8400000<S2sp1d2N12N0". (* [comment removed for export] *)
  Lemma out_heap : forall mq LBq d, mpd_at usegs mq LBq d -> md_own d <> LStatic -> 1 <= md_n d -> md_own d = LHeap.
  Proof.
    intros mq LBq d [(_ & _ & _ & _ & _ & HO) _] NS N1. destruct (md_own d) eqn:O; [| reflexivity| exfalso; exact (NS eq_refl)].
    flat constr:(HO) 2%nat. flclear HO. intros _ N0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac reopen CS hh htc mf sok mi st mk :=
    try clear hh; try clear htc; try clear mf; try clear sok; try clear mi; try clear st; try clear mk;
    (flat constr:((cs_parts _ _ _ _ _ _ _ CS)) 8%nat; intros hh htc mf sok mi st _ mk).

  (* [comment removed for export] *)
  Local Ltac rdq H N i :=
    let RD := fresh "RD" in
    lazymatch type of H with u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_read sg mm A l i _ _ H N ltac:(lia) ltac:(f_equal; lia)) as RD end;
    zstep; clear RD.

  (* [comment removed for export] *)
  Local Ltac binop_post PO m2 mo2 h2 LB2 d2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR :=
    (flat constr:(PO) 31%nat; flclear PO; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 d2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR);
    injection E as -> ->; rewrite ?unsigned_lit in ST2 by lia; rewrite ?unsigned_lit in PX2 by lia.

  (* [comment removed for export] *)
  Lemma zbv_add_unsigned : forall v c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) + c) = Z_to_bv 64 (v + c).
  Proof.
    intros v c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
    rewrite Zplus_mod_idemp_l. reflexivity.
  Qed.
  Lemma zbv_mod : forall v, Z_to_bv 64 (v mod 18446744073709551616) = Z_to_bv 64 v.
  Proof.
    intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
    rewrite Zmod_mod. reflexivity.
  Qed.

  Notation LFR t k j0 j64 u0 u1 u2 j68 tcs :=
    (lframe j0 (Z_to_bv 64 (2^64 - (t + 2))) (Z_to_bv 64 k) (Z_to_bv 64 (4 * (t - 1))) (Z_to_bv 64 t) j64 u0 u1 u2 j68 tcs).
  (* [comment removed for export] *)
  Definition KONT (n t zp k ib : Z) (j0 j64 : list byte) : Prop :=
    forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word) (i : Z)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 x9 x10 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (lframe j0 (Z_to_bv 64 (2^64 - (t + 2))) (Z_to_bv 64 k) (Z_to_bv 64 (4 * (t - 1))) (Z_to_bv 64 t) j64 u0 u1 u2 j68
         (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    t < i <= n - 1 ->
    i <= ib ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 i)
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (4 * t))
               x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) x9 x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x211ec) fc None mq (seg_rom usegs))
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L32867416334.141L33675445158.3  L36635088338.141L54794051144.5  L57480193112.141L8638987958.141 00000G00P00g01401801>S2sp1n1t1i2T02IR2NB3SPBS2ib1i2IBS2sp1n1t1i2T02IR2NB3SPBS1n1t1i2IR2K0S2spS2sp1i". (* [comment removed for export] *)
  Lemma L_ltest : forall (n t zp k ib : Z) (j0 j64 : list byte), KONT n t zp k ib j0 j64 ->
    forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word) (i : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x5 x7 x10 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (lframe j0 (Z_to_bv 64 (2^64 - (t + 2))) (Z_to_bv 64 k) (Z_to_bv 64 (4 * (t - 1))) (Z_to_bv 64 t) j64 u0 u1 u2 j68
         (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    0 <= t -> t < i <= n -> i <= ib + 1 -> n <= 10000 -> 0 <= k < 2^64 ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 x5 (Z_to_bv 64 (4 * t))
               x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x21554) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros n t zp k ib j0 j64 K. intros until x10. intros CS_ ADDRS LL T0 IR IB NB Hk.
    flat constr:(LL) 10%nat. intros _ _ _ _ _ _ _ _ _ VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST _ MK.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CH0 CH1 CH2 CHT CHR.
    zstep. zstep. zstep. zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
    - (* [comment removed for export] *)
      replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + -1 + 1)) by (f_equal; lia).
      unfold KONT in K. eapply K; [exact CS_| exact ADDRS| exact LL| clear - K0 IR; lia| clear - IB; lia].
    - eapply L_fin; [exact CS_| exact ADDRS| reflexivity| exact Hk| exact VB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01\0@D4662108261.351 D49416158319.351D6690581324.351 L11256811570.18 L1171960623.160 L1171960623.346 L12734415834.10 L13072597906.347L13085246180.348L13475139986.21 L13659512551.233L13659512551.335L13669995825.268L13669996291.277L13669996297.178L13669996301.250L13669996307.195L13669996307.297L13672109588.207L13672109588.224L13672109588.262L13672109588.306L13672109588.326L13672109588.364L1455978384.207 L14678034333.350L14678034333.351L15320268189.190L15320268189.217L15320268189.244L15320268189.292L15320268189.319L15320268189.346L17098779603.333L18964789310.347L18964789310.350L18964789560.350L18964789560.351L19628513823.187L19648801077.268L21173714153.18 L22575357070.21 L24936921712.16 L25043585872.313L25808786958.16 L26736795524.5  L29010565666.189L29010565666.216L29010565666.243L29010565666.291L29010565666.318L29010565666.345L29317658691.187L3526235131.5   L35304777808.16 L35306758967.19 L35661609289.7  L35957772237.16 L36253289358.15 L39143142490.16 L42468655062.177L42471337514.159L42778200787.46 L43118069572.15 L45802789392.224L45804903191.195L46304178716.19 L46355679760.326L46357793559.297L47314680299.231L49158382690.268L50567194733.22 L5087926800.306 L50924227096.5  L51037667856.262L53003616607.17 L55006012123.16 L55971982931.311L56996506657.15 L56996506657.21 L56999012166.18 L57176871851.18 L58263820872.15 L59314841581.159L59314841581.345L60415926591.16 L61303316110.15 L61486577697.15 L62867946550.347L62867946800.350L62867946800.351L63036381883.15 L64529214665.22 L66151410442.190L66151410442.217L66151410442.244L66151410442.292L66151410442.319L66151410442.346L663383774.21   L66757147290.213L68351284511.16 L68634302992.364L7024305247.15  L7304674203.371 L9375591753.18  L9746144436.352 L9931864279.21  00000100Y01;01[01n02F02\03F04004K05705c06O07;07g08S09?09k0:W0;C0;o0<[0=G0>30>B0>C0>D0>c0?B0?a0@@0@_0A>0Ah0BH0Bh0CC0C^0DT0Dc0E50EB0EC0Em0En0F?0F@0FA0FB0FC0FD0FE0FT0Fe0Ff0Fg0G@0GA0GN0GO0G\0Gf0Gg0HB0HQ0H`0Ha0I00I?0If0JX0JY0Jh0Jo0K>0K?0K@0Ki0LJ0Lk0MQ0MR0Mg0NN0O:0O;0OH0OL0PG0QD0RA0R\0R]0S<0S[0T:0TY0U80UW0V20VV0VW0Vf0WA0X40X50X60XMFS2sp1n1t2zp2dZ1i2T02IR3SPB2NZ2wq1q1w3PZ0S2sp1n1t2zp2dZ1i2IR3SPB2wq1q1w3PZ0S1L2HI2sp1h4HTOP2hq3SPB3HTc2wq1qS2sp1n1t2zp2dZ1i2IRS2sp1n1t2zp2dZ1i2IR2wq1qS1n1t2zp2dZ1i2T02IR2NZS2sp1n1t2zp2dZ1i2T02IR3SPB2NZ2wq1q3HLZ3PZ0S2sp1n1t2zp2dZ1i2T02IR3SPB2NZ2wq1q3HLZ3PZ0S1L2HI2sp1h4HTOP3SPB2h63HTcS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS1L3HLS2sp2lo3SLO3ACL2zp2dZ3SPB3ACP3PZ02wq1qS2sp2zp2dZ2wq1qFFS2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2dB2zp2dZ3SPB3PZ02wq1q3dT63dT73KN73NT6S2sp1n1t2zp2dZ1i2IR3SPB2wq1q3PZ0S2sp1n1t2zp2dZ1i2IR3SPB2wq1q3PZ0S2sp1t2zp2dZ1i2wq1q1w5Ha_stS2sp1t2zp2dZ1i2wq1q1w5Ha_stS1L3HLS2sp2lo3SLO3ACL1n1t2zp2dZ1i2T02IR3SPB2NZ3PZ03PZ4S2sp2zp2dZ2wq1qS1L2sp2lo3SLO2wq1qS1L2sp2lo3SLOFS2sp2dB2zp2dZ3SPB3PZ02wq1q3dT33dT63KN63NT4FS1L3HLS2sp2lo3SLOFFFFFFS2sp2zp2dZ2wq1qS1L2lo3ACL3dX42P4FFS1L3HLS2sp2lo3SLO3ACL3ACPFS1L2sp2lo3SLOFS2sp2zp2dZ2wqS2sp2zp2dZFS1L2HI2sp1h4HTOP3SPB2h43HTcS2sp2zp2dZ2wq1qS2sp2zp2dZ2wq1qFS2sp2zp2dZ2wq1qS2sp2zp2dZ2wq1qS2sp2zp2dZ3SPB3PZ02wq1q3dT23dT33KN33NT2S2sp1n1t2zp2dX2dZ1i2T02IR3SPB3NXl3PZ02wq1q3dX43KN4FS2sp2zp2dZ2wq1qS2sp2loS2sp2zp2dZ2wq1qFFS2sp2zp2dY2dZ2wq1q3dT33dT63NB63SPB3PZ02ENS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACP2wq1qFS1L3HLS2sp2lo3SLO3SPBS2sp1n1t2zp2dZ1i2T02IR3SPB2NZ3HLZ3PZ01NS2sp1n1t2zp2dZ1i2T02IR3SPB2NZ2wq1q3HLZ3PZ01NFS1L2sp2lo3SLOS2spS1L3HLS2sp2lo3SLO3ACL1n1t2zp2dZ1i2T02IR3SPB2NZ2wq1q3PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2dZ1i2T02IR3SPB2NZ2wq1q1w3PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2dZ1i2T02IR3SPB2NZ2wq1q3PZ03PZ41wS1L2HI2sp1h4HTOP3SPB2h33HTcFS2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S2sp2zp2dZ3SPB3PZ02wq1q1r2Hr2K0S1L2HI2sp1h4HTOP3SPB2h23HTcS2sp2zp2dZ2dT3SPB2NT3PZ02wq1q3dT22KNFS2sp2zp2dZ2wq1qS1L2HI2sp1h4HTOP3SPB2h73HTcS2sp1n1t2zp2dZ1i2T02IR3SPB3PZ02wq1q3dX43dX83KN83NX7FFS2sp1n1t1i2T02IR2NB3SPB". (* [comment removed for export] *)
  Lemma L_bodyB : forall (n t zp k ib : Z) (j0 j64 : list byte), KONT n t zp k ib j0 j64 ->
    0 <= t -> n <= 10000 -> 0 <= k < 2^64 ->
    forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word) (i : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    t < i <= n -> i <= ib + 1 ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (zp + 4 * (i - t - 1))) x5 (Z_to_bv 64 (4 * t))
               (Z_to_bv 64 (4 * (i - t - 1))) (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) (Z_to_bv 64 (i - t - 1)) (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x214a8) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros n t zp k ib j0 j64 K T0 NB Hk. intros until x5. intros CS_ ADDRS LL IR IB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST _ MK.
    flat constr:(LL) 10%nat. intros OX NXl OY NY OZ PZ NZ OT NT VB.
    (* [comment removed for export] *)
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 8%nat. intros FLt17 _ _ _ _ _ HFZ _. flat constr:(FLt17) 2%nat. flclear FLt17. intros FLt18 _. flat constr:(FLt18) 6%nat. flclear FLt18. intros _ _ _ HLZ HNZ HOZ.
    rewrite OZ in HOZ. flat constr:(HOZ) 4%nat. flclear HOZ. intros _ INZ PALZ UZ. flat constr:((HFZ OZ)) 3%nat. intros PZ0 PZ4 _. unfold MPI_MAX_LIMBS in HNZ. rewrite PZ in *.
    rd UZ (i - t - 1).
    lazymatch goal with |- context [sx32 ?w] => rename w into wq end.
    set (q := bv_unsigned wq mod 4294967296).
    assert (QB : 0 <= q < 2^32) by (subst q; apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 8%nat. intros MY NSY WRY LOY CRY CRYL HFY _.
    flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 3 1 dT dY CS_ eq_refl eq_refl)) 2%nat. intros SEP31 OPS31.
    pose proof HMULI as SPM. unfold mpi_mul_int_stmt_g, U_MPI_MUL_INT in SPM.
    eapply aevtM_cut.
    { eapply SPM with (dX := dT) (dA := dY) (b := q) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc QB; lia).
      all: try (rewrite ?E0, ?E1, ?E2, ?E3; reflexivity).
      - subst q. rewrite bv_unsigned_sx32. apply sxz_mod32. apply Z.mod_pos_bound. lia.
      - subst q. rewrite bv_unsigned_sx32. apply sxz_zero_iff. apply Z.mod_pos_bound. lia. }
    clear SPM. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dT2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
    replace (ret_pc (Z_to_bv 64 0x214b8)) with (Z_to_bv 64 0x214b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros R1 FLt19. flat constr:(FLt19) 4%nat. flclear FLt19. intros KA KP KF KN.
    assert (CS2 : CST m2 mo2 h2 LB2 (set_nth 3 [dX; dY; dZ; dT] dT2) dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_l; [exact CS_| reflexivity| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact KF]. }
    cbn [set_nth] in CS2.
    assert (ADDRS2 : locals_at [dX; dY; dZ; dT2]) by (unfold locals_at; cbn [map]; rewrite KA, E0, E1, E2, E3; reflexivity).
    assert (LL2 : loop_loc dX dY dZ dT2 n t zp) by (eapply loop_loc_T; [exact LL| eapply out_heap; [exact MA2| exact (proj1 (proj2 OUT2))| lia]| exact KN]).
    assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct R1 as [(Hr0 & _)|HrF]; [left; exact Hr0| right; exact HrF]).
    clear MT NST WRT LOT CRT CRTL HFT MY NSY WRY LOY CRY CRYL HFY SEP31 OPS31 R1 KF KP MA2 OUT2 PX2 UZ CS_ LL ADDRS.
    reopen CS2 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    { eapply L_err; [exact CS2| exact ADDRS2| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB]. }
    assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
    (* [comment removed for export] *)
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT2 CS2 eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
    pose proof HSHL as SPS. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SPS.
    eapply aevtM_cut.
    { eapply SPS with (dX := dT2) (count := (i - t - 1) * 32) (lo := lo) (h := h2) (LB := LB2); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc IR T0 NB; lia).
      all: try (rewrite ?KA, ?E0, ?E1, ?E2, ?E3; reflexivity). }
    clear SPS. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m3 mo3 h3 LB3 dT3 r E MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR.
    replace (ret_pc (Z_to_bv 64 0x214cc)) with (Z_to_bv 64 0x214cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros R1 FLt20. flat constr:(FLt20) 4%nat. flclear FLt20. intros KA3 KP3 KF3 KN3.
    assert (CS3 : CST m3 mo3 h3 LB3 (set_nth 3 [dX; dY; dZ; dT2] dT3) dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_l; [exact CS2| reflexivity| exact HH3| exact HT3| exact MF3| exact MA3| exact OUT3| exact PX3| exact SOK3| exact MI3| exact ST3| exact KF3]. }
    cbn [set_nth] in CS3.
    assert (ADDRS3 : locals_at [dX; dY; dZ; dT3]) by (unfold locals_at; cbn [map]; rewrite KA3, KA, E0, E1, E2, E3; reflexivity).
    assert (LL3 : loop_loc dX dY dZ dT3 n t zp) by (eapply loop_loc_T; [exact LL2| eapply out_heap; [exact MA3| exact (proj1 (proj2 OUT3))| pose proof LL2 as (_&_&_&_&_&_&_&_&NT2&_); lia]| exact KN3]).
    assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct R1 as [(Hr0 & _)|HrF]; [left; exact Hr0| right; exact HrF]).
    clear MT NST WRT LOT CRT CRTL HFT R1 KF3 KP3 MA3 OUT3 PX3 CS2 LL2 ADDRS2.
    reopen CS3 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    { eapply L_err; [exact CS3| exact ADDRS3| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB]. }
    assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS3 eq_refl)) 8%nat. intros MX NSX WRX LOX CRX CRXL HFX _.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT3 CS3 eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
    flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0 0 dX dX CS3 eq_refl eq_refl)) 2%nat. intros SEP00 OPS00.
    flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0 3 dX dT3 CS3 eq_refl eq_refl)) 2%nat. intros SEP03 OPS03.
    pose proof (HAS (-1) (or_intror eq_refl)) as SPA_. 
    eapply aevtM_cut.
    { eapply SPA_ with (dX := dX) (dA := dX) (dB := dT3) (lo := lo) (h := h3) (LB := LB3); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?KA3, ?KA, ?E0, ?E1, ?E2, ?E3; reflexivity). }
    clear SPA_. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m4 mo4 h4 LB4 dX4 r E MI4 ST4 MF4 HT4 HH4 MA4 OUT4 PX4 SOK4 RR.
    replace (ret_pc (Z_to_bv 64 0x214e4)) with (Z_to_bv 64 0x214e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros R1 FLt21. flat constr:(FLt21) 4%nat. flclear FLt21. intros KA4 KP4 KF4 KN4.
    assert (CS4 : CST m4 mo4 h4 LB4 (set_nth 0 [dX; dY; dZ; dT3] dX4) dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_l; [exact CS3| reflexivity| exact HH4| exact HT4| exact MF4| exact MA4| exact OUT4| exact PX4| exact SOK4| exact MI4| exact ST4| exact KF4]. }
    cbn [set_nth] in CS4.
    assert (ADDRS4 : locals_at [dX4; dY; dZ; dT3]) by (unfold locals_at; cbn [map]; rewrite KA4, KA3, KA, E0, E1, E2, E3; reflexivity).
    assert (LL4 : loop_loc dX4 dY dZ dT3 n t zp) by (eapply loop_loc_X; [exact LL3| eapply out_heap; [exact MA4| exact (proj1 (proj2 OUT4))| lia]| exact KN4]).
    assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct R1 as [(Hr0 & _)|HrF]; [left; exact Hr0| right; exact HrF]).
    clear MX NSX WRX LOX CRX CRXL HFX MT NST WRT LOT CRT CRTL HFT SEP00 OPS00 SEP03 OPS03 R1 KF4 KP4 MA4 OUT4 PX4 CS3 LL3 ADDRS3.
    reopen CS4 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    { eapply L_err; [exact CS4| exact ADDRS4| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB]. }
    assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
    (* [comment removed for export] *)
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS4)) 5%nat. intros CH0 CH1 CH2 CHT CHR. unfold tcells in CHT.
    pose proof (munch_refl [(SP + -128, SP + -104)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    lazymatch type of CHT with rw_cells _ _ _ [C4 _; C4 ?a; C8 ?b; C4 ?c; C4 _] => remember a as v164 eqn:Ev164 in CHT; remember b as v168 eqn:Ev168 in CHT; remember c as v176 eqn:Ev176 in CHT end.
    assert (CS5 : CST m5 mo4 h4 LB4 [dX4; dY; dZ; dT3] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 v164 v168 v176 t180)) []).
    { eapply (cs_frame_updT _ _ _ _ _ _ _ _ _ _ (SP + -128) (SP + -104)); [exact CS4| exact ADDRS4| exact MU| exact WM| assumption| assumption| lia| lia| exact CHT| reflexivity| reflexivity| reflexivity]. }
    assert (EV168 : v168 = Z_to_bv 64 (SP + -124)) by (rewrite Ev168; rewrite ?unsigned_lit by lia; first [reflexivity| f_equal; lia]).
    assert (EV176 : le4 v176 = le2 (Z_to_bv 64 1) ++ le2 (Z_to_bv 64 1)).
    { rewrite Ev176. rewrite le4_split. unfold le2. change (bv_unsigned (Z_to_bv 64 1)) with 1. f_equal; first [reflexivity| rewrite <- Z_to_le_bytes_mod; reflexivity]. }
    pose proof CHT as CR. take CR 1%nat CA0. take CR 1%nat CL.
    assert (CR' : rw_cells usegs m5 (SP + -120) (mpi_cells (SP + -124) (Z_to_bv 64 1) 1 t180)).
    { unfold mpi_cells. eapply rw_cells_reshape; [exact CR| cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite EV168, EV176, <- app_assoc. reflexivity. }
    set (dTs := mkMPD (SP + -120) 1 1 (SP + -124) [v164] t180 LStatic).
    assert (OTs : stack_opnd usegs m5 (SP + -288) dTs).
    { unfold stack_opnd, dTs. cbn [md_own md_addr md_sg md_n md_p md_limbs md_pad length].
      split; [reflexivity|]. split; [exact CR'|]. split; [clear - SPA; Z.div_mod_to_equations; lia|]. split; [clear - SPB SLO HLS ACL ACP; lia|].
      split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; clear; lia|]. split; [clear; lia|]. split; [clear - SPA; Z.div_mod_to_equations; lia|].
      split; [clear - SPB SLO HLS ACL ACP; lia|]. split; [exact (proj2 (proj1 CL))|]. split; [clear; lia|]. split; [clear - SPB; lia| left; reflexivity]. }
    clear MU WM CR' EV168 EV176. repeat match goal with H : rw_cells usegs _ _ _ |- _ => clear H end.
    reopen CS5 HH HTc MF SOK MI ST MK.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX4 CS5 eq_refl)) 8%nat. intros MX NSX WRX LOX CRX CRXL HFX _.
    zstep.
    pose proof HCMPO as SPC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in SPC.
    eapply aevtM_cut_evt; [exact MK| |].
    { eapply SPC with (dX := dX4) (dY := dTs) (LB := LB4); rewrite ?unsigned_lit by lia.
      - left; exact MX.
      - right; exact OTs.
      - intros O. flat constr:((HFX O)) 2%nat. intros P0 _. exact P0.
      - unfold dTs; cbn [md_own]; intros C; discriminate C.
      - exact MI.
      - rewrite KA4, E0. first [reflexivity| f_equal; lia].
      - unfold dTs; cbn [md_addr]. first [reflexivity| f_equal; lia]. }
    clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO. flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x21508)) with (Z_to_bv 64 0x21508) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear CS4 MX NSX WRX LOX CRX CRXL HFX OTs.
    zstep; if_cases K1.
      * (* [comment removed for export] *)
        clear K1. eapply L_ltest; [exact K| exact CS5| exact ADDRS4| exact LL4| exact T0| exact IR| exact IB| exact NB| exact Hk].
      * (* [comment removed for export] *)
        clear K1. zstep. zstep. zstep.
        flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT3 CS5 eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
        flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS5 eq_refl)) 9%nat. intros MY NSY WRY LOY CRY CRYL HFY AY1 _.
        flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 3 1 dT3 dY CS5 eq_refl eq_refl)) 2%nat. intros SEP31 OPS31.
        pose proof HCOPY as SPC. unfold mpi_copy_stmt_x, U_MPI_COPY in SPC.
        eapply aevtM_cut.
        { eapply SPC with (dX := dT3) (dY := dY) (lo := lo) (h := h4) (LB := LB4); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
          all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
          all: try (rewrite ?KA3, ?KA, ?E0, ?E1, ?E2, ?E3; reflexivity).
          apply copy_sep_of_opnd; [exact OPS31| rewrite E1; clear - SLO HLS ACL ACP; lia]. }
        clear SPC. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
        binop_post PO m6 mo6 h6 LB6 dT6 r E MI6 ST6 MF6 HT6 HH6 MA6 OUT6 PX6 SOK6 RR.
        replace (ret_pc (Z_to_bv 64 0x21518)) with (Z_to_bv 64 0x21518) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        flat constr:(RR) 2%nat. flclear RR. intros FLt22 _. flat constr:(FLt22) 4%nat. flclear FLt22. intros CR1 KA6 KP6 KF6.
        assert (CS6 : CST m6 mo6 h6 LB6 (set_nth 3 [dX4; dY; dZ; dT3] dT6) dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 v164 v168 v176 t180)) []).
        { eapply mc_binop_l; [exact CS5| reflexivity| exact HH6| exact HT6| exact MF6| exact MA6| exact OUT6| exact PX6| exact SOK6| exact MI6| exact ST6| exact KF6]. }
        cbn [set_nth] in CS6.
        assert (ADDRS6 : locals_at [dX4; dY; dZ; dT6]) by (unfold locals_at; cbn [map]; rewrite KA6, KA4, KA3, KA, E0, E1, E2, E3; reflexivity).
        assert (KN6 : md_n dT3 <= md_n dT6) by (destruct CR1 as [(_ & _ & NB6)|(_ & EN & _)]; lia).
        assert (LL6 : loop_loc dX4 dY dZ dT6 n t zp) by (eapply loop_loc_T; [exact LL4| eapply out_heap; [exact MA6| exact (proj1 (proj2 OUT6))| pose proof LL4 as (_&_&_&_&_&_&_&_&NT4); lia]| exact KN6]).
        assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct CR1 as [(Hr0 & _)|(HrF & _)]; [left; exact Hr0| right; exact HrF]).
        clear MT NST WRT LOT CRT CRTL HFT MY NSY WRY LOY CRY CRYL HFY SEP31 OPS31 CR1 KF6 KP6 MA6 OUT6 PX6 CS5.
        reopen CS6 HH HTc MF SOK MI ST MK.
        zstep; if_cases K0; zify_cond K0.
        { eapply L_err; [exact CS6| exact ADDRS6| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB]. }
        assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT6 CS6 eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
        pose proof HSHL as SPS. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SPS.
        eapply aevtM_cut.
        { eapply SPS with (dX := dT6) (count := (i - t - 1) * 32) (lo := lo) (h := h6) (LB := LB6); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
          all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc IR T0 NB; lia).
          all: try (rewrite ?KA6, ?KA3, ?KA, ?E0, ?E1, ?E2, ?E3; reflexivity). }
        clear SPS. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
        binop_post PO m7 mo7 h7 LB7 dT7 r E MI7 ST7 MF7 HT7 HH7 MA7 OUT7 PX7 SOK7 RR.
        replace (ret_pc (Z_to_bv 64 0x21528)) with (Z_to_bv 64 0x21528) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        flat constr:(RR) 2%nat. flclear RR. intros R1 FLt23. flat constr:(FLt23) 4%nat. flclear FLt23. intros KA7 KP7 KF7 KN7.
        assert (CS7 : CST m7 mo7 h7 LB7 (set_nth 3 [dX4; dY; dZ; dT6] dT7) dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 v164 v168 v176 t180)) []).
        { eapply mc_binop_l; [exact CS6| reflexivity| exact HH7| exact HT7| exact MF7| exact MA7| exact OUT7| exact PX7| exact SOK7| exact MI7| exact ST7| exact KF7]. }
        cbn [set_nth] in CS7.
        assert (ADDRS7 : locals_at [dX4; dY; dZ; dT7]) by (unfold locals_at; cbn [map]; rewrite KA7, KA6, KA4, KA3, KA, E0, E1, E2, E3; reflexivity).
        assert (LL7 : loop_loc dX4 dY dZ dT7 n t zp) by (eapply loop_loc_T; [exact LL6| eapply out_heap; [exact MA7| exact (proj1 (proj2 OUT7))| pose proof LL6 as (_&_&_&_&_&_&_&_&NT6); lia]| exact KN7]).
        assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct R1 as [(Hr0 & _)|HrF]; [left; exact Hr0| right; exact HrF]).
        clear MT NST WRT LOT CRT CRTL HFT R1 KF7 KP7 MA7 OUT7 PX7 CS6 LL6 ADDRS6.
        reopen CS7 HH HTc MF SOK MI ST MK.
        zstep; if_cases K0; zify_cond K0.
        { eapply L_err; [exact CS7| exact ADDRS7| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB]. }
        assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX4 CS7 eq_refl)) 8%nat. intros MX NSX WRX LOX CRX CRXL HFX _.
        flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT7 CS7 eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
        flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0 0 dX4 dX4 CS7 eq_refl eq_refl)) 2%nat. intros SEP00 OPS00.
        flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0 3 dX4 dT7 CS7 eq_refl eq_refl)) 2%nat. intros SEP03 OPS03.
        pose proof (HAS 1 (or_introl eq_refl)) as SPA_.
        eapply aevtM_cut.
        { eapply SPA_ with (dX := dX4) (dA := dX4) (dB := dT7) (lo := lo) (h := h7) (LB := LB7); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
          all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
          all: try (rewrite ?KA7, ?KA6, ?KA4, ?KA3, ?KA, ?E0, ?E1, ?E2, ?E3; reflexivity). }
        clear SPA_. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
        binop_post PO m8 mo8 h8 LB8 dX8 r E MI8 ST8 MF8 HT8 HH8 MA8 OUT8 PX8 SOK8 RR.
        replace (ret_pc (Z_to_bv 64 0x21540)) with (Z_to_bv 64 0x21540) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        flat constr:(RR) 2%nat. flclear RR. intros R1 FLt24. flat constr:(FLt24) 4%nat. flclear FLt24. intros KA8 KP8 KF8 KN8.
        assert (CS8 : CST m8 mo8 h8 LB8 (set_nth 0 [dX4; dY; dZ; dT7] dX8) dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 v164 v168 v176 t180)) []).
        { eapply mc_binop_l; [exact CS7| reflexivity| exact HH8| exact HT8| exact MF8| exact MA8| exact OUT8| exact PX8| exact SOK8| exact MI8| exact ST8| exact KF8]. }
        cbn [set_nth] in CS8.
        assert (ADDRS8 : locals_at [dX8; dY; dZ; dT7]) by (unfold locals_at; cbn [map]; rewrite KA8, KA7, KA6, KA4, KA3, KA, E0, E1, E2, E3; reflexivity).
        assert (LL8 : loop_loc dX8 dY dZ dT7 n t zp) by (eapply loop_loc_X; [exact LL7| eapply out_heap; [exact MA8| exact (proj1 (proj2 OUT8))| pose proof LL7 as (_&NX7&_); lia]| exact KN8]).
        assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct R1 as [(Hr0 & _)|HrF]; [left; exact Hr0| right; exact HrF]).
        clear MX NSX WRX LOX CRX CRXL HFX MT NST WRT LOT CRT CRTL HFT SEP00 OPS00 SEP03 OPS03 R1 KF8 KP8 MA8 OUT8 PX8 CS7 LL7 ADDRS7.
        reopen CS8 HH HTc MF SOK MI ST MK.
        zstep; if_cases K0; zify_cond K0.
        { eapply L_err; [exact CS8| exact ADDRS8| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB]. }
        assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
        (* [comment removed for export] *)
        clear HLZ HNZ INZ PALZ HFZ PZ0 PZ4.
        flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS8 eq_refl)) 8%nat. intros FLt25 _ _ _ _ _ HFZ _. flat constr:(FLt25) 2%nat. flclear FLt25. intros FLt26 _. flat constr:(FLt26) 6%nat. flclear FLt26. intros _ _ _ HLZ HNZ HOZ.
        rewrite OZ in HOZ. flat constr:(HOZ) 4%nat. flclear HOZ. intros _ INZ PALZ UZ. flat constr:((HFZ OZ)) 3%nat. intros PZ0 PZ4 _. unfold MPI_MAX_LIMBS in HNZ. rewrite PZ in *.
        assert (ZB : 0 < zp /\ zp + 4 * (i - t - 1) < 2^64) by (clear - PZ0 PZ4 ACL SLO HLS SPB ACP IR NZ T0 HNZ HLZ; lia).
        zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - ZB IR T0; lia).
        { exfalso; clear - K0 ZB IR T0; lia. }
        rd UZ (i - t - 1).
        zstep.
        pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] m8) as MU. pose proof (wmono_refl usegs m8) as WM.
        pose proof (u32arr_store_ok usegs _ zp (md_limbs dZ) (i - t - 1) _ UZ ltac:(lia) ltac:(f_equal; lia)) as SOKw.
        zstep.
        lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] => pose proof (u32arr_write usegs _ zp (md_limbs dZ) (i - t - 1) v UZ ltac:(lia)) as UZ' end.
        store_done.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        lazymatch type of UZ' with u32arr _ _ _ ?l => set (zs9 := l) in UZ' end.
        assert (CS9 : CST m9 mo8 h8 LB8 [dX8; dY; set_limbs dZ zs9; dT7] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 v164 v168 v176 t180)) []).
        { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false); [exact CS8| exact MU| exact WM| assumption| assumption| | reflexivity| | | reflexivity| discriminate].
          - constructor; [right; left; exists 2%nat, dZ; split; [reflexivity|]; split; [reflexivity|]; split; [exact OZ|]; cbn [fst snd]; clear - IR HNZ NZ T0 PZ; rewrite ?PZ; lia| constructor].
          - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
              [ do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
              | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
              | | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
            cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OZ]|].
            intros _ _. rewrite PZ. split; [exact UZ'| subst zs9; rewrite upd_length; exact HLZ].
          - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
        eapply L_ltest; [exact K| exact CS9| | apply loop_loc_Z; exact LL8| exact T0| exact IR| exact IB| exact NB| exact Hk].
        unfold locals_at. cbn [map set_limbs md_addr]. unfold locals_at in ADDRS8. cbn [map] in ADDRS8. exact ADDRS8.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ISTATE (n t zp k : Z) (j0 j64 : list byte) (i q : Z) (moq : Model) (ms : machine_state) : Prop :=
    exists (mq : mem) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 wq : word)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 : word),
    ms = MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (zp + 4 * (i - t - 1))) x5 (Z_to_bv 64 (4 * t))
               (Z_to_bv 64 (4 * (i - t - 1))) (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) (Z_to_bv 64 (i - t - 1)) (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x213e4) fc None mq (seg_rom usegs) /\
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [] /\
    locals_at [dX; dY; dZ; dT] /\
    loop_loc dX dY dZ dT n t zp /\
    nth_error (md_limbs dZ) (Z.to_nat (i - t - 1)) = Some wq /\
    bv_unsigned wq mod 2^32 = q
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01M0@D12760851434.177D18696473121.177D25310437757.177D40375623405.177D4662108261.239 D49416158319.239D49532376974.177D55471390793.177D6690581324.239 L10642668194.173L10646928340.174L11254569813.17 L1167931669.177 L1167931669.234 L12610030783.239L12734415834.10 L13072597906.236L13085246180.237L13379996207.4  L13669996297.187L13672109588.216L14678034333.238L14678034333.239L15320268189.209L15795404733.238L16075584073.231L18743961128.4  L18964789310.235L18964789310.239L18964789560.238L18964789560.239L19901862207.239L21175695246.17 L21917923060.174L21923753204.173L24897143244.3  L25622449825.175L25622449825.176L25622450087.177L25736628564.3  L25820589127.177L26305953715.171L28138824896.2  L29010565666.206L31287002149.177L31583138353.3  L33517354533.3  L36436032575.7  L36950940679.2  L36955116083.2  L38076755263.239L39188636933.0  L41480287244.175L41633390655.239L42258615265.177L42468655062.187L42816481324.173L42816481578.176L42816481578.177L45093811327.239L4586513446.175 L46452486793.7  L48576203280.216L48770266301.3  L50982283959.232L52064948629.238L53382726745.238L53749517607.21 L56625524356.177L56996506657.17 L57179347148.18 L582101260.9    L58501596249.2  L59308548964.7  L59308628179.209L59314841581.174L59314955108.2  L59314955108.238L59314955108.7  L62335543678.0  L62867946550.233L62867946800.238L62867946800.239L63561631872.177L63891989021.238L64032823942.176L64032823942.177L64032824192.174L7411612811.177 L7411613069.174 L7411613069.176 L9377572398.18  L9746144436.239 00000100A00S01001101h01i02D03503Q03m04H04d05D06P06f07a08\08k09_0:S0:T0:U0;@0;A0;B0;Q0<B0=30=T0>50?A0?N0?j0@F0@N0@b0A60AL0AV0AW0Ad0Am0An0B`0Bj0C30CC0CD0CE0DQ0DR0Dd0F00F`0G30G\0HE0I10J=0JJ0Jc0K60K?0KV0L50LT0LU0LV0M70M80MO0MV0Mi0NQ0O40O:0OX0Oj0Ok0Q70RC0SO0SP0Sl0TX0UF0V20VF0VW0Vh0Vi0VjFS2sp2dY2dT2wq2v1S2sp2dY2dT2wq2v11wS2sp2dY2dT2wq2v13SPB1w2NT3PT0FS2sp1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ0FS2sp2dY2dT2wq2v13SPB2NT3PT0S2sp1n1t2zp1i2dY2dZ2dT2wq2IR3SPB3PT03dT54PT503PZ0S2sp2dY2dT2wq3SPB2NT3HLT3PT0S2sp2dY2dT2wq3SPB2NT3HLT3PT0S1L2HI2sp1h4HTOP2hq3SPB3HTcS2sp1n1t2zp1i2dY2dZ2dT2wq2IRS2sp1n1t2zp1i2dY2dZ2dT2wq2IR3dT5S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ03PZ4S1n1t2zp2T01i2dZ2IR2NZS2sp1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503HLZ3PZ0S2sp1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503HLZ3PZ0S2dY2dT2NT4APTYS1L3HLS2sp2lo3SLO3ACL2zp2dY2dZ2dT2wq3SPB3ACP3PT03PZ0S1L3HLS2sp2lo3SLO3ACL2zp2dY2dZ2dT2wq3SPB3ACP3PT03PZ0FFS2sp2zp2dY2dZ2dT2wq3SPB3PT03ts43PZ01r2Hr2K0FFS2dT2NT3dT53KN5S2sp1n1t2zp1i2dY2dZ2dT2wq2IR3SPB3PT03dT54PT503PZ0S2sp1n1t2zp1i2dY2dZ2dT2wq2IR3SPB3PT03dT54PT503PZ0S2sp1t2zp1i2dY2dZ2dT2wq3dT55Ha_stS2sp1t2zp1i2dY2dZ2dT2wq3dT55Ha_stS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ03PZ4S1L2sp2lo3SLOS2sp2dY2dT2wq3SPB2NT3HLT3PT0S2sp2dY2dT2wq3SPB2NT3HLT3PT0S3dT52spS2sp2dY2dT2wq2v13PT0S2sp2dY2dT2wq2v13PT0S2sp2dY2dT2wq2v11w3PT0S3dT54VAL5FS2sp2dY2dT2wqS3dT53NT5FS1L3HLS2sp2lo3SLO3ACL2dY2dT2wq2v13SPB1w2NT3PT03PT4S3dT51x2HxS2sp1x2HxS2u02u12u22K02LRSSS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ03PZ4SS2sp1t2T02dY2dT2wqS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ03PZ4S1L3HLS2sp2lo3SLO3ACL2dY2dT2wq2v13SPB2NT3PT03PT4S2sp2zp2dY2dZ2dT2wqS1L3HLS2sp2lo3SLO3ACL2dY2dT2wq3SPB2NT3PT4S1L3HLS2sp2lo3SLO3ACL2dY2dT2wq3SPB2NT3PT4S1L3HLS2sp2lo3SLO3ACL2dY2dT2wq2v13SPB2NT3PT4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ03PZ4S2sp2dY2dT2wqS1L3HLS2sp2lo3SLO3ACL3ACPS2sp2zp2dY2dZ2dT2wqS1q2QB2n0S2sp2zp2dY2dZ2dT2wq3dT5S2sp2zp1q2dY2dZ2dT2wq3dT51H3SZ1S2sp2zp1q2dY2dZ2dT2wq2QB3dT52Q1FFS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPFS1n1t2T01i2dZ2IR2NZ3HLZS2dT2NTS2u02u12u22K02K22LRS2sp2zp2dY2dZ2dT2wq3SPB3PT03PZ01r3HrF2K0S2sp1t2T02dY2dT2wq3SPB2NY3HLY3PT01NS2sp1ES2sp2zp1q2dY2dZ2dT2wq3dT52Q11ES2u02u12u22K02LR1ESS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T01i2dY2dZ2dT2wq2IR3SPB2NZ3PT03dT54PT503PZ03PZ4FS2sp2zp1q2dY2dZ2dT2wq2QB3dT5S1L3HLS2sp2lo3SLO3ACL2dY2dT2wq2v13SPB2NT3PT4S1L3HLS2sp2lo3SLO3ACL2dY2dT2wq2v13SPB1w2NT3PT4S1L3HLS2sp2lo3SLO3ACL2dY2dT2wq2v13SPB2NT3PT4S2sp2dY2dT2wq2v13PT0S2sp2dY2dT2wq3PT0S2sp2dY2dT2wq3PT0FF". (* [comment removed for export] *)
  Lemma L_inner_tail : forall (n t zp k ib : Z) (j0 j64 : list byte), KONT n t zp k ib j0 j64 ->
    0 <= t -> n <= 10000 -> 0 <= k < 2^64 ->
    forall (i q : Z) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word) (wq : word)
      (xra t0 t1 t2 a0 v1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 : word),
    (1 <= q -> forall (moq' : Model) (ms' : machine_state), ISTATE n t zp k j0 j64 i (q - 1) moq' ms' -> aevtM usegs moq' POST ms') ->
    t < i <= n -> i <= ib + 1 -> 0 <= q < 2^32 ->
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    nth_error (md_limbs dZ) (Z.to_nat (i - t - 1)) = Some wq ->
    bv_unsigned wq mod 2^32 = q ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 v1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (zp + 4 * (i - t - 1))) x5 (Z_to_bv 64 (4 * t))
               (Z_to_bv 64 (4 * (i - t - 1))) (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) (Z_to_bv 64 (i - t - 1)) (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x21434) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros n t zp k ib j0 j64 K T0 NB Hk. intros until x5. intros KI IR IB QB CS_ ADDRS LL ZQ QV.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST _ MK.
    flat constr:(LL) 10%nat. intros OX NXl OY NY OZ PZ NZ OT NT VB.
    flat constr:((struct_cells _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 2%nat. intros CT _. rewrite E3 in CT. unfold mpi_cells in CT.
    flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 2%nat. intros CY _. rewrite E1 in CY. unfold mpi_cells in CY.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 8%nat. intros FLt27 _ _ _ _ _ HFY _. flat constr:(FLt27) 2%nat. flclear FLt27. intros FLt28 _. flat constr:(FLt28) 6%nat. flclear FLt28. intros _ _ _ HLY HNY HOY.
    rewrite OY in HOY. flat constr:(HOY) 4%nat. flclear HOY. intros _ _ PALY UY. flat constr:((HFY OY)) 3%nat. intros PY0 PY4 _. unfold MPI_MAX_LIMBS in HNY.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 8%nat. intros FLt29 _ _ _ _ _ HFT _. flat constr:(FLt29) 2%nat. flclear FLt29. intros FLt30 _. flat constr:(FLt30) 6%nat. flclear FLt30. intros _ _ _ HLT HNT HOT.
    rewrite OT in HOT. flat constr:(HOT) 4%nat. flclear HOT. intros _ INT PALT UT. flat constr:((HFT OT)) 3%nat. intros PT0 PT4 _. unfold MPI_MAX_LIMBS in HNT.
    flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 3 1 dT dY CS_ eq_refl eq_refl)) 2%nat. intros _ FLt31. flat constr:(FLt31) 4%nat. flclear FLt31. intros _ _ SEPTY _.
    assert (APTY : md_p dT + 4 * md_n dT <= md_p dY \/ md_p dY + 4 * md_n dY <= md_p dT).
    { destruct SEPTY as [E|[E|[E|E]]]; [exfalso; apply (f_equal md_addr) in E; rewrite E3, E1 in E; clear - E; lia| exfalso; exact (E OT)| exfalso; rewrite OY in E; discriminate| exact E]. }
    clear SEPTY. pose proof (conj UY I) as UYc. clear UY.
    assert (BT : 0 < md_p dT /\ md_p dT + 4 * md_n dT <= SP - 512) by (clear - PT0 PT4 ACL SLO HLS; lia).
    assert (BY : 0 < md_p dY /\ md_p dY + 4 * md_n dY <= SP - 512) by (clear - PY0 PY4 ACL SLO HLS; lia).
    zstep.
    zstep; if_cases KC0; zify_cond KC0; [first [exfalso; clear - KC0 BT BY NT NY T0 SPB PALT PALY; lxu_contra | clear - KC0 BT BY NT NY T0 SPB PALT PALY; lxu_pnull KC0]|].
    zstep. zstep; if_cases KC1; zify_cond KC1; [first [exfalso; clear - KC1 BT BY NT NY T0 SPB PALT PALY; lxu_contra | clear - KC1 BT BY NT NY T0 SPB PALT PALY; lxu_pnull KC1]|].
    pose proof (munch_refl [(md_p dT, md_p dT + 8)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    pose proof (u32arr_store_ok usegs _ (md_p dT) (md_limbs dT) 0 _ UT ltac:(lia) ltac:(f_equal; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] => pose proof (u32arr_write usegs _ (md_p dT) (md_limbs dT) 0 v UT ltac:(lia)) as UT1 end.
    rewrite Z.mul_0_r in UT1.
    store_done. try clear UT; try clear SOKw.
    flat constr:(UYc) 2%nat. flclear UYc. intros UY _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      apply (fun H => u32arr_transport usegs _ mq mx _ _ H MU WM) in UY; [| cbn; split; [rewrite HLY; clear - APTY NT; lia| exact I]] end.
    zstep. zstep.
    zstep; if_cases KC2; zify_cond KC2; [first [exfalso; clear - KC2 BT BY NT NY T0 SPB PALT PALY; lxu_contra | clear - KC2 BT BY NT NY T0 SPB PALT PALY; lxu_pnull KC2]|].
    zstep. zstep. zstep. zstep; if_cases KC3; zify_cond KC3; [first [clear - KC3 BT BY NT NY T0 SPB PALT PALY; lxu_pnull KC3 | exfalso; clear - KC3 BT BY NT NY T0 SPB PALT PALY; lxu_contra]|].
    zstep; if_cases KC4; zify_cond KC4; [first [exfalso; clear - KC4 BT BY NT NY T0 SPB PALT PALY; lxu_contra | clear - KC4 BT BY NT NY T0 SPB PALT PALY; lxu_pnull KC4]|].
    zstep. zstep; if_cases KC5; zify_cond KC5; [first [exfalso; clear - KC5 BT BY NT NY T0 SPB PALT PALY; lxu_contra | clear - KC5 BT BY NT NY T0 SPB PALT PALY; lxu_pnull KC5]|].
    zstep. zstep; if_cases KC6; zify_cond KC6; [first [exfalso; clear - KC6 BT BY NT NY T0 SPB PALT PALY; lxu_contra | clear - KC6 BT BY NT NY T0 SPB PALT PALY; lxu_pnull KC6]|].
    zstep; if_cases KC7; zify_cond KC7; [first [exfalso; clear - KC7 BT BY NT NY T0 SPB PALT PALY; lxu_contra | clear - KC7 BT BY NT NY T0 SPB PALT PALY; lxu_pnull KC7]|].
    rd UY t. clear UY.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch type of UT1 with u32arr _ _ _ ?l => pose proof (u32arr_store_ok usegs m3 (md_p dT) l 1 _ UT1 ltac:(rewrite upd_length; lia) ltac:(f_equal; lia)) as SOKw end.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      lazymatch type of UT1 with u32arr _ _ _ ?l => pose proof (u32arr_write usegs m3 (md_p dT) l 1 v UT1 ltac:(rewrite upd_length; lia)) as UT2 end end.
    rewrite Z.mul_1_r in UT2.
    store_done. try clear UT1; try clear SOKw.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    lazymatch type of UT2 with u32arr _ _ _ ?l => set (ts4 := l) in UT2 end.
    assert (CS4 : CST m4 moq hq LBq [dX; dY; dZ; set_limbs dT ts4] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 3%nat) false false); [exact CS_| exact MU| exact WM| assumption| assumption| | reflexivity| | | reflexivity| discriminate].
      - constructor; [right; left; exists 3%nat, dT; split; [reflexivity|]; split; [reflexivity|]; split; [exact OT|]; cbn [fst snd]; clear - NT; lia| constructor].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          [ do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C] |].
        cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OT]|].
        intros _ _. split; [exact UT2| subst ts4; rewrite !upd_length; exact HLT].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
    assert (ADDRS4 : locals_at [dX; dY; dZ; set_limbs dT ts4]) by (unfold locals_at; cbn [map set_limbs md_addr]; rewrite E0, E1, E2, E3; reflexivity).
    assert (LL4 : loop_loc dX dY dZ (set_limbs dT ts4) n t zp) by (pose proof LL as (B1&B2&B3&B4&B5&B6&B7&B8&B9); repeat (split; [assumption|]); cbn; auto).
    clear MU WM UT2 CS_ LL ADDRS HFY HFT. try clear CT. try clear CY.
    reopen CS4 HH HTc MF SOK MI ST MK.
    (* [comment removed for export] *)
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS4 eq_refl)) 8%nat. intros FLt32 _ _ _ _ _ HFZ _. flat constr:(FLt32) 2%nat. flclear FLt32. intros FLt33 _. flat constr:(FLt33) 6%nat. flclear FLt33. intros _ _ _ HLZ HNZ HOZ.
    rewrite OZ in HOZ. flat constr:(HOZ) 4%nat. flclear HOZ. intros _ INZ PALZ UZ. flat constr:((HFZ OZ)) 3%nat. intros PZ0 PZ4 _. unfold MPI_MAX_LIMBS in HNZ. rewrite PZ in *.
    rdq UZ ZQ (i - t - 1).
    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 _ CS4 eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
    flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 3 3 _ _ CS4 eq_refl eq_refl)) 2%nat. intros SEP33 OPS33.
    pose proof HMULI as SPM. unfold mpi_mul_int_stmt_g, U_MPI_MUL_INT in SPM.
    eapply aevtM_cut.
    { eapply SPM with (dX := set_limbs dT ts4) (dA := set_limbs dT ts4) (b := q) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc QB; lia).
      all: try (cbn [set_limbs md_addr]; rewrite ?E0, ?E1, ?E2, ?E3; reflexivity).
      - rewrite bv_unsigned_sx32, sxz_mod32 by (apply Z.mod_pos_bound; lia). exact QV.
      - rewrite bv_unsigned_sx32, sxz_zero_iff by (apply Z.mod_pos_bound; lia). rewrite QV. tauto. }
    clear SPM. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m5 mo5 h5 LB5 dT5 r E MI5 ST5 MF5 HT5 HH5 MA5 OUT5 PX5 SOK5 RR.
    replace (ret_pc (Z_to_bv 64 0x21494)) with (Z_to_bv 64 0x21494) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros R1 FLt34. flat constr:(FLt34) 4%nat. flclear FLt34. intros KA5 KP5 KF5 KN5. cbn [set_limbs md_addr md_pad md_n] in KA5, KP5, KN5.
    assert (CS5 : CST m5 mo5 h5 LB5 (set_nth 3 [dX; dY; dZ; set_limbs dT ts4] dT5) dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_l; [exact CS4| reflexivity| exact HH5| exact HT5| exact MF5| exact MA5| exact OUT5| exact PX5| exact SOK5| exact MI5| exact ST5| exact KF5]. }
    cbn [set_nth] in CS5.
    assert (ADDRS5 : locals_at [dX; dY; dZ; dT5]) by (unfold locals_at; cbn [map]; rewrite KA5, E0, E1, E2, E3; reflexivity).
    assert (OT5 : md_own dT5 = LHeap) by (eapply out_heap; [exact MA5| exact (proj1 (proj2 OUT5))| clear - KN5 NT; lia]).
    assert (LL5 : loop_loc dX dY dZ dT5 n t zp) by (eapply loop_loc_T; [exact LL4| exact OT5| cbn; exact KN5]).
    assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct R1 as [(Hr0 & _)|HrF]; [left; exact Hr0| right; exact HrF]).
    clear MT NST WRT LOT CRT CRTL HFT SEP33 OPS33 KF5 KP5 OUT5 PX5 UZ CS4 LL4 ADDRS4.
    reopen CS5 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    { eapply L_err; [exact CS5| exact ADDRS5| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB]. }
    destruct R1 as [(Hr0 & VAL5 & _)|HrF]; [| exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in *; lia]. subst r. clear Hr K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    flat constr:((struct_cells _ _ _ _ _ _ _ 3 dT5 CS5 eq_refl)) 5%nat. intros CT5 SGT5 NT5 _ _. rewrite KA5, E3 in CT5. unfold mpi_cells in CT5. unfold MPI_MAX_LIMBS in NT5.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT5 CS5 eq_refl)) 8%nat. intros FLt35 _ _ _ _ _ HFT5 _. flat constr:(FLt35) 2%nat. flclear FLt35. intros FLt36 _. flat constr:(FLt36) 6%nat. flclear FLt36. intros _ _ _ HLT5 _ HOT5. rewrite OT5 in HOT5. flat constr:(HOT5) 4%nat. flclear HOT5. intros _ _ PALT5 UT5.
    flat constr:((HFT5 OT5)) 3%nat. intros PT50 PT54 _.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS5)) 5%nat. intros CH0 CH1 CH2 CHT CHR. unfold t2cells in CH2.
    eapply aevtM_cut_evt; [exact MK| |].
    { eapply u_cmp_mpi with (sp := SPF) (m := m5) (X := SP + -192) (P := md_p dT5) (n := md_n dT5) (sg := md_sg dT5) (xs := md_limbs dT5) (pad := md_pad dT5)
                (Y := SP + -208) (Q := SP + -220) (n' := 3) (sg' := 1) (ys := [u0; u1; u2]) (pad' := j68).
      all: first [ exact CT5 | exact (proj1 UT5) | exact HLT5 | exact SGT5 | exact CH2 | exact (proj2 (proj1 CH1)) | exact MI | reflexivity | (left; reflexivity)
                 | (clear - NT5 PT50 PT54 PALT5 SPA SPB SLO HLS ACL ACP; lia) ]. }
    cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO. flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x214a4)) with (Z_to_bv 64 0x214a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep; if_cases K1; zify_cond K1.
    2: { (* [comment removed for export] *)
         eapply L_bodyB; [exact K| exact T0| exact NB| exact Hk| exact CS5| exact ADDRS5| exact LL5| exact IR| exact IB]. }
    (* [comment removed for export] *)
    assert (Q1 : 1 <= q).
    { destruct (Z.eq_dec q 0) as [Q0|]; [exfalso| clear - QB n0; lia]. rewrite Q0, Z.mul_0_r in VAL5.
      assert (LV0 : lval (md_limbs dT5) (md_n dT5) = 0).
      { rewrite <- (mpd_abs_lval dT5 HLT5). unfold mpd_val in VAL5. unfold mpd_abs. clear - VAL5 SGT5. destruct SGT5 as [E|E]; rewrite E in VAL5; lia. }
      pose proof (lval_range [u0; u1; u2] 3 ltac:(clear; lia)) as LR.
      match goal with Ka : 0 < Z.sgn ?e mod _, Kb : Z.sgn ?e2 mod _ < _ |- _ =>
        rewrite LV0, Z.mul_0_r, Z.mul_1_l, Z.sub_0_l in Ka, Kb; clear - Ka Kb LR;
        destruct (Z.eq_dec (lval [u0; u1; u2] 3) 0) as [E|NE];
        [ rewrite E in Ka; cbn in Ka; lia
        | rewrite (Z.sgn_neg (- lval [u0; u1; u2] 3)) in Kb by lia; cbn in Kb; lia ] end. }
    repeat match goal with Ka : context [Z.sgn _ mod _] |- _ => clear Ka end.
    (* [comment removed for export] *)
    clear HLZ HNZ INZ PALZ PZ0 PZ4 HFZ.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS5 eq_refl)) 8%nat. intros FLt37 _ _ _ _ _ HFZ _. flat constr:(FLt37) 2%nat. flclear FLt37. intros FLt38 _. flat constr:(FLt38) 6%nat. flclear FLt38. intros _ _ _ HLZ HNZ HOZ.
    rewrite OZ in HOZ. flat constr:(HOZ) 4%nat. flclear HOZ. intros _ INZ PALZ UZ. flat constr:((HFZ OZ)) 3%nat. intros PZ0 PZ4 _. unfold MPI_MAX_LIMBS in HNZ. rewrite PZ in *.
    rdq UZ ZQ (i - t - 1).
    zstep.
    pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    pose proof (u32arr_store_ok usegs _ zp (md_limbs dZ) (i - t - 1) _ UZ ltac:(lia) ltac:(f_equal; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] => pose proof (u32arr_write usegs _ zp (md_limbs dZ) (i - t - 1) v UZ ltac:(lia)) as UZ' end.
    store_done.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    lazymatch type of UZ' with u32arr _ _ _ (upd _ _ ?v) => set (wq6 := v) in UZ'; set (zs6 := upd (md_limbs dZ) (Z.to_nat (i - t - 1)) wq6) in UZ' end.
    assert (CS6 : CST m6 mo5 h5 LB5 [dX; dY; set_limbs dZ zs6; dT5] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false); [exact CS5| exact MU| exact WM| assumption| assumption| | reflexivity| | | reflexivity| discriminate].
      - constructor; [right; left; exists 2%nat, dZ; split; [reflexivity|]; split; [reflexivity|]; split; [exact OZ|]; cbn [fst snd]; clear - IR HNZ NZ T0 PZ; rewrite ?PZ; lia| constructor].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          [ do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
        cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OZ]|].
        intros _ _. rewrite PZ. split; [exact UZ'| subst zs6; rewrite upd_length; exact HLZ].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
    eapply (KI Q1). unfold ISTATE.
    exists m6, h5, LB5, dX, dY, (set_limbs dZ zs6), dT5, u0, u1, u2, j68, t160, t164, t168, t176, t180, wq6. do 17 eexists.
    split; [reflexivity|]. split; [exact CS6|].
    split; [unfold locals_at; cbn [map set_limbs md_addr]; rewrite KA5, E0, E1, E2, E3; reflexivity|].
    split; [apply loop_loc_Z; exact LL5|].
    split; [cbn [set_limbs md_limbs]; subst zs6; rewrite nth_error_upd_same by (clear - HLZ HNZ NZ IR T0; lia); reflexivity|].
    subst wq6. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite bv_unsigned_sx32, QV.
    pose proof (sxz_range q QB). assert (SZ1 : sxz q <> 0) by (intros E; apply (proj1 (sxz_zero_iff q QB)) in E; lia).
    rewrite (Z.mod_small (sxz q + -1) (2^64)) by lia. rewrite sxz_add_mod32 by lia. apply Z.mod_small. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L11254569813.15 L13669996298.164L13672109588.193L15320243423.187L16811472528.193L29010565666.185L31733759171.200L36635087953.198L41415943117.198L41811025339.189L46302493051.16 L48225252573.202L50764594099.198L56996506657.15 L5775657213.198 L59308628179.186L59314841581.199L61282542167.189L61486577697.15 L6700308622.15  00000K00k01K01d01k01l02>02m03703D03E03Q03[04<04k05>05Z06006406AS1L2HI2sp1h4HTOP2hq3SPB3HTcS1L3HLS2sp2lo3SLO3ACL2wq3SPB3ACPS1L3HLS2sp2lo3SLO3ACL2wq3SPB3ACPS2sp2dT2wq3SPB2NT1r2K02HrS2sp2wqFS2sp1t2T02dY2wq2K1S1L3HLS2sp2lo3SLO3ACL1t2T02dY2wq3SPB2NY3PY03PY4S2sp2dY2wqS2sp2dT2wq2NTFS2sp1t2dY2wqS2sp2dY2wqS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2sp2lo3SLO3ACL1t2T02dY2wq3SPB2NY3PY03PY4S2sp2wq3SPB1r2Hr2K0S2sp1t2T02dY2wq3SPB2NY3HLY1NS2sp2dT2wq3SPB3dT23NT2S2spS1L2sp2lo3SLO". (* [comment removed for export] *)
  Lemma L_inner_body : forall (n t zp k ib : Z) (j0 j64 : list byte), KONT n t zp k ib j0 j64 ->
    0 <= t -> n <= 10000 -> 0 <= k < 2^64 ->
    forall (i q : Z) (moq : Model) (ms : machine_state),
    (1 <= q -> forall (moq' : Model) (ms' : machine_state), ISTATE n t zp k j0 j64 i (q - 1) moq' ms' -> aevtM usegs moq' POST ms') ->
    t < i <= n -> i <= ib + 1 -> 0 <= q < 2^32 ->
    ISTATE n t zp k j0 j64 i q moq ms -> aevtM usegs moq POST ms
(* [comment removed for export] *).
  Proof.
    intros n t zp k ib j0 j64 K T0 NB Hk i q moq ms KI IR IB QB IS.
    unfold ISTATE in IS. destruct IS as (mq & hq & LBq & dX & dY & dZ & dT & u0 & u1 & u2 & j68 & t160 & t164 & t168 & t176 & t180 & wq & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x5 & -> & CS_ & ADDRS & LL & ZQ & QV).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST _ MK.
    flat constr:(LL) 10%nat. intros OX NXl OY NY OZ PZ NZ OT NT VB.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
    pose proof HLSET as SPL. unfold mpi_lset_stmt, U_MPI_LSET in SPL.
    eapply aevtM_cut.
    { eapply SPL with (dX := dT) (z := 0) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?E0, ?E1, ?E2, ?E3; reflexivity). }
    clear SPL. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dT2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
    replace (ret_pc (Z_to_bv 64 0x213f0)) with (Z_to_bv 64 0x213f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 3%nat. flclear RR. intros R1 KA KF.
    assert (CS2 : CST m2 mo2 h2 LB2 (set_nth 3 [dX; dY; dZ; dT] dT2) dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_l; [exact CS_| reflexivity| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact KF]. }
    cbn [set_nth] in CS2.
    assert (ADDRS2 : locals_at [dX; dY; dZ; dT2]) by (unfold locals_at; cbn [map]; rewrite KA, E0, E1, E2, E3; reflexivity).
    clear MT NST WRT LOT CRT CRTL HFT KF MA2 OUT2 PX2 CS_.
    reopen CS2 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    { assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct R1 as [(Hr0 & _)|(HrF & _)]; [left; exact Hr0| right; exact HrF]).
      eapply L_err; [exact CS2| exact ADDRS2| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| exact VB]. }
    destruct R1 as [(Hr0 & NT2 & OT2 & [w0 LT2] & SGT2 & PDT2)|(Hr & _)]; [| exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia].
    subst r. clear K0. rewrite Z.max_l in NT2 by lia. cbn in SGT2.
    assert (LL2 : loop_loc dX dY dZ dT2 n t zp) by (eapply loop_loc_T; [exact LL| exact OT2| lia]).
    (* [comment removed for export] *)
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS2)) 5%nat. intros CH0 CH1 CH2 CHT CHR.
    flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS2 eq_refl)) 2%nat. intros CY _. rewrite E1 in CY. unfold mpi_cells in CY.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS2 eq_refl)) 8%nat. intros FLt39 _ _ _ _ _ HFY _. flat constr:(FLt39) 2%nat. flclear FLt39. intros FLt40 _. flat constr:(FLt40) 6%nat. flclear FLt40. intros _ _ _ HLY HNY HOY.
    rewrite OY in HOY. flat constr:(HOY) 4%nat. flclear HOY. intros _ _ PALY UY. flat constr:((HFY OY)) 3%nat. intros PY0 PY4 _. unfold MPI_MAX_LIMBS in HNY.
    zstep.
    zstep; if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - zstep. eapply L_inner_tail; try eassumption.
    - zstep. zstep. zstep.
      zstep; if_cases K2; zify_cond K2; [exfalso; clear - K1 K2 T0 IR NY HNY HLY PY0 PY4 SPB; rewrite ?Z.mod_small in K2 by lia; lia|].
      zstep. zstep. zstep. zstep; if_cases K3; zify_cond K3; [clear - K1 K3 T0 IR NY HNY HLY PY0 PY4 SPB; rewrite ?Z.mod_small in K3 by lia; lxu_pnull K3|].
      zstep; if_cases K4; zify_cond K4; [exfalso; clear - K4 PY0; lia|].
      zstep. zstep; if_cases K5; zify_cond K5;
        [exfalso; clear - K1 K5 PALY T0 IR NY HNY HLY PY0 PY4 SPB; rewrite ?Z.mod_small in K5 by lia; rewrite land_3_mod in K5; Z.div_mod_to_equations; lia|].
      rd UY (t - 1). zstep. eapply L_inner_tail; try eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L13940681623.2  L18988169999.0  L51907728244.2  L59308988752.1  L65403326661.10400000700800?00C00MS1N3NB2SS1N3NB2S2Q1S2sp1N3NB2". (* [comment removed for export] *)
  Lemma L_inner : forall (n t zp k ib : Z) (j0 j64 : list byte), KONT n t zp k ib j0 j64 ->
    0 <= t -> n <= 10000 -> 0 <= k < 2^64 ->
    forall (i : Z), t < i <= n -> i <= ib + 1 ->
    forall (N : nat) (moq : Model) (ms : machine_state), Z.of_nat N < 2^32 ->
    ISTATE n t zp k j0 j64 i (Z.of_nat N) moq ms -> aevtM usegs moq POST ms
(* [comment removed for export] *).
  Proof.
    intros n t zp k ib j0 j64 K T0 NB Hk i IR IB.
    induction N as [|N IH]; intros moq ms NB2 IS.
    - eapply (L_inner_body n t zp k ib j0 j64 K T0 NB Hk i (Z.of_nat 0)); [| exact IR| exact IB| clear; lia| exact IS]. intros Q1. exfalso. clear - Q1. lia.
    - eapply (L_inner_body n t zp k ib j0 j64 K T0 NB Hk i (Z.of_nat (S N))); [| exact IR| exact IB| clear - NB2; lia| exact IS].
      intros _ moq' ms' IS'. apply IH; [clear - NB2; lia|]. replace (Z.of_nat N) with (Z.of_nat (S N) - 1) by lia. exact IS'.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18932255420.78000004S2sp". (* [comment removed for export] *)
  Lemma zbv_add_modulus : forall x, Z_to_bv 64 (18446744073709551616 + x) = Z_to_bv 64 x.
  Proof.
    intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
    rewrite Z.add_comm. rewrite <- (Z.add_mod_idemp_r x 18446744073709551616) by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L11607865080.81L19628531477.81L22247875945.82L24790691890.82L31485502988.81L38717662456.81L38717875063.82L52067520956.83L56611640190.83L56611825236.83L56611825865.81L59178176444.83L59308660947.83L65444513020.8300000400@00N00Z00a00h00l01>01K01X01e01o02<02CS2spS2sp2q01R2NES2sp2q02HB1E1HS2sp2q02HB1ES2sp2q0S2sp2q0S2spS2sp2q02HB2NE1R2NZS2sp2q02HB2NES2sp2q02HB2NES2sp2q02HB2NES2sp2q02HBS2sp2q02HB2E0S2sp2q0". (* [comment removed for export] *)
  Lemma q_roundtrip : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pq0,$0.P,(31.(1=.=R1.)(32.R1.(33.+2.+20.)))(2.$0.(23.(23.(1>.(6<.(23.(23.(1>.(6<.R2.)+1.)(33.+2.+40.))(33.+2.+20.)))-1.)(33.+2.+40.))(33.+2.+20.))R2.)")
(* [comment removed for export] *).
  Proof.
    intros q0 HB.
    assert (S1 : ((sxz q0 + 1) mod 2^64) mod 2^32 = (q0 + 1) mod 2^32).
    { pose proof (sxz_range q0 HB) as R. destruct (Z.eq_dec (sxz q0 + 1) (2^64)) as [E|NE].
      - rewrite E, Z.mod_same, Z.mod_0_l by lia. unfold sxz in E. destruct (Z.ltb_spec q0 (2^31)); [lia|].
        replace (q0 + 1) with (2^32) by lia. rewrite Z.mod_same by lia. reflexivity.
      - rewrite (Z.mod_small (sxz q0 + 1)) by lia. apply sxz_add_mod32. exact HB. }
    rewrite S1. destruct (Z.eq_dec q0 (2^32 - 1)) as [E|NE].
    - rewrite E. replace (2^32 - 1 + 1) with (2^32) by lia. rewrite Z.mod_same by lia. unfold sxz. cbn. reflexivity.
    - rewrite (Z.mod_small (q0 + 1)) by lia. pose proof (sxz_range (q0 + 1) ltac:(lia)) as R.
      assert (NZ : sxz (q0 + 1) <> 0) by (intros E0; apply (proj1 (sxz_zero_iff (q0 + 1) ltac:(lia))) in E0; lia).
      rewrite (Z.mod_small (sxz (q0 + 1) + -1)) by lia. rewrite sxz_add_mod32 by lia. rewrite Z.mod_small; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0190@D25171652884.174D25171652884.176D25171652884.177D4662108261.181 D4662108261.182 D49416158319.181D49416158319.182D5236058786.176 D5236058786.177 D66033346937.174D6690581324.181 D6690581324.182 L10357916367.175L1168096659.178 L1170011054.178 L12610030783.183L12734415834.10 L13070716335.178L13072597906.178L13085246180.179L14678034333.181L17483385982.182L18964789310.178L18964789310.180L18964789310.181L18964789560.181L18964789560.182L19629204642.174L19895056584.176L1997256195.172 L21335385048.175L21494960896.177L21566755998.177L25371483764.175L36692683780.174L36692683780.176L36692683780.177L38076755263.183L39170170779.183L41252081172.174L41416270414.174L41633390655.183L42468392300.181L42602196847.176L42602196847.177L43027500658.183L44622288685.174L44622288685.176L44622288685.177L45093811327.183L45820422963.172L49698585326.174L49698585326.176L49698585326.177L50616252568.174L51654213621.2  L582101260.9    L59314841581.173L59314841581.174L59326299102.177L61586660054.174L62867946550.178L62867946550.180L62867946800.181L62867946800.182L64424857615.3  L8161461422.174 L8161461422.176 L8161461422.177 L8929197312.6   L9002935640.175 L9563480628.174 L9746144436.183 00000n01k02i02j02k03V04A05806006h07M08208W08m09C0:C0:Y0;E0<10<]0<^0<_0=A0=f0>K0>e0??0@<0@K0@X0@e0A40AA0AN0BR0CU0DY0EY0En0FS0F`0G`0Gm0HK0Hj0I?0J?0K>0L>0M>0MK0Mn0NP0O30O@0OE0O\0PK0Q:0QG0Qf0Rc0Sc0Tc0Uc0Uk0Vo0X20Y60YF0YS0Y`0YaS1L2HI2sp1h4HTOP2zp2hq2dX2dZ2v03SPB3HTc3PX03PZ02HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2zp2hq2dX2dZ3SPB3HTc1w3PX03PZ02HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2zp2hq2dX2dZ3SPB3HTc2w03PX03PZ02HB5Ha_st5Hl_stFFS2sp1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ0S2sp1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ0S1L3HLS2sp2lo3SLO2zp2dX2dZ3SPB1w3PX03PZ02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2zp2dX2dZ3SPB2w03PX03PZ02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2zp2dX2dZ2v03SPB3PX03PZ02HB5Ha_st5Hl_stS2sp1n1t2zp2dX2dZ1i2qw2IR3SPB3PX03PZ0S2sp1n1t2zp2dX2dZ1i2qw2IR3SPB3PX03PZ0S2sp1n1t2zp2T02dX2dZ1i2IR3SPB3PX03PZ0S2sp1n1t2zp2dX2dZ1i2IRS2sp1n1t2zp2dX2dZ1i2IRS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S1n1t2zp2T02dZ1i2IR2NZS2sp1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03HLZ3PZ0S2sp1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03HLZ3PZ0S2sp1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03HLZ3PZ0FFS2sp1n1t2zp2dX2dZ1i2IR3SPB3PX03PZ0S2sp1n1t2zp2dX2dZ1i2qw2IR3SPB3PX03PZ0S2sp1n1t2zp2dX2dZ1i2IR3SPB3PX03PZ02qwS2sp1t2zp2dX2dZ1i2qw5Ha_stS2sp1t2zp2dX2dZ1i2qw5Ha_stS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03PZ03PZ4S2sp2zp2dX2dZ1iS2sp2zp2dX2dZS2sp2zp2dX2dZS2sp2zp2dX2dZ1iS2sp2zp2dX2dZS2sp2zp2dX2dZS1L3HLS2sp2lo3SLO3ACL2zp2dX2dZ2v03SPB3PX03HLZ3PZ03PZ42HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL2zp2dX2dZ3SPB1w3PX03HLZ3PZ03PZ42HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL2zp2dX2dZ3SPB2w03PX03HLZ3PZ03PZ42HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S2sp2zp2dX2dZ2qw1q2QBS2sp1n1t2zp2T02dX2dZ1i2IR3SPB3PX03PZ0S2sp2zp2dX2dZS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S2sp2zp2dX2dZS2sp2zp2dX2dZ1w2HB5Ha_st5Hl_stS2sp2zp2dX2dZ2w02HB5Ha_st5Hl_stS2sp2zp2dX2dZ2qw1q2QBS1L3HLS2sp2lo3SLO3ACL3DHI2zp2dX2dZ2v03SPB3PX03PZ02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2zp2dX2dZ3SPB1w3PX03PZ02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2zp2dX2dZ3SPB2w03PX03PZ02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S2sp2zp2dX2dZS2sp2zp2dX2dZ2v03SPB2HB5Ha_st5Hl_stS2sp2zp2dX2dZ3SPB1w2HB5Ha_st5Hl_stS2sp2zp2dX2dZ3SPB2w02HB5Ha_st5Hl_stS2sp2zp2dX2dZS1t1iS1n1t2T02dZ1i2IR2NZ3HLZS2sp1n1t2zp2T02dX2dZ1i2IR3SPB3NXl3HLX3PX03PZ01NS2sp1n1t2zp2T02dX2dZ1i2IR3SPB3NXl3HLX3PX03PZ01NS2sp2zp2dX2dZS2sp2zp2dX2dZ2v02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03PZ03PZ42qwS1t2zp1iS1L3HLS2sp2lo3SLO3ACL2zp2dX2dZ2v03SPB3HLX3PX03PX43PZ02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL2zp2dX2dZ3SPB1w3HLX3PX03PX43PZ02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL2zp2dX2dZ3SPB2w03HLX3PX03PX43PZ02HB5Ha_st5Hl_stS1n1t2T02NB1i2IRS2sp2zp2dX2dZS2sp2zp2dX2dZF". (* [comment removed for export] *)
  Lemma L_bodyA3 : forall (n t zp k ib : Z) (j0 j64 : list byte), KONT n t zp k ib j0 j64 ->
    0 <= t -> n <= 10000 -> 0 <= k < 2^64 ->
    forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word) (i : Z) (qw v0 : word)
      (xra t0 t1 t2 a3 a4 a6 a7 t3 t4 t5 t6 x4 x7 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    t < i <= n -> i <= ib + 1 ->
    nth_error (md_limbs dZ) (Z.to_nat (i - t - 1)) = Some qw ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_p dX + 4 * i)) (Z_to_bv 64 (md_p dX)) (Z_to_bv 64 1) a3 a4 v0 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (4 * t))
               x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) (Z_to_bv 64 (i - t - 1)) (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x2134c) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros n t zp k ib j0 j64 K T0 NB Hk. intros until x7. intros CS_ ADDRS LL IR IB ZQ.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST _ MK.
    flat constr:(LL) 10%nat. intros OX NXl OY NY OZ PZ NZ OT NT VB.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CH0 CH1 CH2 CHT CHR. unfold t2cells in CH2.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 8%nat. intros FLt41 _ _ _ _ _ HFX _. flat constr:(FLt41) 2%nat. flclear FLt41. intros FLt42 _. flat constr:(FLt42) 6%nat. flclear FLt42. intros _ _ _ HLX HNX HOX.
    rewrite OX in HOX. flat constr:(HOX) 4%nat. flclear HOX. intros _ _ PALX UX. flat constr:((HFX OX)) 3%nat. intros PX0 PX4 _. unfold MPI_MAX_LIMBS in HNX.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 8%nat. intros FLt43 _ _ _ _ _ HFZ _. flat constr:(FLt43) 2%nat. flclear FLt43. intros FLt44 _. flat constr:(FLt44) 6%nat. flclear FLt44. intros _ _ _ HLZ HNZ HOZ.
    rewrite OZ in HOZ. flat constr:(HOZ) 4%nat. flclear HOZ. intros _ INZ PALZ UZ. flat constr:((HFZ OZ)) 3%nat. intros PZ0 PZ4 _. unfold MPI_MAX_LIMBS in HNZ. rewrite PZ in *.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp + -220, bv_unsigned sp + -208)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    zstep. zstep; if_cases K0; zify_cond K0; [exfalso; clear - K0 SLO ACL ACP HLS; lia|].
    zstep. zstep; if_cases K1; zify_cond K1; [exfalso; rewrite land_3_mod in K1; clear - K1 SPA; Z.div_mod_to_equations; lia|].
    zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    replace ((i + 1) * 4 + md_p dX + -8) with (md_p dX + 4 * (i - 1)) by (clear; lia).
    zstep. zstep; if_cases K2; zify_cond K2; [exfalso; clear - K2 PX0 PX4 NXl IR T0 ACL SLO HLS SPB; rewrite ?Z.mod_small in K2 by lia; lia|].
    zstep. zstep. zstep; if_cases K3; zify_cond K3; [clear - K3 PX0 PX4 NXl IR T0 ACL SLO HLS SPB; rewrite ?Z.mod_small in K3 by lia; lxu_pnull K3|].
    zstep; if_cases K4; zify_cond K4; [exfalso; clear - K4 PX0; lia|].
    zstep. zstep; if_cases K5; zify_cond K5;
      [exfalso; clear - K5 PALX PX0 PX4 NXl IR T0 ACL SLO HLS SPB; rewrite ?Z.mod_small in K5 by lia; rewrite land_3_mod in K5; Z.div_mod_to_equations; lia|].
    zstep. zstep; if_cases K6; zify_cond K6; [exfalso; clear - K6 SLO ACL ACP HLS SPB; lia|].
    zstep; if_cases K7; zify_cond K7; [exfalso; clear - K7 SLO ACL ACP HLS; lia|].
    (* [comment removed for export] *)
    rd UX (i - 1). zstep.
    zstep; if_cases K8; zify_cond K8; [exfalso; clear - K8 PX0 PX4 NXl IR T0 ACL SLO HLS SPB; rewrite ?Z.mod_small in K8 by lia; lia|].
    zstep. zstep; if_cases K9; zify_cond K9; [exfalso; clear - K9 SLO ACL ACP HLS SPB; lia|].
    rd UX i. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep; if_cases K10; zify_cond K10; [exfalso; clear - K10 IR T0 NB; lxu_contra|].
    (* [comment removed for export] *)
    zstep. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. replace ((i - t - 1) * 4) with (4 * (i - t - 1)) by (clear; lia).
    zstep; if_cases K11; zify_cond K11;
      [exfalso; clear - K11 PZ0 PZ4 NZ IR T0 NB ACL SLO HLS SPB; rewrite ?Z.mod_small in K11 by lia; lia|].
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : rw_cells usegs m1 (SP + -220) ?cs |- _ => rename H into CT2 end.
    lazymatch type of CT2 with rw_cells _ _ _ [C4 ?a; C4 ?b; C4 ?c] => set (u0' := a) in CT2; set (u1' := b) in CT2; set (u2' := c) in CT2 end.
    assert (CS1 : CST m1 moq hq LBq [dX; dY; dZ; dT] dR [] (LFR t k j0 j64 u0' u1' u2' j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (cs_frame_upd _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -220) (bv_unsigned sp + -208));
        [exact CS_| exact ADDRS| exact MU| exact WM| assumption| assumption| lia| lia| exact CH0| reflexivity| exact CT2| reflexivity| reflexivity]. }
    clear MU WM.
    (* [comment removed for export] *)
    pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    lazymatch goal with H : u32arr usegs m1 zp _ |- _ => rename H into UZ1 end.
    (* [comment removed for export] *)
    rdq UZ1 ZQ (i - t - 1). zstep.
    pose proof (u32arr_store_ok usegs _ zp (md_limbs dZ) (i - t - 1) _ UZ1 ltac:(lia) ltac:(f_equal; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] => pose proof (u32arr_write usegs _ zp (md_limbs dZ) (i - t - 1) v UZ1 ltac:(lia)) as UZ2 end.
    store_done. try clear SOKw.
    assert (ZQ2 : nth_error (upd (md_limbs dZ) (Z.to_nat (i - t - 1)) (Z_to_bv 64 (bv_unsigned (sx32 qw) + 1))) (Z.to_nat (i - t - 1)) = Some (Z_to_bv 64 (bv_unsigned (sx32 qw) + 1))).
    { apply nth_error_upd_same. clear - HLZ IR T0 NZ HNZ. lia. }
    rdq UZ2 ZQ2 (i - t - 1).
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    pose proof (u32arr_store_ok usegs m2 zp _ (i - t - 1) _ UZ2 ltac:(rewrite upd_length; lia) ltac:(f_equal; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      lazymatch type of UZ2 with u32arr _ _ _ ?l => pose proof (u32arr_write usegs m2 zp l (i - t - 1) v UZ2 ltac:(rewrite upd_length; lia)) as UZ3 end end.
    store_done. try clear SOKw.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch type of UZ3 with u32arr _ _ _ (upd _ _ ?v) => set (wq3 := v) in UZ3; lazymatch type of UZ3 with u32arr _ _ _ ?l => set (zs3 := l) in UZ3 end end.
    assert (CS3 : CST m3 moq hq LBq [dX; dY; set_limbs dZ zs3; dT] dR [] (LFR t k j0 j64 u0' u1' u2' j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false); [exact CS1| exact MU| exact WM| assumption| assumption| | reflexivity| | | reflexivity| discriminate].
      - constructor; [right; left; exists 2%nat, dZ; split; [reflexivity|]; split; [reflexivity|]; split; [exact OZ|]; cbn [fst snd]; clear - IR HNZ NZ T0 PZ; rewrite ?PZ; lia| constructor].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          [ do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
        cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OZ]|].
        intros _ _. rewrite PZ. split; [exact UZ3| subst zs3; rewrite !upd_length; exact HLZ].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
    (* [comment removed for export] *)
    set (q := bv_unsigned qw mod 4294967296).
    assert (QB : 0 <= q < 2^32) by (subst q; apply Z.mod_pos_bound; lia).
    eapply (L_inner n t zp k ib j0 j64 K T0 NB Hk i IR IB (Z.to_nat q)); [rewrite Z2Nat.id by lia; lia|].
    rewrite Z2Nat.id by lia. unfold ISTATE.
    exists m3, hq, LBq, dX, dY, (set_limbs dZ zs3), dT, u0', u1', u2', j68, t160, t164, t168, t176, t180, wq3. do 17 eexists.
    split; [reflexivity|]. split; [exact CS3|].
    split; [unfold locals_at; cbn [map set_limbs md_addr]; rewrite E0, E1, E2, E3; reflexivity|].
    split; [apply loop_loc_Z; exact LL|].
    split; [cbn [set_limbs md_limbs]; subst zs3; rewrite nth_error_upd_same by (rewrite upd_length; clear - HLZ HNZ NZ IR T0; lia); reflexivity|].
    subst wq3 q. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite bv_unsigned_sx32.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite bv_unsigned_sx32.
    change 4294967296 with (2^32). apply q_roundtrip. exact QB.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@D4662108261.172 D49416158319.172D6690581324.172 L12610030783.174L12734415834.10 L13072597906.169L13085246180.170L14678034333.172L17483385982.173L18964789310.169L18964789310.172L18964789560.172L38076755263.174L40738808152.168L41633390655.174L44229058992.3  L45093811327.174L51242545416.177L54966158628.175L57480193112.173L582101260.9    L59314841581.174L62867946550.169L62867946800.172L62867946800.173L66253711294.173L9746144436.174 00000100\01A02A02W03C03o04004104S05505O06O06\07\07d08d09309E09R09i0:X0;U0<U0=R0>O0>PFS2sp1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ0S2sp1n1t2zp2dX2dZ1i2qw2IR3SPB3PX03PZ0S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S1n1t2zp2T02dZ1i2IR2NZS2sp1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03HLZ3PZ0S2sp1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03HLZ3PZ0FFS2sp1n1t2zp2dX2dZ1i2IR3SPB3PX03PZ0S2sp1n1t2zp2dX2dZ1i2IR3SPB3PX03PZ0S2sp1t2zp2dX2dZ1i2qw5Ha_stS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S2sp2zp2dX2dZS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S1t2zp1iS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S2sp2zp2dX2dZ1iS2sp2zp2dX2dZ1i2K0S2sp2zp2dX2dZS1n1t2T02dZ1i2IR2NZ3HLZS2sp1n1t2zp2dX2dZ1i2IR3SPB3NXl3PZ03HLX3PX02K01NS1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2qw2IR3SPB2NZ3PX03PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PX03PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2T02dX2dZ1i2IR3SPB2NZ3PZ03PZ43PX0F". (* [comment removed for export] *)
  Lemma L_bodyA2 : forall (n t zp k ib : Z) (j0 j64 : list byte), KONT n t zp k ib j0 j64 ->
    0 <= t -> n <= 10000 -> 0 <= k < 2^64 ->
    forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word) (i : Z) (qw : word)
      (xra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    t < i <= n -> i <= ib + 1 ->
    nth_error (md_limbs dZ) (Z.to_nat (i - t - 1)) = Some qw ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_p dX + 4 * i)) (Z_to_bv 64 (md_p dX)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (4 * t))
               x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) (Z_to_bv 64 (i - t - 1)) (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x21304) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros n t zp k ib j0 j64 K T0 NB Hk. intros until x7. intros CS_ ADDRS LL IR IB ZQ.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST _ MK.
    flat constr:(LL) 10%nat. intros OX NXl OY NY OZ PZ NZ OT NT VB.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CH0 CH1 CH2 CHT CHR.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 8%nat. intros FLt45 _ _ _ _ _ HFX _. flat constr:(FLt45) 2%nat. flclear FLt45. intros FLt46 _. flat constr:(FLt46) 6%nat. flclear FLt46. intros _ _ _ HLX HNX HOX.
    rewrite OX in HOX. flat constr:(HOX) 4%nat. flclear HOX. intros _ _ PALX UX. flat constr:((HFX OX)) 3%nat. intros PX0 PX4 _. unfold MPI_MAX_LIMBS in HNX.
    (* [comment removed for export] *)
    zstep. zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
    (* [comment removed for export] *)
    - zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      zstep. zstep; if_cases K1; zify_cond K1; [lxu_pnull K1|].
      zstep. zstep. zstep. zstep; if_cases K2; zify_cond K2; [exfalso; apply K2; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia|].
      zstep; if_cases K3; zify_cond K3; [exfalso; lia|].
      zstep; if_cases K4; zify_cond K4; [exfalso; lia|].
      zstep. zstep; if_cases K5; zify_cond K5; [exfalso; rewrite lxu_land3 in K5; clear - K5 PALX; Z.div_mod_to_equations; lia|].
      rd UX (i - 2).
      eapply L_bodyA3; [exact K| exact T0| exact NB| exact Hk| exact CS_| exact ADDRS| exact LL| exact IR| exact IB| exact ZQ].
    (* [comment removed for export] *)
    - zstep. zstep.
      eapply L_bodyA3; [exact K| exact T0| exact NB| exact Hk| exact CS_| exact ADDRS| exact LL| exact IR| exact IB| exact ZQ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@D25171652884.176D9742868322.176 L10357916367.174L12688294881.176L14833703900.174L19895056584.179L21494960896.176L2589382760.176 L2589579755.175 L35205311618.175L35205508353.176L37079340467.174L40876281820.174L41252081172.177L41416270414.174L41418166478.172L41480287244.175L43526719554.175L44622288685.176L4602912984.177 L4602912984.178 L47940492020.174L48772764906.174L49698585326.176L50764594099.174L57480193112.174L59314841581.173L59314841581.174L59314841581.176L59577962801.176L63303730200.176L66232290991.176L66255672638.172L8161461422.176 00000j01^02@03@03J03V03b03l04604704804B04L04n05805B05Q05R06N06X06g07107l08K08U08_09K09o0:[0:e0:f0;A0<<0=<S1L2HI2sp1h4HTOP2hq2dX2dY1i3SPB3HTc3PX03PY02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dX2dY1i3SPB3PX03PY02HB5Ha_st5Hl_stS2sp1n1t2T02dX2dY1i2IR3SPB3PX03PY0S1L3HLS2sp2lo3SLO3ACL2dX2dY1i3SPB3PX03HLY3PY03PY42HB5Ha_st5Hl_stS2sp2dX2dYS2sp2dX2dY1iS2sp2dX2dY1iS2sp2dX2dYS2sp2dX2dYFFS2sp2dX2dYS2sp2dX2dYS2sp1n1t2T02dX2dY1i2IR3SPB3PX03PY0S2sp2dX2dYS2sp2dX2dYS2sp1t2T02dX2dYFS1L3HLS2sp2lo3SLO3ACL3DHI2dX2dY1i3SPB3PX03PY02HB5Ha_st5Hl_stS2sp2dX2dYS2sp2dX2dY1w2w0S2sp2dX2dYS1L3HLS2sp2lo3SLO3ACL1n1t2T02dX2dY1i2IR3SPB3NXl3PX03PX43PY0S2sp2dX2dY1i3SPB2HB5Ha_st5Hl_stS2sp2dX2dYS2sp2dX2dYS2sp1n1t2T02dX2dY1i2IR3SPB3NXl3HLX3PX03PY01NS2sp1t2T02dX2dY3SPB2NY3PX03HLY3PY01NS2sp1n1t2T02dX2dY1i2IR3SPB3NXl3HLX3PX03PY01NS2sp2dX2dYFS2sp2dX2dY1i2HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL1n1t2T02dX2dY1i2IR3SPB3NXl3PX03PX43PY0S1L3HLS2sp2lo3SLO3ACL2dX2dY1i3SPB3HLX3PX03PX43PY02HB5Ha_st5Hl_st". (* [comment removed for export] *)
  Lemma L_bodyA : forall (n t zp k ib : Z) (j0 j64 : list byte), KONT n t zp k ib j0 j64 ->
    0 <= t -> n <= 10000 -> 0 <= k < 2^64 ->
    forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word) (i : Z)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 x9 x10 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    t < i <= n -> i <= ib + 1 ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (4 * t))
               x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) x9 x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x211ec) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros n t zp k ib j0 j64 K T0 NB Hk. intros until x10. intros CS_ ADDRS LL IR IB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST _ MK.
    flat constr:(LL) 10%nat. intros OX NXl OY NY OZ PZ NZ OT NT VB.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CH0 CH1 CH2 CHT CHR.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 2%nat. intros CX _. rewrite E0 in CX. unfold mpi_cells in CX.
    flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 2%nat. intros CY _. rewrite E1 in CY. unfold mpi_cells in CY.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 8%nat. intros FLt51 _ _ _ _ _ HFX _. flat constr:(FLt51) 2%nat. flclear FLt51. intros FLt52 _. flat constr:(FLt52) 6%nat. flclear FLt52. intros _ _ _ HLX HNX HOX.
    rewrite OX in HOX. flat constr:(HOX) 4%nat. flclear HOX. intros _ _ PALX UX. flat constr:((HFX OX)) 3%nat. intros PX0 PX4 _. unfold MPI_MAX_LIMBS in HNX.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 8%nat. intros FLt53 _ _ _ _ _ HFY _. flat constr:(FLt53) 2%nat. flclear FLt53. intros FLt54 _. flat constr:(FLt54) 6%nat. flclear FLt54. intros _ _ _ HLY HNY HOY.
    rewrite OY in HOY. flat constr:(HOY) 4%nat. flclear HOY. intros _ _ PALY UY. flat constr:((HFY OY)) 3%nat. intros PY0 PY4 _. unfold MPI_MAX_LIMBS in HNY.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 8%nat. intros FLt55 _ _ _ _ _ HFZ _. flat constr:(FLt55) 2%nat. flclear FLt55. intros FLt56 _. flat constr:(FLt56) 6%nat. flclear FLt56. intros _ _ _ HLZ HNZ HOZ.
    rewrite OZ in HOZ. flat constr:(HOZ) 4%nat. flclear HOZ. intros _ INZ PALZ UZ. flat constr:((HFZ OZ)) 3%nat. intros PZ0 PZ4 _. unfold MPI_MAX_LIMBS in HNZ. rewrite PZ in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    zstep. replace (md_p dX + i * 4) with (md_p dX + 4 * i) by lia.
    zstep. rewrite (proj2 (Z.ltb_lt 0 (md_p dX)) PX0). change (Z.b2z true) with 1.
    zstep. zstep; if_cases K0; zify_cond K0; [lxu_pnull K0|].
    zstep. zstep. zstep. zstep. zstep; if_cases K1; zify_cond K1; [exfalso; apply K1; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia|].
    zstep; if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep; if_cases K3; zify_cond K3; [exfalso; rewrite lxu_land3 in K3; clear - K3 PALX; Z.div_mod_to_equations; lia|].
    zstep. zstep. zstep; if_cases K4; zify_cond K4; [exfalso; lia|].
    zstep. zstep. zstep. zstep; if_cases K5; zify_cond K5; [lxu_pnull K5|].
    zstep; if_cases K6; zify_cond K6; [exfalso; lia|].
    zstep. zstep; if_cases K7; zify_cond K7; [exfalso; rewrite lxu_land3 in K7; clear - K7 PALY; Z.div_mod_to_equations; lia|].
    rd UX i. rd UY t.
    zstep. zstep.
    lazymatch goal with |- context [Z_to_bv 64 (i + 1 + ?c)] => replace (Z_to_bv 64 (i + 1 + c)) with (Z_to_bv 64 (i - t - 1)) by (rewrite <- (zbv_add_modulus (i - t - 1)); f_equal; lia) end.
    assert (ZST : forall xa3 xa4 xa5 xa7 : word, aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_p dX + 4 * i)) (Z_to_bv 64 (md_p dX)) (Z_to_bv 64 1) xa3 xa4 xa5 (Z_to_bv 64 ((i - t - 1) * 4)) xa7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (4 * t))
               x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) (Z_to_bv 64 (i - t - 1)) (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x212d4) fc None mq (seg_rom usegs))).
    { intros xa3 xa4 xa5 xa7. zstep. replace (zp + (i - t - 1) * 4) with (zp + 4 * (i - t - 1)) by lia.
      pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
      pose proof (u32arr_store_ok usegs _ zp (md_limbs dZ) (i - t - 1) _ UZ ltac:(lia) ltac:(f_equal; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] => pose proof (u32arr_write usegs _ zp (md_limbs dZ) (i - t - 1) v UZ ltac:(lia)) as UZ1 end.
      store_done. try clear SOKw.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      lazymatch type of UZ1 with u32arr _ _ _ (upd _ _ ?v) => set (wq1 := v) in UZ1; lazymatch type of UZ1 with u32arr _ _ _ ?l => set (zs1 := l) in UZ1 end end.
      assert (CS1 : CST m1 moq hq LBq [dX; dY; set_limbs dZ zs1; dT] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false); [exact CS_| exact MU| exact WM| assumption| assumption| | reflexivity| | | reflexivity| discriminate].
        - constructor; [right; left; exists 2%nat, dZ; split; [reflexivity|]; split; [reflexivity|]; split; [exact OZ|]; cbn [fst snd]; clear - IR HNZ NZ T0 PZ; rewrite ?PZ; lia| constructor].
        - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
            [ do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
            | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
            | | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
          cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OZ]|].
          intros _ _. rewrite PZ. split; [exact UZ1| subst zs1; rewrite !upd_length; exact HLZ].
        - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
      assert (ZQ1 : nth_error (md_limbs (set_limbs dZ zs1)) (Z.to_nat (i - t - 1)) = Some wq1).
      { cbn [set_limbs md_limbs]. subst zs1. apply nth_error_upd_same. clear - HLZ HNZ NZ IR T0. lia. }
      assert (ADDRS1 : locals_at [dX; dY; set_limbs dZ zs1; dT]) by (unfold locals_at; cbn [map set_limbs md_addr]; rewrite E0, E1, E2, E3; reflexivity).
      pose proof (loop_loc_Z _ _ _ _ _ _ _ zs1 LL) as LL1.
      zstep.
      eapply L_bodyA2; [exact K| exact T0| exact NB| exact Hk| exact CS1| exact ADDRS1| exact LL1| exact IR| exact IB| exact ZQ1]. }
    zstep; if_cases K8.
    - zstep. zstep. zstep. zstep; if_cases K9; zify_cond K9; [exfalso; apply K9; rewrite ?Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia|].
      zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      zstep; if_cases K10; zify_cond K10; [exfalso; rewrite ?Z.mod_small in K10 by lia; clear - K10 PZ4 PZ0 NZ IR T0 ACL SLO SPB HLS; lia|].
      zstep. zstep. replace (zp + (i - t - 1) * 4) with (zp + 4 * (i - t - 1)) by lia.
      pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
      pose proof (u32arr_store_ok usegs _ zp (md_limbs dZ) (i - t - 1) _ UZ ltac:(lia) ltac:(f_equal; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] => pose proof (u32arr_write usegs _ zp (md_limbs dZ) (i - t - 1) v UZ ltac:(lia)) as UZ1 end.
      store_done. try clear SOKw.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      lazymatch type of UZ1 with u32arr _ _ _ (upd _ _ ?v) => set (wq1 := v) in UZ1; lazymatch type of UZ1 with u32arr _ _ _ ?l => set (zs1 := l) in UZ1 end end.
      assert (CS1 : CST m1 moq hq LBq [dX; dY; set_limbs dZ zs1; dT] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false); [exact CS_| exact MU| exact WM| assumption| assumption| | reflexivity| | | reflexivity| discriminate].
        - constructor; [right; left; exists 2%nat, dZ; split; [reflexivity|]; split; [reflexivity|]; split; [exact OZ|]; cbn [fst snd]; clear - IR HNZ NZ T0 PZ; rewrite ?PZ; lia| constructor].
        - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
            [ do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
            | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
            | | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
          cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OZ]|].
          intros _ _. rewrite PZ. split; [exact UZ1| subst zs1; rewrite !upd_length; exact HLZ].
        - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
      assert (ZQ1 : nth_error (md_limbs (set_limbs dZ zs1)) (Z.to_nat (i - t - 1)) = Some wq1).
      { cbn [set_limbs md_limbs]. subst zs1. apply nth_error_upd_same. clear - HLZ HNZ NZ IR T0. lia. }
      assert (ADDRS1 : locals_at [dX; dY; set_limbs dZ zs1; dT]) by (unfold locals_at; cbn [map set_limbs md_addr]; rewrite E0, E1, E2, E3; reflexivity).
      pose proof (loop_loc_Z _ _ _ _ _ _ _ zs1 LL) as LL1.
      eapply L_bodyA2; [exact K| exact T0| exact NB| exact Hk| exact CS1| exact ADDRS1| exact LL1| exact IR| exact IB| exact ZQ1].
    - zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      zstep. zstep; if_cases K9; zify_cond K9; [lxu_pnull K9|].
      zstep. zstep. zstep. zstep; if_cases K10; zify_cond K10; [exfalso; apply K10; rewrite ?Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia|].
      zstep; if_cases K11; zify_cond K11; [exfalso; lia|].
      zstep; if_cases K12; zify_cond K12; [exfalso; lia|].
      zstep. zstep; if_cases K13; zify_cond K13; [exfalso; rewrite lxu_land3 in K13; clear - K13 PALX; Z.div_mod_to_equations; lia|].
      zstep. zstep. zstep. zstep; if_cases K14; zify_cond K14; [exfalso; apply K14; rewrite ?Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia|].
      zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      zstep; if_cases K15; zify_cond K15; [exfalso; rewrite ?Z.mod_small in K15 by lia; clear - K15 PZ4 PZ0 NZ IR T0 ACL SLO SPB HLS; lia|].
      rd UX (i - 1).
      zstep. zstep. zstep. zstep. zstep. zstep. zstep; if_cases K16.
      + apply ZST.
      + zstep. apply ZST.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L1334498603.4 L48179439333.4L54819953900.6L59308599793.500000:00F00R00_S1t1D1i2HDS1t1D2i'3IB'S1n1t2i'3IR'S1n1t1i2HD2IR". (* [comment removed for export] *)
  Lemma L_iloop : forall (n t zp k : Z) (j0 j64 : list byte),
    0 <= t -> n <= 10000 -> 0 <= k < 2^64 ->
    forall (D : nat) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word) (i : Z)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 x9 x10 : word),
    i - t <= Z.of_nat D ->
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    t < i <= n ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (4 * t))
               x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) x9 x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x211ec) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros n t zp k j0 j64 T0 NB Hk.
    induction D as [|D IH]; intros until x10; intros HD CS_ ADDRS LL IR; [exfalso; clear - HD IR; lia|].
    eapply (L_bodyA n t zp k (t + Z.of_nat D)); [| exact T0| exact NB| exact Hk| exact CS_| exact ADDRS| exact LL| exact IR| clear - HD; lia].
    unfold KONT. intros * CS' ADDRS2 LL' IR' IB'.
    eapply IH; [clear - IB'; lia| exact CS'| exact ADDRS2| exact LL'| clear - IR'; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma loop_loc_Ys : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "PdX,$:.PdY,$:.PdZ,$:.PdT,$:.Pn,$0.Pt,$0.Pzp,$0.Pys,(8.(3.&40.))P,(64.R8.R7.R6.R5.R4.R3.R2.)(64.R9.(65.R8.R2.)R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof. intros * H. unfold loop_loc in *. decompose [and] H. cbn. repeat split; auto. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@D25171652884.190D25171652884.191D9742868322.190 D9742868322.191 L11603572298.188L13669995828.185L13669996307.163L14293316440.190L17301622520.152L19339280541.2  L21335385048.187L24509182583.55 L24510886384.39 L24897143244.3  L24897143244.39 L24897143244.5  L24948143878.153L24949835555.163L26736795524.5  L28506356230.153L28920966066.187L29872710004.188L30873744702.1  L32957941119.27 L34515333208.190L34649796472.2  L34809482490.27 L35902521332.188L36634634861.186L36635087953.180L36950922632.2  L39544944451.1  L40738808152.188L41418166475.191L41418168651.188L41912781940.187L44622288685.190L44622288685.191L45174325948.1  L4602912984.188 L47245696618.4  L48519053616.185L48519054103.163L49698585326.190L49698585326.191L49966973991.27 L50713542139.3  L50764594099.162L54422758649.27 L56998993008.27 L5775618124.4   L5775996609.186 L5777896062.187 L58263967292.5  L58432025651.27 L59308628179.6  L61346358657.3  L61929812241.180L64342654565.27 L6495468378.27  L66232290991.190L66232290991.191L66963798079.19100000b01W02C03203903e04H04O04S04Y04`04a04b04f04j04n05905D05U05`05g05n06106?06F06K06`06g07S08?08@08C08J08Q08X08_09S0:J0:N0:U0:]0:m0;40;P0;o0<00<90<@0<N0=20==0=i0>U0>f0>g0?80?@0?X0@20@30@K0@f0@oS1L2HI2sp1h4HTOP1t2hq2dY3SPB2P03HTc2HB5Ha_st5Hl_stS1L2HI2sp1h4HTOP2hq2dY3SPB2P03HTc2HB5Ha_st5Hl_st1t2zpS1L3HLS2sp2lo3SLO1t2dY3SPB2P02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO2dY3SPB2P02HB5Ha_st5Hl_st1t2zpS2sp2dYS1L3HLS2sp2lo3SLO3ACL2dY3SPB3ACP2P03x174LEN2S1L3HLS2sp2lo3SLO3ACL2dY3SPB3ACP2P0S2sp2dYS2spS1t2zpS2sp2dYFFS2dYS2dYS2dYS2sp2dY3HNYS2sp2dY3HNYS1L3HLS2sp2lo3SLOS2sp2dY3HNYS2sp2dYS2sp2dYS1tS2sp2dY3HNY2K0S2sp2dYS1n1tS2sp1n1t2dY2TN2NB3SPBS2sp2dYS1L3HLS2sp2lo3SLO3ACL1n1t2dY2TN3SPB2NY2P02P4S1L3HLS2sp2lo3SLO3ACL1n1t2dY2TN3SPB2NY2P02P4SS1tS2sp2dYS2sp2dYS2sp2dYS2sp2dYS1L3HLS2sp2lo3SLO3ACL3DHI1t2dY3SPB2P02HB5Ha_st5Hl_stS1L3HLS2sp2lo3SLO3ACL3DHI2dY3SPB2P02HB5Ha_st5Hl_st1t2zpS2dYS2sp2dYS1n1t2K1S2sp2dY3ys24LEN2S2sp2dYS2sp1t2dY3SPB2HB5Ha_st5Hl_stS2sp2dY3SPB2HB5Ha_st5Hl_st1t2zpFS2dY1q2HqS2sp2dYS2sp2dY3SPB2HLS1L3HLS2sp2lo3SLO3ACL3SPA2dY3SPB3ACPS1n1t2TN2NBS1L3HLS2sp2lo3SLO3ACL1n1t2dY2TN3SPB2NY2P02P4S1L3HLS2sp2lo3SLO3ACL1n1t2dY2TN3SPB2NY2P02P4S1L3HLS2sp2lo3SLOFS1n1t2dY2TN2NY2K0S1n1t2TNS2sp1n1t2dY2TN2NB3SPB2P0S1L2sp2lo3ACL2dY3SPB2HL2P4FS2sp1t2dY2HB5Ha_st5Hl_stS2sp2dY2HB5Ha_st5Hl_st1t2zpS2sp1n2dY". (* [comment removed for export] *)
  Lemma L_setup : forall (n t zp k : Z) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (j0 : list byte) (w8 w16 w24 w40 w48 : word) (j64 : list byte) (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word)
      (xra x4 x9 x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    0 <= t <= n -> n <= 10000 -> 0 <= k < 2^64 ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 (Z_to_bv 64 (n + 1)) (Z_to_bv 64 (32 * (n - t)))
               (Z_to_bv 64 (t + 1)) (Z_to_bv 64 (0xffffffffffffffff - zp)) x9 x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x21198) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ ADDRS LL TN NB Hk.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:(LL) 10%nat. intros OX NXl OY NY OZ PZ NZ OT NT VB.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 8%nat. intros MY NSY _ _ _ _ HF _.
    flat constr:((HF OY)) 5%nat. intros P0 P4 _ _ _.
    zstep. zstep. zstep.
    pose proof HSHR as SSH. unfold mpi_shift_r_stmt, U_MPI_SHIFT_R in SSH.
    eapply aevtM_cut_evt; [exact MK| eapply SSH with (LB := LBq) (dX := dY) (count := 32 * (n - t)) (lo := lo);
      rewrite ?unsigned_lit by lia; try eassumption; try reflexivity|].
    all: try (intros _; split; clear - P0 P4 ACL; lia).
    all: try (rewrite E1; first [left; clear - SLO HLS SPB SPA ACL; lia| right; clear - SLO HLS SPB SPA ACL; lia]).
    all: try (intros _; right; rewrite E1; clear - P4 SLO HLS SPB ACL; lia).
    all: try (rewrite E1; f_equal; clear; lia).
    all: try (clear - SLO HLS SPB SPA ACL TN NB; lia).
    clear SSH. cbv beta. intros ms' PO. unfold mpi_shift_r_post in PO.
    flat constr:(PO) 24%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 ys2 -> MU WM MI2 ST2 MA2 LEN2 _.
    rewrite ?unsigned_lit in MU, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x211a4)) with (Z_to_bv 64 0x211a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (proj1 MA2) as MA2'. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in MA2'. rewrite OY in MA2'.
    destruct MA2' as (_ & _ & _ & HL2 & _ & _ & _ & _ & U2).
    assert (CS2 : CST m2 moq hq LBq [dX; set_limbs dY ys2; dZ; dT] dR [] (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 1%nat) false false); [exact CS_| exact MU| exact WM| exact MI2| exact ST2| | reflexivity| | | reflexivity| discriminate].
      - constructor; [left; cbn [fst snd]; clear - SLO HLS; lia| constructor; [right; left; exists 1%nat, dY; split; [reflexivity|]; split; [reflexivity|]; split; [exact OY|]; cbn [fst snd]; clear; lia| constructor]].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          [do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C] |
          | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
        cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OY]|].
        intros _ _. split; [exact U2| exact HL2].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
    assert (ADDRS2 : locals_at [dX; set_limbs dY ys2; dZ; dT]) by (unfold locals_at; cbn [map set_limbs md_addr]; rewrite E0, E1, E2, E3; reflexivity).
    pose proof (loop_loc_Ys _ _ _ _ _ _ _ ys2 LL) as LL2.
    clear MY NSY HF U2 HL2 MA2 LEN2 MU WM CS_ HH HTc MF SOK MI ST CH MK.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS2)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS2)) 5%nat. intros CF0 CF1 CF2 CFT CFR.
    zstep. zstep.
    zstep; if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    { eapply L_fin; [exact CS2| exact ADDRS2| reflexivity| exact Hk| exact VB]. }
    pose proof (munch_refl [(SP + -280, SP + -232)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match type of CF0 with rw_cells _ _ _ [_; _; _; C8 ?a24; _; _; C8 ?a48; _; _] =>
      assert (W24 : a24 = Z_to_bv 64 (2^64 - (t + 2)));
      [| assert (W48 : a48 = Z_to_bv 64 (4 * (t - 1)))] end.
    { rewrite lxor_allones64 by (clear - TN NB; lia). f_equal. clear; lia. }
    { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_eq by lia. apply Z_to_bv_eqm. unfold eqm. change (bv_modulus 64) with (2^64).
      match goal with |- ((?x - ?M * ?q) * _) mod _ = _ => replace ((x - M * q) * 2^2) with (4 * (t - 1) + (- (4 * q)) * 2^64) by (clear; lia) end.
      rewrite Z_mod_plus_full. reflexivity. }
    rewrite W24, W48 in CF0.
    assert (CS3 : CST m3 moq hq LBq [dX; set_limbs dY ys2; dZ; dT] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { unfold lframe. eapply (cs_frame_upd _ _ _ _ _ _ _ _ _ _ (SP + -280) (SP + -232));
        [exact CS2| exact ADDRS2| exact MU| exact WM| exact MI| exact ST| clear; lia| clear; lia| exact CF0| reflexivity| exact CF1| reflexivity| reflexivity]. }
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4. replace (t * 4) with (4 * t) by (clear; lia).
    eapply (L_iloop n t zp k j0 j64 (proj1 TN) NB Hk (Z.to_nat (n - t)));
      [rewrite Z2Nat.id by (clear - TN; lia); clear; lia| exact CS3| exact ADDRS2| exact LL2| clear - TN K1; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0@D4662108261.183 D49416158319.183D6690581324.183 L11254569813.15 L12734415834.8  L13659512551.197L13672109588.226L14678034333.183L16075584458.167L18964789310.180L18964789310.182L18964789560.183L246904734.1    L25817004560.226L29010566049.206L35169284936.180L35180357960.179L35304777808.16 L36253289358.15 L46703120695.180L49158382690.232L56996506657.15 L59308628304.1  L59308944635.3  L59314841581.179L61274419438.1  L61352289665.180L62867946550.179L62867946800.182L62867946800.183L68351284511.16 L7586519423.2   L9746144436.183 00000100]01F01a02202g03\03]03^04E04l05P05Q05i05j06X07F07G07T07c08V09709;09E0:50:60:U0;T0<S0=T0=U0=\0=]FS2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB1w2NZ3PZ0S2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB1w3PZ0S1L2HI2sp1h4HTOP2hq3SPB3HTcS1n1t2zp2dZ2TN2NZS1L3HLS2sp2lo3SLO3ACL2zp2vy1D2dX2dY2dZ2VX3SPB3ACP3PZ0S1L3HLS2sp2lo3SLO3ACL2zp2vy1D2dX2dY2dZ2VX3SPB3ACP3PZ0FFS2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB3PZ0S2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB3PZ0S2sp1n1t2zp2vy1D2dX2dY2dZ2VX1w5Ha_stSS2sp2zp2vy1D2dX2dY2dZ2VXFS2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB2NZ3HLZ3PZ0S2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB2NZ3HLZ3PZ0FS1L2sp2lo3SLOS2sp2vy1D2dX2VXS2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB3NXl3PZ03dX43KN4S1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2K1S2vy2dX2VXS2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB2NZ3HLZ3PZ01NSS2sp1n1t2zp2vy1D2dX2dY2dZ2TN2VXS1L3HLS2sp2lo3SLO3ACL1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB2NZ3PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB2NZ3PZ03PZ4S1L3HLS2sp2lo3SLO3ACL1n1t2zp2vy1D2dX2dY2dZ2TN2VX3SPB1w2NZ3PZ03PZ4FS2dX2dYF". (* [comment removed for export] *)
  Lemma L_loop1 : forall (n t zp k vy : Z) (D : nat) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (j0 : list byte) (w8 w16 w24 w40 w48 : word) (j64 : list byte) (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word)
      (xra x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    0 <= t <= n -> n <= 10000 -> 0 <= k < 2^64 ->
    0 <= mpd_val dX < Z.of_nat D * vy -> mpd_val dY = vy -> 0 < vy ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (zp + 4 * (n - t))) (Z_to_bv 64 (n + 1)) (Z_to_bv 64 (32 * (n - t))) (Z_to_bv 64 (t + 1))
               (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 (4 * (n - t))) x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x20fa0) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros n t zp k vy D. induction D as [|D IH]; intros until t6; intros CS_ ADDRS LL TN NB Hk VX VY VY0; [exfalso; clear - VX; lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:(LL) 10%nat. intros OX NXl OY NY OZ PZ NZ OT NT VB.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 8%nat. intros MX NSX WRX LOX CRX CRXL HFX _.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 8%nat. intros MY NSY WRY LOY CRY CRYL HFY _.
    pose proof HCMP as SPC. unfold mpi_cmp_mpi_stmt, U_MPI_CMP_MPI in SPC.
    eapply aevtM_cut_evt; [exact MK| eapply SPC with (dX := dX) (dY := dY) (LB := LBq); try eassumption; try reflexivity|].
    all: try (rewrite ?E0, ?E1; reflexivity).
    1:{ intros O. flat constr:((HFX O)) 2%nat. intros P0 _. exact P0. }
    1:{ intros O. flat constr:((HFY O)) 2%nat. intros P0 _. exact P0. }
    clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO.
    flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x20fac)) with (Z_to_bv 64 0x20fac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    clear MX NSX WRX LOX CRX CRXL HFX MY NSY WRY LOY CRY CRYL HFY.
    pose proof (Z.sgn_spec (mpd_val dX - mpd_val dY)) as SG.
    zstep; if_cases K0; zify_cond K0; rewrite ?signed_lit_small in K0 by (clear - SG; lia).
    { (* [comment removed for export] *)
      eapply L_setup; [exact CS_| exact ADDRS| exact LL| exact TN| exact NB| exact Hk]. }
    (* [comment removed for export] *)
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 8%nat. intros FLt57 _ _ _ _ _ HFZ _. flat constr:(FLt57) 2%nat. flclear FLt57. intros FLt58 _. flat constr:(FLt58) 6%nat. flclear FLt58. intros _ _ _ HLZ HNZ HOZ.
    rewrite OZ in HOZ. flat constr:(HOZ) 4%nat. flclear HOZ. intros _ INZ PALZ UZ. flat constr:((HFZ OZ)) 3%nat. intros PZ0 PZ4 _. unfold MPI_MAX_LIMBS in HNZ. rewrite PZ in *.
    zstep; if_cases KW; zify_cond KW; [exfalso; rewrite ?unsigned_lit in KW by Stdlib.micromega.Lia.lia; rewrite ?Z.mod_small in KW by Stdlib.micromega.Lia.lia; pose proof (@alloc_ceiling_hi L) as ACH; clear - KW PZ0 PZ4 TN NZ HNZ ACH; Stdlib.micromega.Lia.lia|].
    pose proof (munch_refl [(zp + 4 * (n - t), zp + 4 * (n - t) + 4)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    rd UZ (n - t). zstep.
    pose proof (u32arr_store_ok usegs _ zp (md_limbs dZ) (n - t) _ UZ ltac:(lia) ltac:(f_equal; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] => pose proof (u32arr_write usegs _ zp (md_limbs dZ) (n - t) v UZ ltac:(lia)) as UZ2 end.
    store_done. try clear SOKw.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch type of UZ2 with u32arr _ _ _ ?l => set (zs2 := l) in UZ2 end.
    assert (CS2 : CST m2 moq hq LBq [dX; dY; set_limbs dZ zs2; dT] dR [] (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false); [exact CS_| exact MU| exact WM| assumption| assumption| | reflexivity| | | reflexivity| discriminate].
      - constructor; [right; left; exists 2%nat, dZ; split; [reflexivity|]; split; [reflexivity|]; split; [exact OZ|]; cbn [fst snd]; clear - TN HNZ NZ PZ; rewrite ?PZ; lia| constructor].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          [ do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
        cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; [reflexivity| exact OZ]|].
        intros _ _. rewrite PZ. split; [exact UZ2| subst zs2; rewrite !upd_length; exact HLZ].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
    assert (ADDRS2 : locals_at [dX; dY; set_limbs dZ zs2; dT]) by (unfold locals_at; cbn [map set_limbs md_addr]; rewrite E0, E1, E2, E3; reflexivity).
    pose proof (loop_loc_Z _ _ _ _ _ _ _ zs2 LL) as LL2.
    clear MU WM UZ2 CS_. try clear UZ. try clear HFZ. try clear CH. reopen CS2 HH HTc MF SOK MI ST MK.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS2 eq_refl)) 8%nat. intros MX NSX WRX LOX CRX CRXL HFX _.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS2 eq_refl)) 8%nat. intros MY NSY WRY LOY CRY CRYL HFY _.
    flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0 0 dX dX CS2 eq_refl eq_refl)) 2%nat. intros SEP00 OPS00.
    flat constr:((mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0 1 dX dY CS2 eq_refl eq_refl)) 2%nat. intros SEP01 OPS01.
    pose proof (HAS (-1) (or_intror eq_refl)) as SPA_.
    eapply aevtM_cut.
    { eapply SPA_ with (dX := dX) (dA := dX) (dB := dY) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?E0, ?E1, ?E2, ?E3; reflexivity). }
    clear SPA_. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m4 mo4 h4 LB4 dX4 r E MI4 ST4 MF4 HT4 HH4 MA4 OUT4 PX4 SOK4 RR.
    replace (ret_pc (Z_to_bv 64 0x20fd4)) with (Z_to_bv 64 0x20fd4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros R1 FLt59. flat constr:(FLt59) 4%nat. flclear FLt59. intros KA4 KP4 KF4 KN4.
    assert (CS4 : CST m4 mo4 h4 LB4 (set_nth 0 [dX; dY; set_limbs dZ zs2; dT] dX4) dR [] (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_l; [exact CS2| reflexivity| exact HH4| exact HT4| exact MF4| exact MA4| exact OUT4| exact PX4| exact SOK4| exact MI4| exact ST4| exact KF4]. }
    cbn [set_nth] in CS4.
    assert (ADDRS4 : locals_at [dX4; dY; set_limbs dZ zs2; dT]) by (unfold locals_at; cbn [map set_limbs md_addr]; rewrite KA4, E0, E1, E2, E3; reflexivity).
    assert (LL4 : loop_loc dX4 dY (set_limbs dZ zs2) dT n t zp) by (eapply loop_loc_X; [exact LL2| eapply out_heap; [exact MA4| exact (proj1 (proj2 OUT4))| lia]| exact KN4]).
    assert (Hr : (r = 0 /\ mpd_val dX4 = mpd_val dX - mpd_val dY) \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED).
    { destruct R1 as [[Hr0 HV]|HrF]; [left; split; [exact Hr0| rewrite HV; clear; lia]| right; exact HrF]. }
    clear MX NSX WRX LOX CRX CRXL HFX MY NSY WRY LOY CRY CRYL HFY SEP00 OPS00 SEP01 OPS01 R1 KF4 KP4 MA4 OUT4 PX4 CS2 LL2 ADDRS2.
    reopen CS4 HH HTc MF SOK MI ST MK.
    zstep.
    zstep; if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      destruct Hr as [[_ HV]|Hr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K1; clear - K1; lia].
      eapply IH; [exact CS4| exact ADDRS4| exact LL4| exact TN| exact NB| exact Hk| clear - HV VX VY VY0 K0 SG; nia| exact VY| exact VY0].
    - zstep. eapply L_c0; [exact CS4| exact ADDRS4| reflexivity| reflexivity| | exact VB].
      destruct Hr as [[Hr _]|Hr]; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in *; clear - K1; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L11254568491.20 L13669996307.169L13672109588.198L14438269063.161L15320243423.5  L17301622520.160L18959778753.2  L19158930680.160L20656067758.3  L22575354352.20 L24950276741.161L28508491653.159L28623755671.2  L29010565666.187L2924076915.2   L29315511165.161L31183074820.1  L33552813087.5  L35304777006.20 L41415908595.189L41418087781.5  L49124147222.190L51085802335.190L54328243591.159L54854443536.198L54856524567.169L56996503903.20 L59308628179.1  L64431196287.3  L65376664684.4  L66458274172.3  L8927148449.159 L8929260191.187 L911840735.4    L9931863465.20  00000K00h01E01P01`01d01k01o02;02H02S02^02e02f02n03203603A03B03L03M03W03a03l04004404U04Y04c05305>05X06206A06[S1L2HI2sp1h4HTOP2hq3SPB3HTcS1L3HLS2sp2lo3SLO3ACL3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPB3ACPS2sp2dX3HNXS2dX2dY3dY31r2HrS2spS2dX2dYS2spS2dY3dY33KN3S1L2sp2lo3SLOS2sp2dY3HNYS2sp2dY3HNYS2dX2VXFS2dX3HNXS2spS2dXS2dX2dY3NYXFS2sp2dX2dYSS2sp2dX2dYS2sp2dX2dYS2sp2dX3HNXS2spS2spS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2K0S2zp2dX2dYS2dY3NY13dY33KN3S2dX2dZ3NXZS2sp2dX2dY3NYX3SPB3HNX3NY1S2sp2dX2dY3NYX3SPB3HNX3NY1S2dX2dY3NYX3NY1S2sp2dX2dY3NYX3SPB3HNX3HNY". (* [comment removed for export] *)
  Lemma L_m3 : forall (k zp : Z) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 : word) (j64 : list byte) (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word)
      (xra x5 x6 x7 x8 x9 x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    md_own dX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_p dZ = zp -> md_own dT = LHeap -> 2 <= md_n dT ->
    md_n dY <= md_n dX -> md_n dX + 1 <= md_n dZ ->
    0 <= mpd_val dX -> 0 < mpd_val dY -> 0 <= k < 2^64 -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 k) x5 x6 x7 x8 x9 x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x20f68) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ ADDRS OX OY OZ PZ OT NT NYX NXZ VX VY Hk VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 5%nat. intros CX SGX HNX XNUL XHEAP. rewrite E0 in CX. unfold mpi_cells in CX. unfold MPI_MAX_LIMBS in HNX.
    flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 5%nat. intros CY SGY HNY YNUL YHEAP. rewrite E1 in CY. unfold mpi_cells in CY. unfold MPI_MAX_LIMBS in HNY.
    flat constr:((XHEAP OX)) 2%nat. intros PX0 NX1. flat constr:((YHEAP OY)) 2%nat. intros PY0 NY1.
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dX)) by lia. zstep. rewrite (zx16_small (md_n dY)) by lia.
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 8%nat. intros MY NSY WRY LOY CRY CRYL HFY _.
    pose proof HSHL as SPS. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SPS.
    eapply aevtM_cut.
    { eapply SPS with (dX := dY) (count := (md_n dX - md_n dY) * 32) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc HNX HNY NYX; lia).
      all: try (rewrite ?E0, ?E1, ?E2, ?E3; reflexivity).
      all: try (f_equal; clear - HNX HNY NYX; lia). }
    clear SPS. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m3 mo3 h3 LB3 dY3 r E MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR.
    replace (ret_pc (Z_to_bv 64 0x20f84)) with (Z_to_bv 64 0x20f84) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros R1 FLt60. flat constr:(FLt60) 4%nat. flclear FLt60. intros KA3 KP3 KF3 KN3.
    assert (CS3 : CST m3 mo3 h3 LB3 (set_nth 1 [dX; dY; dZ; dT] dY3) dR [] (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_l; [exact CS_| reflexivity| exact HH3| exact HT3| exact MF3| exact MA3| exact OUT3| exact PX3| exact SOK3| exact MI3| exact ST3| exact KF3]. }
    cbn [set_nth] in CS3.
    assert (ADDRS3 : locals_at [dX; dY3; dZ; dT]) by (unfold locals_at; cbn [map]; rewrite KA3, E0, E1, E2, E3; reflexivity).
    assert (OY3 : md_own dY3 = LHeap) by (eapply out_heap; [exact MA3| exact (proj1 (proj2 OUT3))| clear - KN3 NY1; lia]).
    assert (Hr : (r = 0 /\ mpd_val dY3 = mpd_val dY * 2 ^ ((md_n dX - md_n dY) * 32)) \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED).
    { destruct R1 as [(Hr0 & HV & _)|HrF]; [left; split; [exact Hr0| exact HV]| right; exact HrF]. }
    clear MY NSY WRY LOY CRY CRYL HFY R1 KF3 KP3 MA3 OUT3 PX3 CS_ CX CY CH.
    reopen CS3 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    { eapply L_err; [exact CS3| exact ADDRS3| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia| exact VB]. }
    destruct Hr as [[_ HV]|Hr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K0; clear - K0; lia]. clear K0.
    (* [comment removed for export] *)
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS3)) 5%nat. intros CF0 CF1 CF2 CFT CFR.
    pose proof (munch_refl [(bv_unsigned sp + -288, bv_unsigned sp + -208)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep. zstep. zstep.
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
    match type of CF0 with rw_cells _ ?mx _ ?c0 => match type of CF1 with rw_cells _ _ _ ?c1 =>
      assert (CS4 : CST mx mo3 h3 LB3 [dX; dY3; dZ; dT] dR [] (frame c0 c1 j68 (tcells t160 t164 t168 t176 t180)) [])
        by (eapply cs_frame_upd; [exact CS3| exact ADDRS3| exact MU| exact WM| assumption| assumption| Stdlib.micromega.Lia.lia| Stdlib.micromega.Lia.lia| exact CF0| reflexivity| exact CF1| reflexivity| reflexivity]) end end.
    assert (VY3 : 0 < mpd_val dY3) by (rewrite HV; apply Z.mul_pos_pos; [exact VY| apply Z.pow_pos_nonneg; clear - HNX HNY NYX; lia]).
    replace (Z_to_bv 64 (md_n dX)) with (Z_to_bv 64 ((md_n dX - 1) + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (md_n dY)) with (Z_to_bv 64 ((md_n dY - 1) + 1)) by (f_equal; lia).
    replace ((md_n dX - md_n dY) * 32) with (32 * ((md_n dX - 1) - (md_n dY - 1))) by (clear; lia).
    replace ((md_n dX - md_n dY) * 4) with (4 * ((md_n dX - 1) - (md_n dY - 1))) by (clear; lia).
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ CS4 eq_refl)) 8%nat. intros _ _ _ _ _ _ HFZ _. flat constr:((HFZ OZ)) 3%nat. intros PZ0 PZ4 _. rewrite PZ in PZ0, PZ4.
    pose proof (@alloc_ceiling_hi L) as ACH.
    rewrite ?(Z.mod_small zp 18446744073709551616) by Stdlib.micromega.Lia.lia. rewrite ?(Z.mod_small zp (2^64)) by Stdlib.micromega.Lia.lia. rewrite zb_lxor_ones by Stdlib.micromega.Lia.lia.
    eapply (L_loop1 (md_n dX - 1) (md_n dY - 1) zp k (mpd_val dY3) (Z.to_nat (mpd_val dX + 1)));
      [exact CS4| exact ADDRS3| | clear - NYX NY1; lia| clear - HNX; lia| exact Hk| rewrite Z2Nat.id by (clear - VX; lia); clear - VX VY3; nia| reflexivity| exact VY3].
    unfold loop_loc. split; [exact OX|]. split; [clear; lia|]. split; [exact OY3|]. split; [clear - KN3; lia|].
    split; [exact OZ|]. split; [exact PZ|]. split; [clear - NXZ; lia|]. split; [exact OT|]. split; [exact NT| exact VB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma val_lval : forall mq LBq d, mpd_at usegs mq LBq d -> md_sg d = 1 -> mpd_val d = lval (md_limbs d) (md_n d).
  Proof.
    intros mq LBq d [(_ & _ & _ & HL & _) _] SG. unfold mpd_val. rewrite SG, Z.mul_1_l. fold (mpd_abs d). apply mpd_abs_lval. exact HL.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00i0@L11254748466.19 L13669996307.195L13669996307.226L13672109588.224L13672109588.255L15320243423.7  L17301622520.169L22343444146.182L22575357070.19 L22575731433.19 L24356465842.185L24511139416.41 L24897143244.3  L24897143244.41 L24950081828.168L2668244716.4   L27605118583.185L29010566049.216L29742944465.248L30197694287.6  L31525662448.167L31525856484.3  L31525859044.166L32027975233.0  L32237656832.4  L34358816812.7  L35079898537.4  L35304777808.19 L3602613805.184 L36953018911.2  L39352618855.19 L39353024768.19 L40631134805.3  L40715968912.224L40718049431.195L41417907836.4  L43100038149.184L43143153634.4  L44018045102.183L44188293008.255L44190373527.226L4918824764.4   L50574068621.2  L50574197157.166L50574199717.3  L50713542139.3  L50764594099.169L52094629443.4  L54425245910.3  L5498208254.166 L56996506657.19 L56996880966.19 L59308628304.1  L60543194556.4  L63036381883.19 L6493751157.3   L68351105912.20 00000T01E02:02k03`04604@04J04`05605C05D05H05L05Z05j06:06;06<06P06^06i07707807F07\07j07k08L08M08^08o09:09J09Z09d0:50:E0:R0:b0;20;A0;I0;W0;b0;k0<50<B0<J0<X0=B0=l0>00>>0>b0>c0>dS1L2HI2sp1h4HTOP2hq2dY3SPB3HTc2bl2shS1L3HLS2sp2lo3SLO3ACL2dX2dY3SPB3ACP3PY02bl3BLR2shS1L3HLS2sp2lo3SLO3ACL2dX2dY3SPB3ACP3PY02bl3BLR2sh3SHBS1L3HLS2sp2lo3SLO3ACL2dX2dY3SPB3ACP3PY02bl3BLR2shS1L3HLS2sp2lo3SLO3ACL2dX2dY3SPB3ACP3PY02bl3BLR2sh3SHBS2dX2dY2bl2sh3dX31r2HrS2sp2dX2dYS2sp2dX2dYS1L2sp2lo3SLO2dY2bl2shS1L2sp2lo3SLO2dY2bl2shS2sp2dX2dY2blFS2dYS2dYS2sp2dX2dY3HNYS2dX3NX13dX33KN3S2sp2dX2dY2bl2BMFFS2dY2bl2sh3dY42r42HrS2sp2dX2dY3HNYS2dX2dY3VXYS2sp2dX2dY3HNYSS2dY2bl2sh3SHBS2dX2dY2dZ3NXZ2bl2sh1HS2dY2bl2sh3SHBFS2sp2dX2dY3NYX3SPB3PY03HNX2bl3BLRSS2sp2dY2bl2sh3SHBS2sp2dY2bl2sh3SHBS2dX2dZ3NXZS2sp2dX2dY2bl2shS2sp2dX2dY2bl2shS2dY2bl2shS2sp2dX2dY2bl3BLRS2dY3NY13dY43KN4S2sp2dX2dY2blS2sp2dX2dY2bl2shS2sp2dX2dY2bl2shS2dX2dY3NYX3NY1S2dX3NX1S2sp2dX2dY3HNXS2dX2dY3VXYS2dY1q2HqS2sp2dX2dYS2dY2bl2BM2K0S2dY3HLYS2sp2dX2dY3VXYS1L3HLS2sp2lo3SLO3ACL3SPA2dY3SPB3ACP2bl2shS1L3HLS2sp2lo3SLO3ACL3SPA2dY3SPB3ACP2bl2shS2K1S2dY2bl2sh3SHBS1L2HI2sp1h4HTOP2dY3SPB2bl2sh2h33HTcFF". (* [comment removed for export] *)
  Lemma L_m2 : forall (zp : Z) (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 : word) (j64 : list byte) (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word)
      (xra x4 x5 x6 x7 x8 x9 x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    md_own dX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_p dZ = zp -> md_own dT = LHeap -> 2 <= md_n dT ->
    md_n dY <= md_n dX -> md_n dX + 2 <= md_n dZ -> md_sg dX = 1 -> md_sg dY = 1 ->
    0 < mpd_val dY <= mpd_val dX -> 0 < mpd_abs dB ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x20f4c) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ ADDRS OX OY OZ PZ OT NT NYX NXZ SGX SGY VXY VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 5%nat. intros CY _ HNY YNUL YHEAP. rewrite E1 in CY. unfold mpi_cells in CY. unfold MPI_MAX_LIMBS in HNY.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 8%nat. intros FLt61 _ _ _ _ _ HFY _. flat constr:(FLt61) 2%nat. flclear FLt61. intros FLt62 _. flat constr:(FLt62) 6%nat. flclear FLt62. intros _ _ _ HLY _ HOY.
    rewrite OY in HOY. flat constr:(HOY) 4%nat. flclear HOY. intros NY1 INY PALY UY. flat constr:((HFY OY)) 3%nat. intros PY0 PY4 _.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 2%nat. intros FLt63 _. flat constr:(FLt63) 2%nat. flclear FLt63. intros FLt64 _. flat constr:(FLt64) 6%nat. flclear FLt64. intros _ _ _ HLX HNX HOX.
    rewrite OX in HOX. flat constr:(HOX) 2%nat. flclear HOX. intros NX1 _. unfold MPI_MAX_LIMBS in HNX.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 2%nat. intros MX _. flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 2%nat. intros MY _.
    pose proof (val_lval _ _ _ MX SGX) as VLX. pose proof (val_lval _ _ _ MY SGY) as VLY.
    pose proof (core_bitlen_mono_val (md_limbs dX) (md_n dX) (md_limbs dY) (md_n dY) ltac:(lia) ltac:(lia) ltac:(rewrite <- VLX, <- VLY; lia)) as BLM.
    pose proof (core_bitlen_range (md_limbs dY) (md_n dY) ltac:(lia)) as BLR.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (zx16_small (md_n dY)) by lia. zstep.
    pose proof HCBL as SPB_. unfold mpi_core_bitlen_stmt, U_MPI_CORE_BITLEN in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (A := md_p dY) (n := md_n dY) (xs := md_limbs dY); try eassumption; try reflexivity|].
    all: try (apply u32arr_ro; exact UY).
    all: try (clear - HNY HLY; lia).
    all: try (clear - PALY; apply Z.mod_divide in PALY; [| lia]; apply Z.mod_divide; [lia|]; (flat constr:(PALY) 2%nat; flclear PALY; intros q Hq); exists (4 * q); lia).
    clear SPB_. cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO. destruct_exs PO.
    flat constr:(PO) 5%nat. flclear PO. intros -> _ _ _ ->.
    replace (ret_pc (Z_to_bv 64 0x20f58)) with (Z_to_bv 64 0x20f58) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    set (bl := core_bitlen (md_limbs dY) (md_n dY)) in *.
    pose proof (Z.mod_pos_bound bl 32 ltac:(lia)) as BM.
    zstep. rewrite land_31 by lia. zstep.
    zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
    - (* [comment removed for export] *)
      zstep. rewrite lxor_ones5 by lia.
      set (sh := 31 - bl mod 32) in *. assert (SHB : 1 <= sh <= 31) by (subst sh; clear - BM K0; lia).
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 8%nat. intros MX_ NSX WRX LOX CRX CRXL HFX _.
      pose proof HSHL as SPS. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SPS.
      eapply aevtM_cut.
      { eapply SPS with (dX := dX) (count := sh) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc SHB; lia).
        all: try (rewrite ?E0, ?E1, ?E2, ?E3; reflexivity). }
      clear SPS. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      binop_post PO m3 mo3 h3 LB3 dX3 r E MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR.
      replace (ret_pc (Z_to_bv 64 0x21180)) with (Z_to_bv 64 0x21180) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(RR) 2%nat. flclear RR. intros R1 FLt65. flat constr:(FLt65) 4%nat. flclear FLt65. intros KA3 KP3 KF3 KN3.
      assert (CS3 : CST m3 mo3 h3 LB3 (set_nth 0 [dX; dY; dZ; dT] dX3) dR [] (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply mc_binop_l; [exact CS_| reflexivity| exact HH3| exact HT3| exact MF3| exact MA3| exact OUT3| exact PX3| exact SOK3| exact MI3| exact ST3| exact KF3]. }
      cbn [set_nth] in CS3.
      assert (ADDRS3 : locals_at [dX3; dY; dZ; dT]) by (unfold locals_at; cbn [map]; rewrite KA3, E0, E1, E2, E3; reflexivity).
      assert (OX3 : md_own dX3 = LHeap) by (eapply out_heap; [exact MA3| exact (proj1 (proj2 OUT3))| clear - KN3 NX1; lia]).
      assert (Hr : (r = 0 /\ mpd_val dX3 = mpd_val dX * 2 ^ sh /\ md_sg dX3 = md_sg dX /\ md_n dX3 = shift_l_n sh dX) \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED).
      { destruct R1 as [(Hr0 & HV & HS & HN)|HrF]; [left; auto| right; exact HrF]. }
      clear MX_ NSX WRX LOX CRX CRXL HFX R1 KF3 KP3 MA3 OUT3 PX3 CY UY CH.
      reopen CS3 HH HTc MF SOK MI ST MK.
      zstep; if_cases K1; zify_cond K1.
      { eapply L_err; [exact CS3| exact ADDRS3| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia| exact VB]. }
      destruct Hr as [(_ & HVX & HSX & HNX3)|Hr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K1; clear - K1; lia]. clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY CS3 eq_refl)) 8%nat. intros MY_ NSY WRY LOY CRY CRYL HFY_ _.
      pose proof HSHL as SPS. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SPS.
      eapply aevtM_cut.
      { eapply SPS with (dX := dY) (count := sh) (lo := lo) (h := h3) (LB := LB3); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc SHB; lia).
        all: try (rewrite ?KA3, ?E0, ?E1, ?E2, ?E3; reflexivity). }
      clear SPS. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      binop_post PO m4 mo4 h4 LB4 dY4 r4 E MI4 ST4 MF4 HT4 HH4 MA4 OUT4 PX4 SOK4 RR.
      replace (ret_pc (Z_to_bv 64 0x21190)) with (Z_to_bv 64 0x21190) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(RR) 2%nat. flclear RR. intros R1 FLt66. flat constr:(FLt66) 4%nat. flclear FLt66. intros KA4 KP4 KF4 KN4.
      assert (CS4 : CST m4 mo4 h4 LB4 (set_nth 1 [dX3; dY; dZ; dT] dY4) dR [] (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply mc_binop_l; [exact CS3| reflexivity| exact HH4| exact HT4| exact MF4| exact MA4| exact OUT4| exact PX4| exact SOK4| exact MI4| exact ST4| exact KF4]. }
      cbn [set_nth] in CS4.
      assert (ADDRS4 : locals_at [dX3; dY4; dZ; dT]) by (unfold locals_at; cbn [map]; rewrite KA4, KA3, E0, E1, E2, E3; reflexivity).
      assert (OY4 : md_own dY4 = LHeap) by (eapply out_heap; [exact MA4| exact (proj1 (proj2 OUT4))| clear - KN4 NY1; lia]).
      assert (Hr : (r4 = 0 /\ mpd_val dY4 = mpd_val dY * 2 ^ sh /\ md_sg dY4 = md_sg dY /\ md_n dY4 = shift_l_n sh dY) \/ r4 = MBEDTLS_ERR_MPI_ALLOC_FAILED).
      { destruct R1 as [(Hr0 & HV & HS & HN)|HrF]; [left; auto| right; exact HrF]. }
      clear MY_ NSY WRY LOY CRY CRYL HFY_ R1 KF4 KP4 MA4 OUT4 PX4 CS3 ADDRS3.
      reopen CS4 HH HTc MF SOK MI ST MK.
      zstep; if_cases K1; zify_cond K1.
      { eapply L_err; [exact CS4| exact ADDRS4| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia| exact VB]. }
      destruct Hr as [(_ & HVY & HSY & HNY4)|Hr]; [| exfalso; subst r4; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K1; clear - K1; lia]. clear K1.
      zstep.
      assert (P2 : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; clear - SHB; lia).
      eapply (L_m3 sh zp); [exact CS4| exact ADDRS4| exact OX3| exact OY4| exact OZ| exact PZ| exact OT| exact NT| | | | | clear - SHB; lia| exact VB].
      + rewrite HNX3, HNY4. apply shift_l_n_mono; [clear - SHB; lia| clear - NYX NY1; lia| exact BLM].
      + rewrite HNX3. pose proof (shift_l_n_le_succ sh dX ltac:(clear - SHB; lia) ltac:(clear - NX1; lia)). clear - H NXZ. lia.
      + rewrite HVX. clear - VXY P2. nia.
      + rewrite HVY. clear - VXY P2. nia.
    - (* [comment removed for export] *)
      zstep. eapply (L_m3 0 zp); [exact CS_| exact ADDRS| exact OX| exact OY| exact OZ| exact PZ| exact OT| exact NT| exact NYX| clear - NXZ; lia| clear - VXY; lia| clear - VXY; lia| clear; lia| exact VB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma opnd_facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PCS,(8.(42.$0.(8.$3<.)))Pd,$:.P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R7.R6.R5.R4.R3.VdR,(4?.$9.)R2.(4?.(42.$0.(8.$3<.))))P,(1.(41.$:.R2.$4;.)(2.$:.R2.VdR,))(31.(<.$4<.R9.R6.R3.)(31.(14.VL,R6.Vlo,(15.R3.)+10.)(31.P,(2.$?.(10.R3.)$16.)(14.VL,R7.Vlo,(17.R4.)(18.+4.(19.R4.)))(31.P,(>.(2.$?.(10.R3.)$1<.))(1.(1=.(1>.(17.R4.)(18.+4.(19.R4.)))Vlo,)(1=.(1>.(13.&40.Vsp,)-120.)(17.R4.)))(31.P,(2.$?.(10.R3.)$16.)(31.(32.=(17.R4.))(1=.+1.(19.R4.)))(1.(1=.(1>.(15.R3.)+10.)Vlo,)(1=.(13.&40.Vsp,)(15.R3.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls CS d CS_ [IN|E].
    - flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ _ CS_ IN)) 6%nat. intros ME CRE CREL LE HFE ASE.
      split; [exact ME|]. split; [exact CRE|]. split; [exact CREL|]. split; [exact LE|]. split; [| exact ASE]. intros O. flat constr:((HFE O)) 4%nat. intros P0 _ _ N1. auto.
    - rewrite E. flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW _ _ _ LW CRW CRWL HFW ASW _.
      split; [exact MW|]. split; [exact CRW|]. split; [exact CRWL|]. split; [exact LW|]. split; [| exact ASW]. intros O. flat constr:((HFW O)) 4%nat. intros P0 _ _ N1. auto.
  Qed.
  Lemma opnd_sep_l : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PCS,(8.(42.$0.(8.$3<.)))Pi,$4=.Pdi,$:.Pd,$:.P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R9.R8.R7.R6.R5.VdR,(4?.$9.)R4.(4?.(42.$0.(8.$3<.))))P,(2.(5.$:.)(50.$:.R6.R4.)(51.$:.R3.))P,(1.(41.$:.R3.$4;.)(2.$:.R3.VdR,))(31.(=.R5.R4.)(12.R5.R4.Vlo,(1>.(13.&40.Vsp,)-120.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls CS i di d CS_ Hi [IN|E].
    - exact (mc_opnd_sep_le _ _ _ _ _ _ _ _ _ i di d CS_ Hi IN).
    - rewrite E. exact (mc_opnd_sep_lw _ _ _ _ _ _ _ _ _ i di CS_ Hi).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01]0@D15693759375.221D25171652884.174D25171652884.175D26836135970.221D31233843170.174D36655585506.175D41386762978.208D41386762978.222D5082246559.207 D5082246559.208 D5082246559.222 D53128511161.207D64220354184.221L10645010990.2  L11256719616.18 L13082847747.201L13669996303.226L13672077207.187L13672109588.255L13672228662.169L13982323198.172L14556395849.171L14556395849.219L15320243423.4  L1556619717.220 L16695035536.255L17592780024.202L18008924610.172L18468797831.2  L19064786548.217L20304442840.220L22136722483.220L2213969294.18  L22881030104.169L23461310230.165L23541585465.2  L24418977839.175L25640717784.169L25649702269.2  L25864836748.219L26032823479.3  L26033846918.3  L27017465125.170L27023838098.213L28811841688.8  L28814044093.200L29010565920.244L29150155311.208L29150155311.222L29613760150.207L29956516996.0  L30542433823.172L32121109934.3  L32275636709.18 L32338763764.172L32362796660.169L33330066392.1  L35274813740.2  L3556165204.202 L35909626660.8  L36605650392.217L39319860527.174L40825300462.18 L41132015570.220L41411501643.199L4173929907.201 L42428319433.1  L42743412937.2  L42755330731.217L42755330731.221L42755330989.214L44622288685.174L44622288685.175L44622288685.222L46302493051.19 L4933004239.2   L49698585326.174L49698585326.175L49698585326.207L49698585326.208L49698585326.222L50464586734.220L51040919282.49 L52970903990.221L53442142006.218L54976524414.203L54976524414.204L56809307369.218L56883890379.2  L56970658055.1  L56996506657.18 L58666067060.169L59308628304.3  L59308628433.1  L60901541340.3  L61243392304.172L61261352215.9  L6267329815.193 L63024886479.18 L64703406222.18 L64812528791.18 L64823245511.195L6514581356.220 L66251664681.3  L663383774.18   L8069655616.172 L876130995.221  L876131253.218  L876131253.220  00000E01201_01h02O03603c04P05J06D07707d07e07m08H08Q09709W0:=0:]0:^0:_0:`0:m0:n0;70;@0;M0;U0;^0;g0<>0<K0<R0<]0<e0=;0=B0=J0=S0=^0=i0>40>A0>Y0?80?90?Q0?i0@A0@B0@C0@N0@[0@b0@i0@l0A20A;0AS0A\0B20B60BM0BV0B_0Bc0Bk0CF0Ca0D<0Dk0EZ0FO0FP0FX0G20GL0Gh0HD0H`0Ho0I00I10I:0J:0K:0K;0KC0KG0Kh0Ko0L90L=0LG0LT0Lj0M10M?0MJ0MU0Mb0Mk0N40NO0NV0Nc0O00O=S2sp2dA3SPB3HLA1A3BA0S1L2HI2sp1h2dA4HTOP2hq3SPB3HTc2HB5Ha_st5Hl_stS1L2HI2sp1h2dA4HTOP2hq3SPB3HTc2HB5Ha_st5Hl_stS2sp2dA1AS1L3HLS2sp2dA2lo3SLO3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2dA2lo3SLO3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2dA2lo3SLO3SPB1A3BA02HB5Ha_st5Hl_stS1L3HLS2sp2dA2lo3SLO3SPB1A3BA02HB5Ha_st5Hl_stS1L2HI2sp1h2dA4HTOP2hq3SPB3HTc1A2h23HT23BA02HB5Ha_st5Hl_stS1L2HI2sp1h2dA4HTOP2hq3SPB3HTc1A2h23HT23BA02HB5Ha_st5Hl_stS1L2HI2sp1h2dA4HTOP3SPB1A2h23BA03HTc2HB5Ha_st5Hl_stS1L3HLS2sp2dA2lo3SLO3SPB1A3BA02HB5Ha_st5Hl_stFS2dA3HNAS1L2HI2sp1h4HTOP2hq3SPB3HTcS2sp2dA1AS1L3HLS2sp2dA2lo3SLO3ACL3SPB1A3BA03ACVS1L3HLS2sp2dA2lo3SLO3ACL3SPB3ACPS1L3HLS2sp2dA2lo3SLO3ACL3SPB1A3BA03ACVS1L3HLS2sp2dA2lo3SLO3ACL3SPB3ACPFFFS2dA3dT41r2HrFS2sp2dA1AS2sp2dA1AS2sp2dA2dT2E3S2dA3HNAS2sp2dA1AS2sp2dA1AS2sp2dA2dY3SPB2E11A3BA0S1L2sp2lo3SLOS2sp2dAS2sp2dA3HNAS2dA3HNAS2sp2dA2HB5Ha_st5Hl_stS2sp2dAS2dA3HNAS2sp2dA1AS2dA3HNA2K0S2dA2dX3NXAS2sp2dA3HNAS2sp2dA3HNA1AS1L2dA3HNA1A3BA03BA43ACVS1L2sp2dA3SPB3HLA1A3BA03BA43ACVFS2sp2dA1A2HB5Ha_st5Hl_stS2sp2dA1A2HB5Ha_st5Hl_stS2sp2dA1A2HB5Ha_st5Hl_stSFS2dA2dB3VABS1L2sp2lo3SLOS2sp2dAS2sp2dAS1AS2dA1AS2sp2dA1AS1L2dA3HNA1A3BA03BA43ACVS2sp2dA1AS2sp2dA2HB5Ha_st5Hl_stS2spS2sp2dA2dX3SPB2E01A3BA0S2sp2dA1AS2sp2dA1AS2dAS2dA3HNAS1L2sp2dA3SPB3HLA1A3BA43ACVS1L2sp2dA3SPB3HLA1A3BA43ACVS1L2sp2dA3SPB3HLA1A3BA43ACVS1L3HLS2sp2dA2lo3SLO3ACL3DHI3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2dA2lo3SLO3ACL3DHI3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2dA2lo3SLO3ACL3DHI3SPB1A3BA02HB5Ha_st5Hl_stFS2dA3HNAS2sp2dA3SPB2HB5Ha_st5Hl_stS2sp2dA3SPB2HB5Ha_st5Hl_stS2sp2dA3SPB1A2HB5Ha_st5Hl_stS2sp2dA3SPB1A2HB5Ha_st5Hl_stS2sp2dA3SPB1A2HB5Ha_st5Hl_stS2sp2dA2dT2E31AFFS2sp2dA1AS1L3HLS2sp2dA2lo3SLO3ACL2dX3NXA3SPB3NX11A3BA03BA42HB5Ha_st5Hl_stS1L3HLS2sp2dA2lo3SLO3ACL2dX3NXA3SPB3NX11A3BA03BA42HB5Ha_st5Hl_stFS2dA3HNAS2spS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2sp2dAS1A3BA02K1S2K2S2dA3HNA1AS2sp2dA2dZ2E2S1L2sp2dA2lo3ACL1A3BA4S2sp2dAS2sp2dA3SPB2K0S2sp2dA3HNAS2sp2dA3HNAS2sp2dA3HNA1AS2sp2dA1AS2sp1a2HaS1L2HI2sp1h4HTOP3SPB2h23HTcS2sp2dAS2sp2dA1A3BA0S2sp2dA1A3BA0S2sp2dA1A3BA0". (* [comment removed for export] *)
  Lemma L_m1 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 : word) (j64 : list byte) (u0 u1 u2 j68 t160 t164 t168 t176 t180 : word)
      (xra x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    md_own dX = LHeap -> md_own dY = LHeap -> md_own dZ = LNull -> md_own dT = LNull ->
    md_n dY <= md_n dX -> md_n dX <= md_n dA ->
    mpd_abs dX = mpd_abs dA -> mpd_abs dY = mpd_abs dB -> 0 < mpd_abs dB <= mpd_abs dA ->
    aevtM usegs moq (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (div_mpi_rem_R LB dR dA dB) lo m mo)
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20ecc) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ ADDRS OX OY OZ OT NYX NXA AX AY VAB. assert (VB : 0 < mpd_abs dB) by (clear - VAB; lia).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof ADDRS as ADDRS'. unfold locals_at in ADDRS'. cbn [map] in ADDRS'. injection ADDRS' as E0 E1 E2 E3.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CF0 CF1 CF2 CFT CFR. unfold t2cells in CF2.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 5%nat. intros CX SGX HNX _ XHEAP. rewrite E0 in CX. unfold mpi_cells in CX. unfold MPI_MAX_LIMBS in HNX.
    flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 5%nat. intros CY SGY HNY _ YHEAP. rewrite E1 in CY. unfold mpi_cells in CY. unfold MPI_MAX_LIMBS in HNY.
    flat constr:((struct_cells _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 5%nat. intros CZ SGZ _ ZNUL _. clear CZ.
    flat constr:((ZNUL OZ)) 2%nat. intros PZ0 NZ0.
    flat constr:((XHEAP OX)) 2%nat. intros PX0 NX1. flat constr:((YHEAP OY)) 2%nat. intros PY0 NY1.
    flat constr:((opnd_facts _ _ _ _ _ _ dA CS_ opndA)) 2%nat. intros FLt67 _. flat constr:(FLt67) 2%nat. flclear FLt67. intros FLt68 SGA. flat constr:(FLt68) 6%nat. flclear FLt68.
    intros CSA HALA HPOSA HLA HNA _. unfold mpi_cells in CSA. unfold MPI_MAX_LIMBS in HNA.
    first [pose proof (rw_cells_bound _ _ _ _ CSA) as AB| pose proof (ro_cells_bound _ _ _ _ CSA) as AB]. cbn [cells_size csize Nat.add] in AB. clear CSA.

    zstep.
    pose proof (munch_refl [(SP + -152, SP + -134)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (CS1 : CST m1 moq hq LBq [set_sg dX 1; set_sg dY 1; dZ; dT] dR []
                    (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (SP + -152) (SP + -134) []);
        [exact CS_| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| | |].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          try (left; split; [lia| reflexivity]).
        + right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. rewrite E0. unfold mpi_cells. assumption.
        + right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. rewrite E1. unfold mpi_cells. assumption.
      - unfold frame, t2cells. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd]; assumption.
      - apply frame_chs; [| reflexivity| reflexivity| reflexivity]. unfold locals_at. cbn [map set_sg md_addr]. rewrite E0, E1, E2, E3. reflexivity. }
    assert (ADDRS1 : locals_at [set_sg dX 1; set_sg dY 1; dZ; dT]) by (unfold locals_at; cbn [map set_sg md_addr]; rewrite E0, E1, E2, E3; reflexivity).
    clear MU WM CS_ CX CY CH CF0 CF1 CF2 CFT CFR. reopen CS1 HH HTc MF SOK MI ST MK.

    zstep; if_cases KN; zify_cond KN.
    { exfalso. rewrite ?unsigned_lit, ?Z.mod_small in KN by (clear - HPOSA AB; lia). clear - KN HPOSA. lia. }
    zstep. zstep; if_cases KA; zify_cond KA.
    { exfalso. rewrite ?unsigned_lit in KA by (clear - HPOSA AB; lia). change 7 with (Z.ones 3) in KA. rewrite Z.land_ones in KA by lia.
      apply KA. change (2^3) with 8. clear - HALA. lia. }

    flat constr:((opnd_facts _ _ _ _ _ _ dA CS1 opndA)) 2%nat. intros ((CSA1 & _) & _) _. unfold mpi_cells in CSA1.
    zstep. rewrite (zx16_small (md_n dA)) by lia. clear CSA1.
    zstep. zstep. zstep.
    zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
    { eapply L_c0; [exact CS1| exact ADDRS1| reflexivity| reflexivity| clear; lia| exact VB]. }

    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ ?pc _ _ _ _) => replace pc with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity) end.
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := md_n dA + 2) (sz := 4) (lo := lo);
      rewrite ?unsigned_lit by lia; try eassumption; try reflexivity |].
    all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc HNA K0; lia).
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as -> ->. rewrite ?unsigned_lit in PO by lia.
    flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 PR2 h2 HT2 RES.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    lazymatch type of MI2 with mem_inv _ ?mx => rename mx into m2 end.
    lazymatch type of MF2 with mo_frame _ ?mx => rename mx into mo2 end.
    destruct RES as [[-> HH2] | (A & -> & BRA & HH2 & ZCH)].
    {
      assert (CS2 : CST m2 mo2 h2 LBq [set_sg dX 1; set_sg dY 1; dZ; dT] dR []
                      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
      { eapply (mc_heap_nop _ _ _ _ _ _ _ _ _ 0); [exact CS1| reflexivity| exact HH2| exact HT2| exact MF2| exact PR2| exact MI2| exact ST2]. }
      clear CS1 HH HTc MF SOK MI ST MK. reopen CS2 HH HTc MF SOK MI ST MK.
      zstep; if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity].
      eapply L_c0; [exact CS2| exact ADDRS1| reflexivity| reflexivity| clear; lia| exact VB]. }

    flat constr:(BRA) 5%nat. intros BA0 BA16 _ BA4 _.
    pose proof alloc_ceiling_bounds as ACV.
    flat constr:((struct_cells _ _ _ _ _ _ _ 2 dZ CS1 eq_refl)) 2%nat. intros CZ1 _. rewrite E2 in CZ1. unfold mpi_cells in CZ1. rewrite PZ0, NZ0 in CZ1.
    assert (CZ2 : rw_cells usegs m2 (SP + -176) [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 (md_sg dZ)); C2 (Z_to_bv 64 0); C4 (md_pad dZ)]).
    { eapply (heap_pres_rw_cells usegs L LBq _ m1 m2); [exact PR2| exact CZ1|]. intros a Ha. left. cbn [cells_size csize Nat.add] in Ha. clear - Ha. lia. }
    clear CZ1. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    pose proof (munch_refl [(SP + -176, SP + -160)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof (conj MI2 (conj ST2 (conj HH2 ZCH))) as PROT.
    zstep; if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by (clear - BA0 BA4 ACP; lia); clear - K1 BA0; lia|].

    zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    rename MI2 into MI3. rename CZ2 into CZ3. try clear ST2. try clear HH2. try clear ZCH. flat constr:(PROT) 4%nat. flclear PROT. intros MI2 ST2 HH2 ZCH.
    assert (CS3 : CST m3 mo2 h2 ((A, 4 * (md_n dA + 2)) :: LBq)
              (set_nth 2 [set_sg dX 1; set_sg dY 1; dZ; dT] (mkMPD (md_addr dZ) (md_sg dZ) (md_n dA + 2) A (repeat (Z_to_bv 64 0) (Z.to_nat (md_n dA + 2))) (md_pad dZ) LHeap))
              dR [] (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_calloc_attach _ _ _ _ _ _ _ _ _ 2 dZ m2 mo2 h2 A (md_n dA + 2) m3 (md_sg dZ) (md_pad dZ));
        [exact CS1| reflexivity| exact OZ| | exact HT2| exact MF2| exact PR2| exact MI2| exact ST2| | | unfold MPI_MAX_LIMBS; clear - K0 HNA; lia
        | rewrite E2; replace (SP + -176 + 16) with (SP + -160) by (clear; lia); exact MU| exact WM| exact MI3| rewrite E2; unfold mpi_cells; exact CZ3| exact SGZ].
      - replace (4 * (md_n dA + 2)) with ((md_n dA + 2) * 4) by (clear; lia). exact HH2.
      - replace (4 * (md_n dA + 2)) with ((md_n dA + 2) * 4) by (clear; lia). exact BRA.
      - replace (4 * (md_n dA + 2)) with ((md_n dA + 2) * 4) by (clear; lia). exact ZCH. }
    cbn [set_nth] in CS3.
    match type of CS3 with cstate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [_; _; ?dz; _] _ _ _ _ => set (dZ3 := dz) in CS3 end.
    assert (ADDRS3 : locals_at [set_sg dX 1; set_sg dY 1; dZ3; dT]) by (unfold locals_at; cbn [map set_sg md_addr dZ3]; rewrite E0, E1, E2, E3; reflexivity).
    clear MU WM CS1 CZ3 HH HTc MF SOK MI ST MK MK2 PR2 ZCH MI2 ST2 HH2 MI3. reopen CS3 HH HTc MF SOK MI ST MK.

    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ3 CS3 eq_refl)) 2%nat. intros FLt69 _. flat constr:(FLt69) 2%nat. flclear FLt69. intros FLt70 _. flat constr:(FLt70) 6%nat. flclear FLt70. intros _ _ _ _ _ HOZ3.
    cbn [dZ3 md_own md_p md_n md_limbs] in HOZ3. flat constr:(HOZ3) 4%nat. flclear HOZ3. intros _ _ _ UZ3.
    pose proof (u32arr_cells _ _ _ _ UZ3) as ZCH3. rewrite repeat_length in ZCH3.
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
    pose proof U_memset_spec as SPm. unfold memset_stmt in SPm.
    eapply aevtM_cut_evt; [exact MK| eapply SPm with (junk := u32s (repeat (Z_to_bv 64 0) (Z.to_nat (md_n dA + 2)))); clear SPm | clear SPm].
    { rewrite !unsigned_lit by (clear - BA0 BA4 ACV HNA K0; lia).
      replace (Z.to_nat ((md_n dA + 2) * 4)) with (4 * Z.to_nat (md_n dA + 2))%nat by (clear - HNA; lia). exact ZCH3. }
    { exact MI. }
    unfold memset_post. cbv beta. intros ms' PO.
    flat constr:(PO) 20%nat. flclear PO. intros z0 z1 z2 za1 za2 z3 z4 z5 z6 z7 z8 z9 z10 z11 m4 E MUd WMd MI4 ZCH4. subst ms'.
    rewrite !unsigned_lit in MUd, ZCH4 by (clear - BA0 BA4 ACV HNA K0; lia).
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    assert (UZ4 : u32arr usegs m4 A (repeat (Z_to_bv 64 0) (Z.to_nat (md_n dA + 2)))).
    { eapply u32arr_of_cells; [exact ZCH4|]. rewrite u32s_repeat0. change (0 mod 256) with 0. f_equal. clear - HNA. lia. }
    assert (ST4 : stk usegs m4 lo SPc).
    { eapply stk_transport_disjoint; [exact ST| exact MUd| exact WMd|]. cbn. clear - BA0 BA4 ACL HNA. lia. }
    assert (CS4 : CST m4 mo2 h2 ((A, 4 * (md_n dA + 2)) :: LBq) [set_sg dX 1; set_sg dY 1; dZ3; dT] dR []
                    (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false); [exact CS3| exact MUd| exact WMd| exact MI4| exact ST4| | reflexivity| | | reflexivity| discriminate].
      - constructor; [right; left; exists 2%nat, dZ3; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; cbn [fst snd dZ3 md_p md_n]; clear; lia| constructor].
      - intros j d d' Hj Hj'. rewrite Hj in Hj'. injection Hj' as <-. do 6 (split; [reflexivity|]). split; [intros _; reflexivity|].
        intros EJ _. injection EJ as <-. cbn in Hj. injection Hj as <-. cbn [dZ3 md_p md_limbs md_n]. split; [exact UZ4| rewrite repeat_length; clear - HNA; lia].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
    clear UZ3 ZCH3 ZCH4 UZ4 MUd WMd CS3 HH HTc MF SOK MI ST MK ST4 MI4. reopen CS4 HH HTc MF SOK MI ST MK.

    zstep. zstep; if_cases KZ; zify_cond KZ.
    { exfalso. rewrite ?unsigned_lit in KZ by (clear - BA0 BA4 ACP ACV HNA K0; lia). change 3 with (Z.ones 2) in KZ. rewrite Z.land_ones in KZ by lia.
      apply KZ. change (2^2) with 4. clear - BA16. lia. }

    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 2 dZ3 CS4 eq_refl)) 2%nat. intros FLt71 _. flat constr:(FLt71) 2%nat. flclear FLt71. intros FLt72 _. flat constr:(FLt72) 6%nat. flclear FLt72. intros _ _ _ _ _ HOZ5.
    cbn [dZ3 md_own md_p md_n md_limbs] in HOZ5. flat constr:(HOZ5) 4%nat. flclear HOZ5. intros _ _ _ UZ5.
    pose proof (munch_refl [(A, A + 4)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    pose proof (u32arr_store_ok usegs _ A _ 0 _ UZ5 ltac:(rewrite repeat_length; clear - HNA; lia) ltac:(f_equal; lia)) as SOKw.
    zstep.
    replace (A + 0) with (A + 4 * 0) by (clear; lia).
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write usegs _ A _ 0 v UZ5 ltac:(rewrite repeat_length; clear - HNA; lia)) as UZ6 end.
    store_done. try clear SOKw.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    lazymatch type of UZ6 with u32arr _ _ _ ?l => set (zs6 := l) in UZ6 end.
    assert (CS5 : CST m5 mo2 h2 ((A, 4 * (md_n dA + 2)) :: LBq) [set_sg dX 1; set_sg dY 1; set_limbs dZ3 zs6; dT] dR []
                    (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false); [exact CS4| exact MU| exact WM| assumption| assumption| | reflexivity| | | reflexivity| discriminate].
      - constructor; [right; left; exists 2%nat, dZ3; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; cbn [fst snd dZ3 md_p md_n]; clear - HNA; lia| constructor].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          [ do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]
          | | do 6 (split; [reflexivity|]); split; [intros _; reflexivity| intros C; discriminate C]].
        cbn [set_limbs dZ3 md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split; [intros C; exfalso; apply C; split; reflexivity|].
        intros _ _. split; [exact UZ6| subst zs6; rewrite !upd_length, repeat_length; clear - HNA; lia].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros C; discriminate C]. }
    set (dZ5 := set_limbs dZ3 zs6) in CS5.
    assert (ADDRS5 : locals_at [set_sg dX 1; set_sg dY 1; dZ5; dT]) by (unfold locals_at; cbn [map set_sg set_limbs md_addr dZ5 dZ3]; rewrite E0, E1, E2, E3; reflexivity).
    clear MU WM CS4. try clear UZ5. try clear UZ6. reopen CS5 HH HTc MF SOK MI ST MK.

    flat constr:((opnd_facts _ _ _ _ _ _ dA CS5 opndA)) 2%nat. intros ((CSA5 & _) & _) _. unfold mpi_cells in CSA5.
    zstep. rewrite (zx16_small (md_n dA)) by lia.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS5)) 5%nat. intros CG0 CG1 CG2 CGT CGR. unfold t2cells in CG2.
    flat constr:((struct_cells _ _ _ _ _ _ _ 2 dZ5 CS5 eq_refl)) 2%nat. intros CZ5 _. cbn [dZ5 dZ3 set_limbs md_addr md_p md_sg md_n md_pad] in CZ5. rewrite E2 in CZ5. unfold mpi_cells in CZ5.
    pose proof (munch_refl [(SP + -168, SP + -166)] m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    assert (CS6 : CST m6 mo2 h2 ((A, 4 * (md_n dA + 2)) :: LBq) [set_sg dX 1; set_sg dY 1; set_sg dZ5 1; dT] dR []
                    (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (SP + -168) (SP + -166) []);
        [exact CS5| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| | |].
      - intros j d d' Hj Hj'. destruct j as [|[|[|[|j]]]]; cbn in Hj, Hj'; [| | | | destruct j; discriminate Hj]; injection Hj as <-; injection Hj' as <-;
          try (left; split; [cbn [set_sg md_addr]; lia| reflexivity]).
        right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. cbn [dZ5 dZ3 set_limbs md_addr md_p md_n md_pad]. rewrite E2. unfold mpi_cells. assumption.
      - unfold frame, t2cells. constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]; cbn [fst snd]; assumption.
      - apply frame_chs; [| reflexivity| reflexivity| reflexivity]. unfold locals_at. cbn [map set_sg set_limbs md_addr dZ5 dZ3]. rewrite E0, E1, E2, E3. reflexivity. }
    set (dZ6 := set_sg dZ5 1) in CS6.
    assert (ADDRS6 : locals_at [set_sg dX 1; set_sg dY 1; dZ6; dT]) by (unfold locals_at; cbn [map set_sg set_limbs md_addr dZ6 dZ5 dZ3]; rewrite E0, E1, E2, E3; reflexivity).
    clear MU WM CS5. try clear CZ5. try clear CSA5. try clear CG0. try clear CG1. try clear CG2. try clear CGT. try clear CGR. reopen CS6 HH HTc MF SOK MI ST MK.

    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT CS6 eq_refl)) 8%nat. intros MT NST WRT LOT CRT CRTL HFT _.
    pose proof HGROW as SPG. unfold mpi_grow_stmt, U_MPI_GROW in SPG.
    eapply aevtM_cut.
    { eapply SPG with (dX := dT) (nb := md_n dA + 2) (lo := lo) (LB := (A, 4 * (md_n dA + 2)) :: LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc HNA K0; lia).
      all: try (rewrite ?E0, ?E1, ?E2, ?E3; reflexivity). }
    clear SPG. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m7 mo7 h7 LB7 dT4 r E MI7 ST7 MF7 HT7 HH7 MA4 OUT4 PX4 SOK7 RR.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    flat constr:(RR) 2%nat. flclear RR. intros R1 KF4.
    assert (CS7 : CST m7 mo7 h7 LB7 (set_nth 3 [set_sg dX 1; set_sg dY 1; dZ6; dT] dT4) dR []
                    (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64] [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_l; [exact CS6| reflexivity| exact HH7| exact HT7| exact MF7| exact MA4| exact OUT4| exact PX4| exact SOK7| exact MI7| exact ST7| exact KF4]. }
    cbn [set_nth] in CS7.
    flat constr:(OUT4) 3%nat. intros KA4 NS4 _.
    assert (ADDRS4 : locals_at [set_sg dX 1; set_sg dY 1; dZ6; dT4]) by (unfold locals_at; cbn [map set_sg set_limbs md_addr dZ6 dZ5 dZ3]; rewrite KA4, E0, E1, E2, E3; reflexivity).
    assert (Hr : (r = 0 /\ md_n dT4 = md_n dA + 2) \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED).
    { destruct R1 as [(Hr0 & _ & HN & _)|[HrF _]]; [left; split; [exact Hr0| rewrite HN; pose proof MT as [(_ & _ & _ & _ & _ & HO) _]; rewrite OT in HO; (flat constr:(HO) 2%nat; flclear HO; intros _ ->); clear - HNA; lia]| right; exact HrF]. }
    clear MT NST WRT LOT CRT CRTL HFT R1 KF4 MA4 OUT4 PX4 CS6 HH HTc MF SOK MI ST MK.
    reopen CS7 HH HTc MF SOK MI ST MK.

    zstep; if_cases K2; zify_cond K2.
    { eapply L_err; [exact CS7| exact ADDRS4| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia| exact VB]. }
    destruct Hr as [[_ HNT]|Hr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K2; clear - K2; lia]. clear K2.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 3 dT4 CS7 eq_refl)) 3%nat. intros MT4 NST4 _.
    assert (OT4 : md_own dT4 = LHeap) by (eapply out_heap; [exact MT4| exact NST4| rewrite HNT; clear - HNA; lia]).
    eapply (L_m2 A); [exact CS7| exact ADDRS4| cbn; exact OX| cbn; exact OY| reflexivity| reflexivity| exact OT4| rewrite HNT; clear - HNA; lia
      | cbn; exact NYX| cbn [set_sg set_limbs md_n dZ6 dZ5 dZ3]; clear - NXA; lia| reflexivity| reflexivity| | exact VB].
    unfold mpd_val. cbn [set_sg md_sg md_limbs]. fold (mpd_abs dX) (mpd_abs dY). rewrite !Z.mul_1_l, AX, AY. exact VAB.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L11469020189.98 L24928794956.101L33041182163.100L50754888306.100L52972366418.100L59314955108.100L6663987453.100 00000@00R00c01201E01X01hS2sp1d2dS2d'3HN'S2sp1d2dS2d'2N12Z0S2sp1d2dS2d'1T2N1S2sp1d2dS2d'2LRS2sp1d2dS2d'3HN'2NES2sp1d2dS2d'3POS2LRS2sp2dS2d'2HN2N1". (* [comment removed for export] *)
  Lemma copy_local_facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))PLB0,(8.$9.)PLB1,(8.$9.)Pd,$:.PdS,$:.Pd',$:.P,(<.$4<.R6.R4.R1.)P,(1.(2.$0.(53.R3.)+1.)(2.$0.(53.R3.)-1.))P,(>.(2.$?.(10.R3.)$11.))P,(2.$?.(10.R6.)$1<.)P,(2.$0.(19.R7.)=)P,(6>.R7.R8.R:.=R6.)P,(6?.R8.R9.R7.)P,(32.=(61.R9.))(31.(2.$0.(61.R9.)(61.R:.))(31.(31.(1=.+1.(19.R9.))(1=.(19.R9.)(19.R:.)))(31.(2.$?.(10.R9.)$16.)(31.(1.(2.$0.(19.R9.)+1.)(1=.(33.+2.(18.+20.(20.(19.R9.)+1.)))(61.R:.)))(32.(61.R:.)(33.+2.(18.+20.(19.R9.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq LB0 LB1 d dS d' MD SGS NS ON N0 [CR _] TR POS.
    destruct CR as [(_ & HV & HN)|(C & _)]; [| discriminate C].
    flat constr:(MD) 2%nat. intros FLt73 SG. flat constr:(FLt73) 6%nat. flclear FLt73. intros _ _ _ HL HN' HO.
    assert (AB : mpd_abs d' = mpd_abs dS) by (rewrite <- (mpd_val_abs d' SG), <- (mpd_val_abs dS SGS), HV; reflexivity).
    pose proof (mpd_abs_lval d' HL) as AL. pose proof (lval_range (md_limbs d') (md_n d') ltac:(lia)) as LR.
    assert (N1 : 1 <= md_n d').
    { destruct (Z.eq_dec (md_n d') 0) as [E|NE]; [| lia]. exfalso. rewrite <- AL, AB, E in LR. change (2 ^ (32 * 0)) with 1 in LR. lia. }
    split; [exact AB|]. split; [rewrite N0 in HN; lia|]. split.
    - destruct (md_own d') eqn:O; [(flat constr:(HO) 2%nat; flclear HO; intros _ Z0); lia| reflexivity| exfalso; exact (NS eq_refl)].
    - split; [| rewrite <- AB, AL; lia]. unfold copy_trim in TR. rewrite N0 in TR. destruct TR as [T|[T|T]]; [lia| left; exact T| right; exact T].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_ret0 : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (ls : list mpd) (dW : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word) (r : Z)
      (xra x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq ls dW [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    Forall (fun d : mpd => md_own d = LNull) ls -> locals_at ls -> cells_size cs0 = 68%nat -> cells_size tpc = 12%nat ->
    -2^31 < r <= 0 -> 0 < mpd_abs dB ->
    aevtM usegs moq POST
      (MS (mkR xra SPF gp tp t0 t1 t2 x0 x1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21124) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ NUL ADDRS SZ0 SZ1 Hr VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    destruct ls as [|dX [|dY [|dZ [|dT [|]]]]]; try discriminate ADDRS. unfold locals_at in ADDRS. cbn [map] in ADDRS. injection ADDRS as EX EY EZ ET.
    flat constr:((struct_cells _ _ _ _ _ _ _ 0 dX CS_ eq_refl)) 2%nat. intros CX _. flat constr:((struct_cells _ _ _ _ _ _ _ 1 dY CS_ eq_refl)) 2%nat. intros CY _.
    flat constr:((struct_cells _ _ _ _ _ _ _ 2 dZ CS_ eq_refl)) 2%nat. intros CZ _. flat constr:((struct_cells _ _ _ _ _ _ _ 3 dT CS_ eq_refl)) 2%nat. intros CT _.
    rewrite EX in CX. rewrite EY in CY. rewrite EZ in CZ. rewrite ET in CT. unfold mpi_cells in CX, CY, CZ, CT.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ NUL)) 11%nat. intros HH HT MF MW OUT BK PX SOK MI ST CH.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CH1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CH2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as CH3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as CHR.
    cbn [fst snd] in CH0, CH1, CH2, CH3, CHR. clear CH. unfold t2cells in CH2. unfold tcells in CH3.
    do 13 zstep.
    release_frame CH0 ST (bv_unsigned sp + -220). release_frame CH1 ST (bv_unsigned sp + -208). release_frame CH2 ST (bv_unsigned sp + -192).
    release_frame CT ST (bv_unsigned sp + -176). release_frame CZ ST (bv_unsigned sp + -160).
    release_frame CY ST (bv_unsigned sp + -144). release_frame CX ST (bv_unsigned sp + -128).
    release_frame CH3 ST (bv_unsigned sp + -104). release_frame CHR ST (bv_unsigned sp).
    zstep. zstep.
    apply aevtM_done. unfold mpi_binop_post. do 14 eexists. exists mq, moq, hq, LBq, dW, r.
    split; [rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|]. split; [exact HH|]. split; [exact MW|]. split; [exact OUT|].
    split; [exact PX|]. split; [exact SOK|]. split; [split; [exact Hr| intros _; exact VB]| exact BK].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma opnd_sep_w : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PCS,(8.(42.$0.(8.$3<.)))Pd,$:.P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R7.R6.R5.R4.R3.VdR,(4?.$9.)R2.(4?.(42.$0.(8.$3<.))))P,(1.(41.$:.R2.$4;.)(2.$:.R2.VdR,))(31.(=.VdR,R3.)(12.VdR,R3.Vlo,(1>.(13.&40.Vsp,)-120.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls CS d CS_ [IN|E].
    - exact (mc_opnd_sep_we _ _ _ _ _ _ _ _ _ d CS_ IN).
    - rewrite E. exact (mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_early : forall (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (cs0 tpc : list cell) (j68 t160 t164 t168 t176 t180 : word)
      (xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
      (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] -> Forall (fun d : mpd => md_own d = LNull) [dX; dY; dZ; dT] ->
    cells_size cs0 = 68%nat -> cells_size tpc = 12%nat -> 0 < mpd_abs dB ->
    aevtM usegs moq POST
      (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
               x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21084) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ ADDRS NUL SZ0 SZ1 VB.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(facts0) 2%nat. intros R0 _.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((w_cells _ _ _ _ _ _ _ CS_)) 2%nat. intros CW _. pose proof (rw_cells_bound _ _ _ _ CW) as WB. unfold mpi_cells in WB. cbn [cells_size csize Nat.add] in WB. clear CW.
    zstep; if_cases K0; zify_cond K0; [exfalso; clear - K0 R0 WB; rewrite ?Z.mod_small in K0 by lia; lia|].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW NSW EA WR LW CRW CRWL HFW ASW WA8.
    flat constr:((opnd_facts _ _ _ _ _ _ dA CS_ opndA)) 6%nat. intros MA CRA_ CRAL_ LOA HFA ASA.
    flat constr:((opnd_sep_w _ _ _ _ _ _ dA CS_ opndA)) 2%nat. intros SEPWA OPSWA.
    pose proof HCOPY as SPC. unfold mpi_copy_stmt_x, U_MPI_COPY in SPC.
    eapply aevtM_cut.
    { eapply SPC with (dX := dR) (dY := dA) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      apply copy_sep_of_opnd; [exact OPSWA| pose proof MA as [(_ & _ & P0 & _) _]; clear - P0; lia]. }
    clear SPC. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 31%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 (CR & TRIM).
    injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
    replace (ret_pc (Z_to_bv 64 0x21094)) with (Z_to_bv 64 0x21094) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(CR) 4%nat. intros CR1 CAD CPD CFR.
    assert (CS2 : CST m2 mo2 h2 LB2 [dX; dY; dZ; dT] dW2 [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply mc_binop_w; [exact CS_| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact CFR| exact CPD|].
      destruct CR1 as [(_ & _ & NB)|(_ & EN & _)]; lia. }
    assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct CR1 as [(Hr0 & _)|(HrF & _)]; [left; exact Hr0| right; exact HrF]).
    clear CS_ MW MA HH HTc MF SOK MI ST CH MK PX2 OUT2.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS2)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    zstep; if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      eapply L_ret0; [exact CS2| exact NUL| exact ADDRS| exact SZ0| exact SZ1| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia| exact VB].
    - (* [comment removed for export] *)
      eapply L_err; [exact CS2| exact ADDRS| exact SZ0| exact SZ1| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia| exact VB].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma L_main : forall (mq : mem) (j0 j148 : list byte) (t160 t164 t180 : word)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq mo h LB [] dR [] [(SPc, [CB 144 j0; C4 (Z_to_bv 64 0); CB 12 j148]);
      (SP + -128, tcells t160 t164 (Z_to_bv 64 (SP + -144)) (Z_to_bv 64 65537) t180); (SP + -104, REGS)] [] ->
    munch [(lo, SP)] m mq -> wmono usegs m mq ->
    aevtM usegs mo POST (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA))
        (Z_to_bv 64 (Z.sgn (mpd_val dB))) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x20e60) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ MUq WMq.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(MB0) 2%nat. intros _ SGB.
    pose proof (mpd_val_abs dB SGB) as VAL. pose proof (mpd_abs_nonneg dB) as ABN.
    assert (SG3 : (Z.sgn (mpd_val dB) = 0 /\ mpd_abs dB = 0) \/ ((Z.sgn (mpd_val dB) = 1 \/ Z.sgn (mpd_val dB) = -1) /\ 0 < mpd_abs dB)).
    { destruct (Z.lt_trichotomy (mpd_val dB) 0) as [LT|[EQ|GT]].
      - right. split; [right; exact (Z.sgn_neg _ LT)| lia].
      - left. rewrite EQ. split; [reflexivity| lia].
      - right. split; [left; exact (Z.sgn_pos _ GT)| lia]. }
    flat constr:((cs_parts _ _ _ _ _ _ _ CS_)) 8%nat. intros HH1 HT1 MF1 SOK1 MI1 ST1 CH1 MK1.
    (* [comment removed for export] *)
    zstep; if_cases K0; zify_cond K0; rewrite ?Z_to_bv_unsigned in K0; try (unfold bv_wrap in K0; change (bv_modulus 64) with (2^64) in K0).
    - assert (AB0 : mpd_abs dB = 0).
      { destruct SG3 as [(_ & A0)|([E|E] & _)]; [exact A0| rewrite E in K0; exfalso; clear - K0; lia| rewrite E in K0; exfalso; clear - K0; lia]. }
      zstep. zstep.
      flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ ltac:(constructor))) 11%nat. intros HH HT MF MW OUT BK PX SOK MI ST CH.
      pose proof (Forall_inv CH) as CH0. pose proof (Forall_inv (Forall_inv_tail CH)) as CHT.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as CHR. cbn [fst snd] in CH0, CHT, CHR. clear CH. unfold tcells in CHT.
      do 13 zstep.
      release_frame CH0 ST (bv_unsigned sp + -128). release_frame CHT ST (bv_unsigned sp + -104). release_frame CHR ST (bv_unsigned sp).
      zstep. zstep.
      apply aevtM_done. unfold mpi_binop_post. do 14 eexists. exists mq, mo, h, LB, dR, (-12).
      split; [rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
      split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|]. split; [exact HH|]. split; [exact MW|]. split; [exact OUT|].
      split; [exact PX|]. split; [exact SOK|]. split; [split; [clear; lia| intros E'; exfalso; clear - E'; lia]| exact BK].
    - assert (VB : 0 < mpd_abs dB).
      { destruct SG3 as [(E & _)|(_ & V)]; [rewrite E in K0; exfalso; clear - K0; lia| exact V]. }
      (* [comment removed for export] *)
      pose proof (Forall_inv CH1) as FRJ0. pose proof (Forall_inv (Forall_inv_tail CH1)) as FRT.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH1))) as FRR. cbn [fst snd] in FRJ0, FRT, FRR.
      assert (FRJ : rw_cells usegs mq SPc [CB 160 (cells_bytes [CB 144 j0; C4 (Z_to_bv 64 0); CB 12 j148])]).
      { eapply rw_cells_reshape; [exact FRJ0| |].
        - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length by exact (cells_at_wf _ _ _ _ (proj1 FRJ0)). reflexivity.
        - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity. }
      clear FRJ0.
      pose proof (munch_refl [(SPc, SP + -128)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
      pose proof (conj HH1 (conj SOK1 (conj MI1 ST1))) as PROT1.
      do 14 zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      rename HH1 into HH2. rename SOK1 into SOK2. rename MI1 into MI2. rename ST1 into ST2.
      flat constr:(PROT1) 4%nat. flclear PROT1. intros HH1 SOK1 MI1 ST1.
      lazymatch type of FRJ with rw_cells _ _ _ (CB 80 ?a :: _ :: _ :: CB 4 ?b :: _ :: _ :: CB 4 ?c :: _ :: _ :: CB 4 ?d :: _ :: _ :: CB 4 ?e :: _ :: _ :: CB 4 ?f :: _) =>
        set (J := a) in FRJ; set (j68 := b) in FRJ; set (jT := c) in FRJ; set (jZ := d) in FRJ; set (jY := e) in FRJ; set (jX := f) in FRJ end.
      pose proof (rw_cells_split_CB usegs m2 _ [] 80 J _ [8;8;8;8;8;8;8;8;4;4;4;4]%nat FRJ eq_refl) as FR2. cbn [mk_CB_cells app] in FR2. clear FRJ.
      apply (rw_cells_CB8_C8 usegs m2 _ [_]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB8_C8 usegs m2 _ [_; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB8_C8 usegs m2 _ [_; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB8_C8 usegs m2 _ [_; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB8_C8 usegs m2 _ [_; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB8_C8 usegs m2 _ [_; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB8_C8 usegs m2 _ [_; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB4_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB4_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB4_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_split_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_C2_mod16 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 196609) / 2 ^ 16)) with (Z_to_bv 64 3) in FR2 by (rewrite unsigned_lit by (clear; lia); reflexivity).
      change (196609 mod 2 ^ 16) with 1 in FR2.
      apply (rw_cells_CB4_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_split_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB4_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_split_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB4_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_split_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB4_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_split_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      apply (rw_cells_CB4_C4 usegs m2 _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]) in FR2. cbn [app] in FR2.
      replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16)) with (Z_to_bv 64 0) in FR2 by (rewrite unsigned_lit by (clear; lia); reflexivity).
      take FR2 9%nat CF0. take FR2 3%nat CF1. take FR2 4%nat CF2. take FR2 4%nat CT. take FR2 4%nat CZ. take FR2 4%nat CY. rename FR2 into CX.
      lazymatch type of CF0 with rw_cells _ _ _ ?c => set (cs0 := c) in CF0 end.
      lazymatch type of CF1 with rw_cells _ _ _ ?c => set (tpc := c) in CF1 end.
      set (dX0 := mkMPD (SP + -144) 1 0 0 [] (wof jX) LNull). set (dY0 := mkMPD (SP + -160) 1 0 0 [] (wof jY) LNull).
      set (dZ0 := mkMPD (SP + -176) 1 0 0 [] (wof jZ) LNull). set (dT0 := mkMPD (SP + -192) 1 0 0 [] (wof jT) LNull).
      assert (ADDRS0 : locals_at [dX0; dY0; dZ0; dT0]) by reflexivity.
      assert (MU2 : munch [(lo, SP)] m m2).
      { first [exact MUq| (eapply munch_trans; [exact MUq|]; eapply munch_weaken; [| exact MU]; intros x Hx; cbn in Hx |- *; clear - Hx SLO HLS; lia)]. }
      assert (WM2 : wmono usegs m m2) by first [exact WMq| exact (wmono_trans _ _ _ _ WMq WM)].
      assert (ESA : Forall (fun e => mpd_at usegs m LB e) es).
      { unfold es. destruct ALIAS; [constructor; [exact MB0| constructor]| constructor; [exact MA0| constructor; [exact MB0| constructor]]]. }
      assert (CS2 : CST m2 mo h LB [dX0; dY0; dZ0; dT0] dR []
                      (frame cs0 tpc (wof j68) (tcells t160 t164 (Z_to_bv 64 (SP + -144)) (Z_to_bv 64 65537) t180)) []).
      { eapply mc_init; [exact HH0| exact SOK0| exact MI0| exact MR0| exact ESA| exact MU2| exact WM2| exact MI2| exact ST2| | | |].
        - subst dX0 dY0 dZ0 dT0. unfold mpi_cells.
          repeat (constructor; [cbn [md_addr md_own md_p md_n md_limbs md_sg md_pad]; split; [assumption|]; repeat (split; [first [reflexivity| clear - SPA SPB SLO HLS; lia]|]); clear - SPA; lia|]). constructor.
        - subst dX0 dY0 dZ0 dT0. intros i j di dj Hi Hj NE.
          destruct i as [|[|[|[|i]]]]; cbn in Hi; [| | | | destruct i; discriminate Hi]; injection Hi as <-;
          destruct j as [|[|[|[|j]]]]; cbn in Hj; try (destruct j; discriminate Hj); injection Hj as <-; cbn [md_addr]; clear - NE; lia.
        - unfold frame, t2cells. constructor; [exact CF0| constructor; [exact CF1| constructor; [exact CF2| constructor; [exact FRT| constructor; [exact FRR| constructor]]]]].
        - apply frame_chs; [exact ADDRS0| reflexivity| reflexivity| reflexivity]. }
      assert (E0 : md_addr dX0 = SP + -144) by reflexivity. assert (E1 : md_addr dY0 = SP + -160) by reflexivity.
      assert (E2 : md_addr dZ0 = SP + -176) by reflexivity. assert (E3 : md_addr dT0 = SP + -192) by reflexivity.
      assert (OX : md_own dX0 = LNull) by reflexivity. assert (OY : md_own dY0 = LNull) by reflexivity.
      assert (OZ : md_own dZ0 = LNull) by reflexivity. assert (OT : md_own dT0 = LNull) by reflexivity.
      assert (NX0 : md_n dX0 = 0) by reflexivity. assert (NY0 : md_n dY0 = 0) by reflexivity.
      assert (NUL0 : Forall (fun d : mpd => md_own d = LNull) [dX0; dY0; dZ0; dT0]) by (repeat constructor).
      clearbody dX0 dY0 dZ0 dT0.
      clear CF0 CF1 CF2 CT CZ CY CX FRT FRR MU WM MU2 WM2 HH2 SOK2 MI2 ST2 CS_ HH1 HT1 MF1 SOK1 MI1 ST1 CH1 MK1.
      flat constr:((cs_parts _ _ _ _ _ _ _ CS2)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
      flat constr:((opnd_facts _ _ _ _ _ _ dA CS2 opndA)) 6%nat. intros MA _ _ _ HFA _.
      flat constr:((opnd_facts _ _ _ _ _ _ dB CS2 (or_introl opndB))) 6%nat. intros MB _ _ _ HFB _.
      flat constr:(MA) 2%nat. intros _ SGA.
      assert (SGC : (Z.sgn (mpd_abs dA - mpd_abs dB) = -1 /\ mpd_abs dA < mpd_abs dB) \/
                    ((Z.sgn (mpd_abs dA - mpd_abs dB) = 0 \/ Z.sgn (mpd_abs dA - mpd_abs dB) = 1) /\ mpd_abs dB <= mpd_abs dA)).
      { destruct (Z.lt_trichotomy (mpd_abs dA - mpd_abs dB) 0) as [LT|[EQ|GT]].
        - left. split; [exact (Z.sgn_neg _ LT)| lia].
        - right. rewrite EQ. split; [left; reflexivity| lia].
        - right. split; [right; exact (Z.sgn_pos _ GT)| lia]. }
      zstep. zstep. zstep.
      pose proof HCABS as SPC. unfold mpi_cmp_abs_stmt, U_MPI_CMP_ABS in SPC.
      eapply aevtM_cut_evt; [exact MK| eapply SPC with (LB := LB) (dX := dA) (dY := dB); try eassumption; try reflexivity|].
      all: try (intros O; flat constr:((HFA O)) 2%nat; intros P0 _; exact P0).
      all: try (intros O; flat constr:((HFB O)) 2%nat; intros P0 _; exact P0).
      clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO.
      flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
      replace (ret_pc (Z_to_bv 64 0x20ea8)) with (Z_to_bv 64 0x20ea8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep; if_cases K1; zify_cond K1; rewrite ?Z_to_bv_unsigned in K1; try (unfold bv_wrap in K1; change (bv_modulus 64) with (2^64) in K1).
      { zstep; if_cases KQ; zify_cond KQ; [| exfalso; apply KQ; reflexivity].
        eapply L_early; [exact CS2| exact ADDRS0| exact NUL0| reflexivity| reflexivity| exact VB]. }
      assert (VAB : 0 < mpd_abs dB <= mpd_abs dA).
      { destruct SGC as [(E & _)|(_ & GE)]; [rewrite E in K1; exfalso; clear - K1; lia| lia]. }
      clear SGC K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dX0 CS2 eq_refl)) 8%nat. intros MX NSX WRX LOX CRX CRXL HFX _.
      flat constr:((opnd_facts _ _ _ _ _ _ dA CS2 opndA)) 6%nat. intros MA' CRA_ CRAL_ LOA HFA' ASA.
      flat constr:((opnd_sep_l _ _ _ _ _ _ 0 dX0 dA CS2 eq_refl opndA)) 2%nat. intros SEP0A OPS0A.
      pose proof HCOPY as SPC. unfold mpi_copy_stmt_x, U_MPI_COPY in SPC.
      eapply aevtM_cut.
      { eapply SPC with (dX := dX0) (dY := dA) (lo := lo) (h := h) (LB := LB); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
        all: try (rewrite ?E0, ?E1, ?E2, ?E3; reflexivity).
        apply copy_sep_of_opnd; [exact OPS0A| pose proof MA' as [(_ & _ & P0 & _) _]; clear - P0; lia]. }
      clear SPC. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      flat constr:(PO) 31%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 mo3 h3 LB3 dX3 r E MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 (CR & TRIM).
      injection E as -> ->. rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in PX3 by lia.
      replace (ret_pc (Z_to_bv 64 0x20eb8)) with (Z_to_bv 64 0x20eb8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(CR) 4%nat. intros CR1 CAD CPD CFR.
      assert (CS3 : CST m3 mo3 h3 LB3 (set_nth 0 [dX0; dY0; dZ0; dT0] dX3) dR []
                      (frame cs0 tpc (wof j68) (tcells t160 t164 (Z_to_bv 64 (SP + -144)) (Z_to_bv 64 65537) t180)) []).
      { eapply mc_binop_l; [exact CS2| reflexivity| exact HH3| exact HT3| exact MF3| exact MA3| exact OUT3| exact PX3| exact SOK3| exact MI3| exact ST3| exact CFR]. }
      cbn [set_nth] in CS3.
      assert (ADDRS3 : locals_at [dX3; dY0; dZ0; dT0]) by (unfold locals_at; cbn [map]; rewrite CAD, E0, E1, E2, E3; reflexivity).
      assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct CR1 as [(Hr0 & _)|(HrF & _)]; [left; exact Hr0| right; exact HrF]).
      flat constr:(OUT3) 3%nat. intros _ NS3 _.
      clear MX NSX WRX LOX CRX CRXL HFX MA' CRA_ CRAL_ LOA HFA' ASA SEP0A OPS0A CS2 HH HTc MF SOK MI ST MK PX3 OUT3.
      reopen CS3 HH HTc MF SOK MI ST MK.
      zstep; if_cases K2; zify_cond K2.
      { eapply L_err; [exact CS3| exact ADDRS3| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia| exact VB]. }
      assert (Hr0 : r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr K2; lia). subst r. clear Hr K2.
      destruct (copy_local_facts _ _ _ _ _ _ MA3 SGA NS3 OX NX0 CR (TRIM eq_refl) ltac:(clear - VAB; lia)) as (AX & NX3 & OX3 & TRX & BX).
      clear CR TRIM CR1 CFR MA3.
      zstep. zstep. zstep.
      flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 1 dY0 CS3 eq_refl)) 8%nat. intros MY NSY WRY LOY CRY CRYL HFY _.
      flat constr:((opnd_facts _ _ _ _ _ _ dB CS3 (or_introl opndB))) 6%nat. intros MB' CRB_ CRBL_ LOB HFB' ASB.
      flat constr:((opnd_sep_l _ _ _ _ _ _ 1 dY0 dB CS3 eq_refl (or_introl opndB))) 2%nat. intros SEP1B OPS1B.
      pose proof HCOPY as SPC. unfold mpi_copy_stmt_x, U_MPI_COPY in SPC.
      eapply aevtM_cut.
      { eapply SPC with (dX := dY0) (dY := dB) (lo := lo) (h := h3) (LB := LB3); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
        all: try (rewrite ?E0, ?E1, ?E2, ?E3; reflexivity).
        apply copy_sep_of_opnd; [exact OPS1B| pose proof MB' as [(_ & _ & P0 & _) _]; clear - P0; lia]. }
      clear SPC. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      flat constr:(PO) 31%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m4 mo4 h4 LB4 dY4 r E MI4 ST4 MF4 HT4 HH4 MA4 OUT4 PX4 SOK4 (CR & TRIM).
      injection E as -> ->. rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in PX4 by lia.
      replace (ret_pc (Z_to_bv 64 0x20ec8)) with (Z_to_bv 64 0x20ec8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(CR) 4%nat. intros CR1 CAD4 CPD4 CFR4.
      assert (CS4 : CST m4 mo4 h4 LB4 (set_nth 1 [dX3; dY0; dZ0; dT0] dY4) dR []
                      (frame cs0 tpc (wof j68) (tcells t160 t164 (Z_to_bv 64 (SP + -144)) (Z_to_bv 64 65537) t180)) []).
      { eapply mc_binop_l; [exact CS3| reflexivity| exact HH4| exact HT4| exact MF4| exact MA4| exact OUT4| exact PX4| exact SOK4| exact MI4| exact ST4| exact CFR4]. }
      cbn [set_nth] in CS4.
      assert (ADDRS4 : locals_at [dX3; dY4; dZ0; dT0]) by (unfold locals_at; cbn [map]; rewrite CAD4, CAD, E0, E1, E2, E3; reflexivity).
      assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct CR1 as [(Hr0 & _)|(HrF & _)]; [left; exact Hr0| right; exact HrF]).
      flat constr:(OUT4) 3%nat. intros _ NS4 _.
      clear MY NSY WRY LOY CRY CRYL HFY MB' CRB_ CRBL_ LOB HFB' ASB SEP1B OPS1B CS3 HH HTc MF SOK MI ST MK PX4 OUT4.
      reopen CS4 HH HTc MF SOK MI ST MK.
      zstep; if_cases K3; zify_cond K3.
      { eapply L_err; [exact CS4| exact ADDRS4| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr; lia| exact VB]. }
      assert (Hr0 : r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; clear - Hr K3; lia). subst r. clear Hr K3.
      flat constr:(MB) 2%nat. intros _ SGB'.
      destruct (copy_local_facts _ _ _ _ _ _ MA4 SGB' NS4 OY NY0 CR (TRIM eq_refl) ltac:(clear - VAB; lia)) as (AY & NY4 & OY4 & TRY & BY).
      eapply L_m1; [exact CS4| exact ADDRS4| exact OX3| exact OY4| exact OZ| exact OT| | clear - NX3; lia| exact AX| exact AY| exact VAB].
      destruct TRY as [T1|T2]; [clear - T1 NX3; lia|].
      assert (LT : 2 ^ (32 * (md_n dY4 - 1)) < 2 ^ (32 * md_n dX3)) by (clear - T2 BX VAB; lia).
      apply Z.pow_lt_mono_r_iff in LT; clear - LT NX3 NY4; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma es_at : Forall (fun e => mpd_at usegs m LB e) es.
  Proof. unfold es. destruct ALIAS; [constructor; [exact MB0| constructor]| constructor; [exact MA0| constructor; [exact MB0| constructor]]]. Qed.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "".
  Lemma div_val_T0 : forall a p pd own, mpd_val (mkMPD a 1 1 p [Z_to_bv 64 0] pd own) = 0.
  Proof. intros. unfold mpd_val. cbn [md_sg md_limbs]. vm_compute. reflexivity. Qed.

  Lemma div_T_opnd : forall (mm : mem) (P Q SPx : Z) (w : word),
    rw_cells usegs mm P [C4 (Z_to_bv 64 0)] ->
    rw_cells usegs mm Q [C8 (Z_to_bv 64 P); C4 (Z_to_bv 64 65537); C4 w] ->
    0 < Q -> Q mod 8 = 0 -> 0 < P -> P mod 4 = 0 -> SPx <= P -> P + 4 < 2^64 ->
    stack_opnd usegs mm SPx (mkMPD Q 1 1 P [Z_to_bv 64 0] w LStatic).
  Proof.
    intros mm P Q SPx w FL FT Q0 Q8 P0 P4 HS HB.
    pose proof FL as [[_ BL] _].
    unfold stack_opnd. cbn [md_own md_addr md_sg md_n md_p md_limbs md_pad].
    split; [reflexivity|]. split.
    { unfold mpi_cells. eapply rw_cells_reshape; [exact FT| cbn; tauto|].
      cbn [cells_bytes cbytes]. f_equal. rewrite app_assoc. f_equal. unfold le2, le4. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
      refine (f_equal2 (@cons (bv 8)) _ (f_equal2 (@cons (bv 8)) _ (f_equal2 (@cons (bv 8)) _ (f_equal2 (@cons (bv 8)) _ eq_refl))));
        apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity. }
    split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BL|]. split; [lia|]. split; [lia|].
    left; reflexivity.
  Qed.

  Local Ltac div_cb4_first H :=
    lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
      let rec go pre l := lazymatch l with
        | CB 4 ?bs :: ?post => apply (rw_cells_CB4_C4 sg mm A pre bs post) in H
        | ?c :: ?rest => go (pre ++ [c]) rest
        end in go (@nil cell) cs
    end; cbn [app] in H.

  Lemma L_div : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    aevtM usegs mo POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dB)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20df4) fc None m (seg_rom usegs)).
  Proof.
    intros.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(facts0) 8%nat. intros R0 R8 RAS RBLK HBR _ _ _.
    pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK.
    pose proof ST0 as ST. pose proof MI0 as MI. pose proof es_at as ESA.
    carve_frame 288%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 288, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    set (mI := m) in HH0, MR0, MA0, MB0, MI0, SOK0, ST0, ESA.
    do 27 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 144 ?ja :: _ :: CB 20 ?jb :: _ :: _ :: CB 4 ?jc :: _) =>
      set (j0 := ja) in FR; set (j20 := jb) in FR; set (j180 := jc) in FR end.
    apply (rw_cells_split_CB usegs m1 _ [CB 144 j0; C4 (Z_to_bv 64 0)] 20 j20 _ [12; 4; 4]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    set (j148 := firstn 12 j20) in FR.
    div_cb4_first FR. div_cb4_first FR. div_cb4_first FR.
    set (t160 := le_bytes_to_word (firstn 4 (skipn 12 j20))) in FR.
    set (t164 := le_bytes_to_word (firstn 4 (skipn 4 (skipn 12 j20)))) in FR.
    set (t180 := le_bytes_to_word j180) in FR.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?rest) =>
      destruct (rw_cells_split3 usegs m1 _ [c1; c2; c3] [c4; c5; c6; c7; c8] rest FR) as (F1 & F2 & F3) end.
    cbn [cells_size csize Nat.add] in F2, F3.
    lazymatch type of F2 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -128) in F2 by (clear; lia) end.
    lazymatch type of F3 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -104) in F3 by (clear; lia) end.
    lazymatch type of F1 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: []) =>
      destruct (rw_cells_split3 usegs m1 _ [c1] [c2] [c3] F1) as (_ & FL & _) end.
    lazymatch type of F2 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: []) =>
      destruct (rw_cells_split3 usegs m1 _ [c1; c2] [c3; c4; c5] [] F2) as (_ & FT & _) end.
    cbn [cells_size csize Nat.add] in FL, FT.
    lazymatch type of FL with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -144) in FL by (clear; lia) end.
    lazymatch type of FT with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -120) in FT by (clear; lia) end.
    assert (MU1 : munch [(lo, SP)] m m1).
    { eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. clear - Hx SLO HLS. lia. }
    pose proof HH0 as HH0'. pose proof SOK0 as SOK0'. pose proof MI0 as MI0'. pose proof MR0 as MR0'. unfold mI in HH0', SOK0', MI0', MR0', ESA.
    assert (CS1 : CST m1 mo h LB [] dR [] [(SPc, [CB 144 j0; C4 (Z_to_bv 64 0); CB 12 j148]); (SP + -128, tcells t160 t164 (Z_to_bv 64 (SP + -144)) (Z_to_bv 64 65537) t180); (SP + -104, REGS)] []).
    { eapply mc_init; [exact HH0'| exact SOK0'| exact MI0'| exact MR0'| exact ESA| exact MU1| exact WM| exact MI| exact ST| constructor| | |].
      - intros i j di dj Hi. destruct i; discriminate Hi.
      - constructor; [exact F1| constructor; [exact F2| constructor; [exact F3| constructor]]].
      - constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd tcells cells_size csize Nat.add]; (split; [clear; lia| split; [clear; lia| intros d []]]). }
    clear FR F1 F2 F3 MU. rename WM into WM1.
    flat constr:((cs_parts _ _ _ _ _ _ _ CS1)) 8%nat. intros HH1 HT1 MF1 SOK1 MI1 ST1 CH1 MK1.
    flat constr:((opnd_facts _ _ _ _ _ _ dB CS1 (or_introl opndB))) 6%nat. intros MB _ _ _ HFB _.
    pose proof HCMPO as SPC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in SPC.
    eapply aevtM_cut_evt; [exact MK1| eapply SPC with (LB := LB) (dX := dB) (dY := mkMPD (SP + -120) 1 1 (SP + -144) [Z_to_bv 64 0] t180 LStatic);
      [ apply opnd_at_mpd; exact MB
      | right; rewrite unsigned_lit by lia; eapply div_T_opnd; [exact FL| exact FT| lia ..]
      | intros O; exact (proj1 (HFB O))
      | cbn; intros O; discriminate O
      | exact MI1
      | reflexivity
      | reflexivity ]|].
    clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO.
    flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x20e60)) with (Z_to_bv 64 0x20e60) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite div_val_T0, Z.sub_0_r.
    eapply L_main; [exact CS1| exact MU1| exact WM1].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Walk.

  Theorem U_mpi_div_mpi_ok : mpi_div_mpi_stmt usegs L HI U_MPI_DIV_MPI MSF.
  Proof.
    unfold mpi_div_mpi_stmt, U_MPI_DIV_MPI. intros until lo.
    intros HH MX MA MB SXA SXB SAB NSX NEB OPA OPB CRA CRAL CRB CRBL WRX XLO ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    eapply L_div; eassumption.
  Qed.
End DivP.
