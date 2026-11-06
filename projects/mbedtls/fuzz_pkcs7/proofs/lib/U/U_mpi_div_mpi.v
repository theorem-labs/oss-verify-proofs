(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts MpiOpnd. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiClient.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_copy U_mpi_shift_l U_mpi_cmp U_mpi_lset U_mpi_mul_int_W U_mpi_core_bitlen U_mpi_core_shift_r U_mpi_shift_r U_mpi_cmp_abs U_mpi_divmod_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_div_mpi () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.U.U_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.U.U_mpi_addsub.mpd_writable"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.HeapIface.hl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.U.U_mpi_addsub.mpi_binop_post"; "OSSVerify.KrLib.U.U_mpi_addsub.add_sub_mpi_R"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.U.U_mpi_mul_int_W.mul_int_R"; "OSSVerify.KrLib.U.U_mpi_divmod_stmt.div_mpi_rem_R"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Lib.MpiCoreAux.core_bitlen"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "OSSVerify.KrLib.U.U_mpi_shift_l.shift_l_n"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.C2"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.bool"; "DivP.Walk.ALIAS"; "Corelib.Init.Datatypes.true"; "DivP.Walk.es"; "OSSVerify.KrLib.U.UImg.usegs"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.USpec.MpiClient.cstate"; "Corelib.Init.Datatypes.nil"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.Spec.Rep.MPI_MAX_LIMBS"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.Lib.AEvt.MOK"; "DivP.Walk.locals_at"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "Stdlib.ZArith.BinInt.Z.of_nat"; "DivP.Walk.frame"; "DivP.Walk.t2cells"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Cells.CB"; "DivP.Walk.loop_loc"; "DivP.Walk.set_limbs"; "DivP.Walk.lframe"; "DivP.Walk.KONT"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Stdlib.ZArith.BinInt.Z.to_nat"; "DivP.Walk.ISTATE"; "OSSVerify.KrLib.Lib.MpiCoreAux.sxz"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "OSSVerify.KrLib.U.U_mpi_copy.copy_R"; "OSSVerify.KrLib.U.U_mpi_copy.copy_trim"; "OSSVerify.KrLib.U.U_mpi_cmp.SIGF"; "Stdlib.ZArith.BinInt.Z.sgn"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"].


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
  Notation SPc := (SP + -288).
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
  Local Ltac mc_inst X :=
    refine (X usegs L HI HLS DIMG HND IMGC SW ROIMG h LB mo m SP lo SPc dR es ACL _ _ HTOP
              (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0))))))) DHI NSR WRR
              (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok);
    [ clear - SLO HLS; lia | clear - sp; lia ].
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

  Notation SPF := (Z_to_bv 64 SPc).
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
  Proof using ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
    intros ls cs0 tpc j68 tcs LOCS SZ0 SZ1 SZ2.
    assert (ADDRS : forall d, In d ls -> SP + -192 <= md_addr d /\ md_addr d + 16 <= SP + -128).
    { intros d IN. apply (in_map md_addr) in IN. unfold locals_at in LOCS. rewrite LOCS in IN. cbn in IN. lia. }
    unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]];
      cbn [fst snd]; rewrite ?SZ0, ?SZ1, ?SZ2; cbn [cells_size csize t2cells Nat.add];
      (split; [lia| split; [lia|]]); intros d IN; pose proof (ADDRS d IN); lia.
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
    intros mq moq hq LBq ls dW cs0 tpc j68 tcs STq.
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (_ & _ & _ & _ & _ & _ & CELLS & _).
    unfold frame in CELLS.
    pose proof (Forall_inv CELLS) as C0. pose proof (Forall_inv_tail CELLS) as R1.
    pose proof (Forall_inv R1) as C1. pose proof (Forall_inv_tail R1) as R2.
    pose proof (Forall_inv R2) as C2. pose proof (Forall_inv_tail R2) as R3.
    pose proof (Forall_inv R3) as C3. pose proof (Forall_inv (Forall_inv_tail R3)) as C4'.
    cbn [fst snd] in C0, C1, C2, C3, C4'.
    split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3| exact C4'].
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
    intros mq moq hq LBq ls dW cs0 tpc j68 tcs flo fhi m1 cs0' tpc' STq LOCS MU1 WM1 MI1 ST1 FLO FHI NC0 SZ0 NTP SZ1 SZ2.
    assert (ADDRS : forall d, In d ls -> SP + -192 <= md_addr d /\ md_addr d + 16 <= SP + -128).
    { intros d IN. apply (in_map md_addr) in IN. unfold locals_at in LOCS. rewrite LOCS in IN. cbn in IN. lia. }
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ STq) as (Fcs0 & Ftpc & Ft2 & Ftc & REGq).
    apply (mc_hi_write mq moq hq LBq ls dW [] _ [] flo fhi [] m1 ls _ STq MU1 WM1 MI1 ST1);
      [lia | lia | constructor | reflexivity | | | ].
    - intros j d d' Ej Ej'. left. rewrite Ej in Ej'. injection Ej' as <-. split; [| reflexivity].
      pose proof (ADDRS d (nth_error_In _ _ Ej)). lia.
    - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd].
      + exact NC0.
      + exact NTP.
      + eapply rw_cells_transport; [exact Ft2| exact MU1| exact WM1|]. cbn. lia.
      + eapply rw_cells_transport; [exact Ftc| exact MU1| exact WM1|]. rewrite SZ2. cbn. lia.
      + eapply rw_cells_transport; [exact REGq| exact MU1| exact WM1|]. cbn. lia.
    - apply frame_chs; assumption.
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
    intros mq moq hq LBq ls dW cs0 tpc j68 tcs flo fhi m1 tcs' STq LOCS MU1 WM1 MI1 ST1 FLO FHI NTC SZ2 SZ0 SZ1.
    assert (ADDRS : forall d, In d ls -> SP + -192 <= md_addr d /\ md_addr d + 16 <= SP + -128).
    { intros d IN. apply (in_map md_addr) in IN. unfold locals_at in LOCS. rewrite LOCS in IN. cbn in IN. lia. }
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ STq) as (Fcs0 & Ftpc & Ft2 & Ftc & REGq).
    apply (mc_hi_write mq moq hq LBq ls dW [] _ [] flo fhi [] m1 ls _ STq MU1 WM1 MI1 ST1);
      [lia | lia | constructor | reflexivity | | | ].
    - intros j d d' Ej Ej'. left. rewrite Ej in Ej'. injection Ej' as <-. split; [| reflexivity].
      pose proof (ADDRS d (nth_error_In _ _ Ej)). lia.
    - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd].
      + eapply rw_cells_transport; [exact Fcs0| exact MU1| exact WM1|]. rewrite SZ0. cbn. lia.
      + eapply rw_cells_transport; [exact Ftpc| exact MU1| exact WM1|]. rewrite SZ1. cbn. lia.
      + eapply rw_cells_transport; [exact Ft2| exact MU1| exact WM1|]. cbn. lia.
      + exact NTC.
      + eapply rw_cells_transport; [exact REGq| exact MU1| exact WM1|]. cbn. lia.
    - apply frame_chs; assumption.
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
    intros mq moq hq LBq ls dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 STq ALLNUL LOCS SZcs SZtp RRANGE BPOS.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ STq) as (Fcs0 & Ftpc & Ft2 & Ftc & REGq).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    assert (FRlo : 0 <= SP + -288) by lia.
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (HPq & TOPq & FRMq & SOKq & MIq & STKq & _ & MOKq).
    pose proof (mc_final _ _ _ _ _ _ _ _ STq ALLNUL) as (_ & _ & _ & MWq & OUTq & KEEPq & PXq & _).
    assert (STKfull : stk usegs mq lo SP).
    { destruct STq as (_ & _ & _ & LOKq & _).
      unfold locals_at in LOCS.
      destruct ls as [|dX [|dY [|dZ [|dT [|dE rest]]]]]; try discriminate LOCS.
      cbn in LOCS. injection LOCS as AX AY AZ AT.
      pose proof (Forall_inv LOKq) as LX. pose proof (Forall_inv_tail LOKq) as LOK1.
      pose proof (Forall_inv LOK1) as LY. pose proof (Forall_inv_tail LOK1) as LOK2.
      pose proof (Forall_inv LOK2) as LZ. pose proof (Forall_inv (Forall_inv_tail LOK2)) as LT.
      destruct LX as (((CX & _) & _) & _). destruct LY as (((CY & _) & _) & _).
      destruct LZ as (((CZ & _) & _) & _). destruct LT as (((CT & _) & _) & _).
      rewrite AX in CX. rewrite AY in CY. rewrite AZ in CZ. rewrite AT in CT.
      apply (stk_release _ _ _ _ _ STKq) in Fcs0; [| lia]. rewrite SZcs in Fcs0.
      replace (SP + -288 + Z.of_nat 68) with (SP + -220) in Fcs0 by lia.
      apply (stk_release _ _ _ _ _ Fcs0) in Ftpc; [| lia]. rewrite SZtp in Ftpc.
      replace (SP + -220 + Z.of_nat 12) with (SP + -208) in Ftpc by lia.
      apply (stk_release _ _ _ _ _ Ftpc) in Ft2; [| lia]. cbn [cells_size csize t2cells Nat.add] in Ft2.
      replace (SP + -208 + Z.of_nat 16) with (SP + -192) in Ft2 by lia.
      apply (stk_release _ _ _ _ _ Ft2) in CT; [| lia]. cbn [cells_size csize mpi_cells Nat.add] in CT.
      replace (SP + -192 + Z.of_nat 16) with (SP + -176) in CT by lia.
      apply (stk_release _ _ _ _ _ CT) in CZ; [| lia]. cbn [cells_size csize mpi_cells Nat.add] in CZ.
      replace (SP + -176 + Z.of_nat 16) with (SP + -160) in CZ by lia.
      apply (stk_release _ _ _ _ _ CZ) in CY; [| lia]. cbn [cells_size csize mpi_cells Nat.add] in CY.
      replace (SP + -160 + Z.of_nat 16) with (SP + -144) in CY by lia.
      apply (stk_release _ _ _ _ _ CY) in CX; [| lia]. cbn [cells_size csize mpi_cells Nat.add] in CX.
      replace (SP + -144 + Z.of_nat 16) with (SP + -128) in CX by lia.
      apply (stk_release _ _ _ _ _ CX) in Ftc; [| lia]. cbn [cells_size csize tcells Nat.add] in Ftc.
      replace (SP + -128 + Z.of_nat 24) with (SP + -104) in Ftc by lia.
      apply (stk_release _ _ _ _ _ Ftc) in REGq; [| lia]. cbn [cells_size csize Nat.add] in REGq.
      replace (SP + -104 + Z.of_nat 104) with SP in REGq by lia. exact REGq. }
    do 16 zstep.
    apply aevtM_done. unfold mpi_binop_post.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, mq, moq, hq, LBq, dW, r.
    split; [reflexivity|]. split; [exact MIq|]. split; [exact STKfull|]. split; [exact FRMq|].
    split; [exact TOPq|]. split; [exact HPq|]. split; [exact MWq|]. split; [exact OUTq|].
    split; [exact PXq|]. split; [exact SOKq|].
    split; [split; [exact RRANGE| intros _; exact BPOS]| exact KEEPq].
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
    intros mq moq hq LBq ls dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 STq ALLNUL LOCS SZcs SZtp RRANGE BPOS.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ STq) as (Fcs0 & Ftpc & Ft2 & Ftc & REGq).
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (HPq & TOPq & FRMq & SOKq & MIq & STKq & _ & MOKq).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    do 3 zstep.
    destruct (rw_cells_forget _ _ _ _ Ftpc) as [old Fold]. rewrite SZtp in Fold.
    pose proof HPZ as PZ. unfold platform_zeroize_stmt, U_PLATFORM_ZEROIZE in PZ.
    eapply aevtM_cut_evt; [exact MOKq | eapply PZ with (A := SP + -220) (n := 12) (lo := lo) (junk := old);
      rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity; lia |].
    intros ms' PO. unfold platform_zeroize_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MU2 & WM2 & MI2 & ZR2 & ST2 & SOK2).
    rewrite ?(unsigned_lit (SP + -288)) in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 135456)) with (Z_to_bv 64 135456) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (ADDRS : forall d, In d ls -> SP + -192 <= md_addr d /\ md_addr d + 16 <= SP + -128).
    { intros d IN. apply (in_map md_addr) in IN. unfold locals_at in LOCS. rewrite LOCS in IN.
      cbn in IN. lia. }
    assert (CS2 : cstate usegs L HI h LB mo m SP lo SPc dR es m2 moq hq LBq ls dW []
                    (frame cs0 [CB (Z.to_nat 12) (repeat (Z_to_bv 8 0) (Z.to_nat 12))] j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_hi_write mq moq hq LBq ls dW [] _ [] (SP + -220) (SP + -220 + 12) [(SP + -288 - 16, SP + -288)] m2 ls _ STq MU2 WM2 MI2 ST2);
        [lia | lia | constructor; [cbn; lia| constructor] | reflexivity | | | ].
      - intros j d d' Ej Ej'. left. rewrite Ej in Ej'. injection Ej' as <-. split; [| reflexivity].
        pose proof (ADDRS d (nth_error_In _ _ Ej)). lia.
      - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd].
        + eapply rw_cells_transport; [exact Fcs0| exact MU2| exact WM2|]. rewrite SZcs. cbn. lia.
        + exact ZR2.
        + eapply rw_cells_transport; [exact Ft2| exact MU2| exact WM2|]. cbn. lia.
        + eapply rw_cells_transport; [exact Ftc| exact MU2| exact WM2|]. cbn. lia.
        + eapply rw_cells_transport; [exact REGq| exact MU2| exact WM2|]. cbn. lia.
      - apply frame_chs; [exact LOCS| exact SZcs| reflexivity| reflexivity]. }
    exact (L_ret m2 moq hq LBq ls dW cs0 _ j68 t160 t164 t168 t176 t180 r (Z_to_bv 64 135456) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
             y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CS2 ALLNUL LOCS SZcs eq_refl RRANGE BPOS).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma struct_cells4 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_div_mpi ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$4<.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PCS,(8.(42.$0.(8.$3<.)))Pi,$4=.Pd,$:.P,(4>.$4<.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-120.)VdR,$4;.R9.R8.R7.R6.R5.R4.(4?.$9.)R3.(4?.(42.$0.(8.$3<.))))P,(2.(5.$:.)(50.$:.R6.R3.)(51.$:.R2.))(3=.$4<.R;.(15.R3.)(3?.$3<.(5=.(25.&40.(17.R3.)))(3?.$3<.(62.(25.&40.(1>.(23.(13.&40.(25.&40.(53.R3.)))(33.+2.+10.))(18.(33.+2.+10.)(13.&40.(25.&40.(19.R3.)))))))(3?.$3<.(62.(54.R3.))(4?.$3<.)))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW CS i d STq NTH.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ STq NTH) as (((CELLS & _) & _) & _).
    unfold mpi_cells in CELLS.
    exact (rw_cells_join_C2C2 usegs mq (md_addr d) [C8 (Z_to_bv 64 (md_p d))] _ _ [C4 (md_pad d)] CELLS).
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
    intros mq moq hq LBq dX dY dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin XN YN ZN LOCAT S68 S12 RBND BABS.
    pose proof (cs_parts _ _ _ _ _ _ _ CSin) as (HPin & TOPin & MFin & SOKin & MIin & STKin & _ & MOKin).
    pose proof (bv_unsigned_in_range 64 sp) as SPbnd. change (bv_modulus 64) with (2^64) in SPbnd.
    pose proof alloc_ceiling_pos as ACEpos.
    pose proof LOCAT as ADDRS. unfold locals_at in ADDRS. cbn in ADDRS. injection ADDRS as AdX AdY AdZ AdT.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSin (eq_refl : nth_error [dX; dY; dZ; dT] 3 = Some dT))
      as (((CELLT & _ & _ & LENT & NBT & OWNF) & SGT) & NST & _ & _ & _ & _ & HEAPF & _).
    pose proof (struct_cells4 _ _ _ _ _ _ _ 3 dT CSin eq_refl) as JT.
    rewrite AdT in CELLT, JT.
    zstep.
    destruct (md_own dT) eqn:OWNT.
    - cbn iota in OWNF. destruct OWNF as (PT0 & NT0).
      rewrite PT0. if_true.
      clear CELLT.
      pose proof (munch_refl [(SP + -192, SP + -176)] mq) as MUst.
      pose proof (wmono_refl usegs mq) as WMst.
      zstep. zstep.
      pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CSin) as (Fc0 & Ftp & Ft2 & Ftc & Freg).
      pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 0)] _ [C4 (md_pad dT)] JT) as JT2. clear JT.
      pose proof (rw_cells_C2_congr _ _ _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1)] _ 0 [C4 (md_pad dT)] JT2
                    ltac:(rewrite unsigned_lit by lia; reflexivity)) as JT3. clear JT2.
      assert (CSout : cstate usegs L HI h LB mo m SP lo SPc dR es m1 moq hq LBq [dX; dY; dZ; set_sg dT 1] dW []
                        (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { apply (mc_hi_write mq moq hq LBq _ dW [] _ [] (SP + -192) (SP + -176) [] m1 [dX; dY; dZ; set_sg dT 1] _
                 CSin MUst WMst MIin STKin); [lia | lia | constructor | reflexivity | | | ].
        - intros j d d' Ej Ej'.
          destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-.
            right. exists 1. split; [reflexivity |]. split; [left; reflexivity |].
            rewrite AdT, PT0, NT0. exact JT3.
          + exfalso. destruct j; discriminate Ej.
        - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd].
          + eapply rw_cells_transport; [exact Fc0| exact MUst| exact WMst|]. rewrite S68. cbn. lia.
          + eapply rw_cells_transport; [exact Ftp| exact MUst| exact WMst|]. rewrite S12. cbn. lia.
          + eapply rw_cells_transport; [exact Ft2| exact MUst| exact WMst|]. cbn. lia.
          + eapply rw_cells_transport; [exact Ftc| exact MUst| exact WMst|]. cbn. lia.
          + eapply rw_cells_transport; [exact Freg| exact MUst| exact WMst|]. cbn. lia.
        - apply frame_chs; [exact LOCAT| exact S68| exact S12| reflexivity]. }
      eapply (L_c4 m1 moq hq LBq _ dW cs0 tpc j68 t160 t164 t168 t176 t180 r); [exact CSout | | exact LOCAT | exact S68 | exact S12 | exact RBND | exact BABS].
      repeat constructor; assumption.
    - cbn iota in OWNF. destruct OWNF as (NGE1 & INB & PAL & LIMBS).
      destruct (HEAPF eq_refl) as (PPOS & PEND & _ & _ & _).
      assert (PNZ : bv_eqb (Z_to_bv 64 (md_p dT)) (Z_to_bv 64 0) = false).
      { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
      rewrite PNZ. cbv_concl_iota.
      unfold mpi_cells in CELLT. unfold MPI_MAX_LIMBS in NBT.
      zstep. zstep.
      assert (LEN4 : Z_to_bv 64 (bv_unsigned (zx16 (Z_to_bv 64 (md_n dT))) ≪ 2) = Z_to_bv 64 (4 * md_n dT)).
      { unfold zx16. rewrite (unsigned_lit (md_n dT)) by lia. rewrite (Z.mod_small (md_n dT)) by lia.
        rewrite (unsigned_lit (md_n dT)) by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. }
      rewrite LEN4. clear LEN4 CELLT.
      zstep.
      pose proof HZF as ZFS. unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE in ZFS.
      pose proof (u32arr_cells _ _ _ _ LIMBS) as LBYTES.
      replace (4 * length (md_limbs dT))%nat with (Z.to_nat (4 * md_n dT)) in LBYTES by lia.
      eapply aevtM_cut.
      { eapply ZFS with (buf := md_p dT) (len := 4 * md_n dT) (lo := lo) (junk := u32s (md_limbs dT)).
        - exact HPin.
        - right. split; [exact INB | exact LBYTES].
        - lia.
        - rewrite unsigned_lit by lia. exact STKin.
        - rewrite unsigned_lit by lia. lia.
        - exact ACL.
        - rewrite unsigned_lit by lia. rewrite TOPin. lia.
        - rewrite unsigned_lit by lia. lia.
        - exact DHI.
        - exact TP.
        - exact MIin.
        - exact SOKin.
        - exact CA.
        - reflexivity.
        - reflexivity. }
      intros ms' mo' ZPOST. unfold zeroize_and_free_post in ZPOST.
      destruct ZPOST as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2
                         & ECFG & MI2 & STK2 & MF2 & TOP2 & HP2 & PX2 & SOK2).
      injection ECFG as -> ->.
      rewrite unsigned_lit in STK2, PX2 by lia.
      replace (ret_pc (Z_to_bv 64 135436)) with (Z_to_bv 64 135436) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      pose proof (heap_presx_rw_cells _ _ _ _ _ _ _ _ _ PX2 JT ltac:(intros a Ha; left; cbn in Ha; lia)
                    ltac:(cbn; split; [lia | exact I])) as JT2.
      clear JT.
      pose proof (fun m3 => mc_release mq moq hq LBq _ dW [] _ [] 3 dT m2 mo2 h2 m3 (md_pad dT) CSin eq_refl OWNT
                              HP2 TOP2 MF2 PX2 SOK2 MI2 STK2) as REL.
      pose proof (heap_mok _ _ _ _ _ _ _ HP2) as MOK2.
      clear HP2 PX2.
      pose proof (munch_refl [(SP + -192, SP + -176)] m2) as MUst.
      pose proof (wmono_refl usegs m2) as WMst.
      zstep. zstep.
      match goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into m3 end.
      pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 0)] _ [C4 (md_pad dT)] JT2) as JT3. clear JT2.
      pose proof (rw_cells_C2_congr _ _ _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1)] _ 0 [C4 (md_pad dT)] JT3
                    ltac:(rewrite unsigned_lit by lia; reflexivity)) as JT4. clear JT3.
      rewrite <- AdT in JT4.
      assert (MU3 : munch [(md_addr dT, md_addr dT + 16)] m2 m3).
      { rewrite AdT. replace (SP + -192 + 16) with (SP + -176) by lia. exact MUst. }
      pose proof (REL m3 MU3 WMst MI2 JT4) as CSout. cbn [set_nth] in CSout.
      eapply (L_c4 m3 mo2 h2 _ _ dW cs0 tpc j68 t160 t164 t168 t176 t180 r); [exact CSout | | exact LOCAT | exact S68 | exact S12 | exact RBND | exact BABS].
      repeat constructor; assumption.
    - exfalso. exact (NST eq_refl).
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
    intros mq moq hq LBq dX dY dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin XN YN LOCAT S68 S12 RBND BABS.
    pose proof (cs_parts _ _ _ _ _ _ _ CSin) as (HPin & TOPin & MFin & SOKin & MIin & STKin & _ & MOKin).
    pose proof (bv_unsigned_in_range 64 sp) as SPbnd. change (bv_modulus 64) with (2^64) in SPbnd.
    pose proof alloc_ceiling_pos as ACEpos.
    pose proof LOCAT as ADDRS. unfold locals_at in ADDRS. cbn in ADDRS. injection ADDRS as AdX AdY AdZ AdT.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSin (eq_refl : nth_error [dX; dY; dZ; dT] 3 = Some dT))
      as (((TCELL & _) & _) & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSin (eq_refl : nth_error [dX; dY; dZ; dT] 2 = Some dZ))
      as (((CELLZ & _ & _ & LENZ & NBZ & OWNF) & SGZ) & NSZ & _ & _ & _ & _ & HEAPF & _).
    pose proof (struct_cells4 _ _ _ _ _ _ _ 2 dZ CSin eq_refl) as JZ.
    rewrite AdZ in CELLZ, JZ. rewrite AdT in TCELL. unfold mpi_cells in TCELL.
    zstep.
    destruct (md_own dZ) eqn:OWNZ.
    - cbn iota in OWNF. destruct OWNF as (PZ0 & NZ0).
      rewrite PZ0. if_true.
      clear CELLZ.
      zstep. clear TCELL. zstep.
      pose proof (munch_refl [(SP + -176, SP + -160)] mq) as MUst.
      pose proof (wmono_refl usegs mq) as WMst.
      zstep. zstep.
      match goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into m3 end.
      pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CSin) as (Fc0 & Ftp & Ft2 & Ftc & Freg).
      pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 0)] _ [C4 (md_pad dZ)] JZ) as JZ2. clear JZ.
      pose proof (rw_cells_C2_congr _ _ _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1)] _ 0 [C4 (md_pad dZ)] JZ2
                    ltac:(rewrite unsigned_lit by lia; reflexivity)) as JZ3. clear JZ2.
      assert (CSout : cstate usegs L HI h LB mo m SP lo SPc dR es m3 moq hq LBq [dX; dY; set_sg dZ 1; dT] dW []
                        (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { apply (mc_hi_write mq moq hq LBq _ dW [] _ [] (SP + -176) (SP + -160) [] m3 [dX; dY; set_sg dZ 1; dT] _
                 CSin MUst WMst MIin STKin); [lia | lia | constructor | reflexivity | | | ].
        - intros j d d' Ej Ej'.
          destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-.
            right. exists 1. split; [reflexivity |]. split; [left; reflexivity |].
            rewrite AdZ, PZ0, NZ0. exact JZ3.
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + exfalso. destruct j; discriminate Ej.
        - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd].
          + eapply rw_cells_transport; [exact Fc0| exact MUst| exact WMst|]. rewrite S68. cbn. lia.
          + eapply rw_cells_transport; [exact Ftp| exact MUst| exact WMst|]. rewrite S12. cbn. lia.
          + eapply rw_cells_transport; [exact Ft2| exact MUst| exact WMst|]. cbn. lia.
          + eapply rw_cells_transport; [exact Ftc| exact MUst| exact WMst|]. cbn. lia.
          + eapply rw_cells_transport; [exact Freg| exact MUst| exact WMst|]. cbn. lia.
        - apply frame_chs; [exact LOCAT| exact S68| exact S12| reflexivity]. }
      eapply (L_c3 m3 moq hq LBq dX dY _ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r);
        [exact CSout | exact XN | exact YN | exact OWNZ | exact LOCAT | exact S68 | exact S12 | exact RBND | exact BABS].
    - cbn iota in OWNF. destruct OWNF as (NGE1 & INB & PAL & LIMBS).
      destruct (HEAPF eq_refl) as (PPOS & PEND & _ & _ & _).
      assert (PNZ : bv_eqb (Z_to_bv 64 (md_p dZ)) (Z_to_bv 64 0) = false).
      { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
      rewrite PNZ. cbv_concl_iota.
      unfold mpi_cells in CELLZ. unfold MPI_MAX_LIMBS in NBZ.
      zstep. zstep.
      assert (LEN4 : Z_to_bv 64 (bv_unsigned (zx16 (Z_to_bv 64 (md_n dZ))) ≪ 2) = Z_to_bv 64 (4 * md_n dZ)).
      { unfold zx16. rewrite (unsigned_lit (md_n dZ)) by lia. rewrite (Z.mod_small (md_n dZ)) by lia.
        rewrite (unsigned_lit (md_n dZ)) by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. }
      rewrite LEN4. clear LEN4 CELLZ.
      zstep.
      pose proof HZF as ZFS. unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE in ZFS.
      pose proof (u32arr_cells _ _ _ _ LIMBS) as LBYTES.
      replace (4 * length (md_limbs dZ))%nat with (Z.to_nat (4 * md_n dZ)) in LBYTES by lia.
      eapply aevtM_cut.
      { eapply ZFS with (buf := md_p dZ) (len := 4 * md_n dZ) (lo := lo) (junk := u32s (md_limbs dZ)).
        - exact HPin.
        - right. split; [exact INB | exact LBYTES].
        - lia.
        - rewrite unsigned_lit by lia. exact STKin.
        - rewrite unsigned_lit by lia. lia.
        - exact ACL.
        - rewrite unsigned_lit by lia. rewrite TOPin. lia.
        - rewrite unsigned_lit by lia. lia.
        - exact DHI.
        - exact TP.
        - exact MIin.
        - exact SOKin.
        - exact CA.
        - reflexivity.
        - reflexivity. }
      intros ms' mo' ZPOST. unfold zeroize_and_free_post in ZPOST.
      destruct ZPOST as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2
                         & ECFG & MI2 & STK2 & MF2 & TOP2 & HP2 & PX2 & SOK2).
      injection ECFG as -> ->.
      rewrite unsigned_lit in STK2, PX2 by lia.
      replace (ret_pc (Z_to_bv 64 135404)) with (Z_to_bv 64 135404) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      pose proof (heap_presx_rw_cells _ _ _ _ _ _ _ _ _ PX2 JZ ltac:(intros a Ha; left; cbn in Ha; lia)
                    ltac:(cbn; split; [lia | exact I])) as JZ2.
      pose proof (heap_presx_rw_cells _ _ _ _ _ _ _ _ _ PX2 TCELL ltac:(intros a Ha; left; cbn in Ha; lia)
                    ltac:(cbn; split; [lia | exact I])) as TCELL2.
      clear JZ TCELL.
      pose proof (fun m3 => mc_release mq moq hq LBq _ dW [] _ [] 2 dZ m2 mo2 h2 m3 (md_pad dZ) CSin eq_refl OWNZ
                              HP2 TOP2 MF2 PX2 SOK2 MI2 STK2) as REL.
      pose proof (heap_mok _ _ _ _ _ _ _ HP2) as MOK2.
      clear HP2 PX2.
      zstep. clear TCELL2. zstep.
      pose proof (munch_refl [(SP + -176, SP + -160)] m2) as MUst.
      pose proof (wmono_refl usegs m2) as WMst.
      zstep. zstep.
      match goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into m3 end.
      pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 0)] _ [C4 (md_pad dZ)] JZ2) as JZ3. clear JZ2.
      pose proof (rw_cells_C2_congr _ _ _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1)] _ 0 [C4 (md_pad dZ)] JZ3
                    ltac:(rewrite unsigned_lit by lia; reflexivity)) as JZ4. clear JZ3.
      rewrite <- AdZ in JZ4.
      assert (MU3 : munch [(md_addr dZ, md_addr dZ + 16)] m2 m3).
      { rewrite AdZ. replace (SP + -176 + 16) with (SP + -160) by lia. exact MUst. }
      pose proof (REL m3 MU3 WMst MI2 JZ4) as CSout. cbn [set_nth] in CSout.
      eapply (L_c3 m3 mo2 h2 _ dX dY _ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r);
        [exact CSout | exact XN | exact YN | reflexivity | exact LOCAT | exact S68 | exact S12 | exact RBND | exact BABS].
    - exfalso. exact (NSZ eq_refl).
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
    intros mq moq hq LBq dX dY dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin XN LOCAT S68 S12 RBND BABS.
    pose proof (cs_parts _ _ _ _ _ _ _ CSin) as (HPin & TOPin & MFin & SOKin & MIin & STKin & _ & MOKin).
    pose proof (bv_unsigned_in_range 64 sp) as SPbnd. change (bv_modulus 64) with (2^64) in SPbnd.
    pose proof alloc_ceiling_pos as ACEpos.
    pose proof LOCAT as ADDRS. unfold locals_at in ADDRS. cbn in ADDRS. injection ADDRS as AdX AdY AdZ AdT.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSin (eq_refl : nth_error [dX; dY; dZ; dT] 2 = Some dZ))
      as (((ZCELL & _) & _) & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSin (eq_refl : nth_error [dX; dY; dZ; dT] 1 = Some dY))
      as (((CELLY & _ & _ & LENY & NBY & OWNF) & SGY) & NSY & _ & _ & _ & _ & HEAPF & _).
    pose proof (struct_cells4 _ _ _ _ _ _ _ 1 dY CSin eq_refl) as JY.
    rewrite AdY in CELLY, JY. rewrite AdZ in ZCELL. unfold mpi_cells in ZCELL.
    zstep.
    destruct (md_own dY) eqn:OWNY.
    - cbn iota in OWNF. destruct OWNF as (PY0 & NY0).
      rewrite PY0. if_true.
      clear CELLY.
      zstep. clear ZCELL.
      pose proof (munch_refl [(SP + -160, SP + -144)] mq) as MUst.
      pose proof (wmono_refl usegs mq) as WMst.
      zstep. zstep.
      match goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into m3 end.
      pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CSin) as (Fc0 & Ftp & Ft2 & Ftc & Freg).
      pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 0)] _ [C4 (md_pad dY)] JY) as JY2. clear JY.
      pose proof (rw_cells_C2_congr _ _ _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1)] _ 0 [C4 (md_pad dY)] JY2
                    ltac:(rewrite unsigned_lit by lia; reflexivity)) as JY3. clear JY2.
      assert (CSout : cstate usegs L HI h LB mo m SP lo SPc dR es m3 moq hq LBq [dX; set_sg dY 1; dZ; dT] dW []
                        (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { apply (mc_hi_write mq moq hq LBq _ dW [] _ [] (SP + -160) (SP + -144) [] m3 [dX; set_sg dY 1; dZ; dT] _
                 CSin MUst WMst MIin STKin); [lia | lia | constructor | reflexivity | | | ].
        - intros j d d' Ej Ej'.
          destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-.
            right. exists 1. split; [reflexivity |]. split; [left; reflexivity |].
            rewrite AdY, PY0, NY0. exact JY3.
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + exfalso. destruct j; discriminate Ej.
        - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd].
          + eapply rw_cells_transport; [exact Fc0| exact MUst| exact WMst|]. rewrite S68. cbn. lia.
          + eapply rw_cells_transport; [exact Ftp| exact MUst| exact WMst|]. rewrite S12. cbn. lia.
          + eapply rw_cells_transport; [exact Ft2| exact MUst| exact WMst|]. cbn. lia.
          + eapply rw_cells_transport; [exact Ftc| exact MUst| exact WMst|]. cbn. lia.
          + eapply rw_cells_transport; [exact Freg| exact MUst| exact WMst|]. cbn. lia.
        - apply frame_chs; [exact LOCAT| exact S68| exact S12| reflexivity]. }
      eapply (L_c2 m3 moq hq LBq dX _ dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r);
        [exact CSout | exact XN | exact OWNY | exact LOCAT | exact S68 | exact S12 | exact RBND | exact BABS].
    - cbn iota in OWNF. destruct OWNF as (NGE1 & INB & PAL & LIMBS).
      destruct (HEAPF eq_refl) as (PPOS & PEND & _ & _ & _).
      assert (PNZ : bv_eqb (Z_to_bv 64 (md_p dY)) (Z_to_bv 64 0) = false).
      { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
      rewrite PNZ. cbv_concl_iota.
      unfold mpi_cells in CELLY. unfold MPI_MAX_LIMBS in NBY.
      zstep. zstep.
      assert (LEN4 : Z_to_bv 64 (bv_unsigned (zx16 (Z_to_bv 64 (md_n dY))) ≪ 2) = Z_to_bv 64 (4 * md_n dY)).
      { unfold zx16. rewrite (unsigned_lit (md_n dY)) by lia. rewrite (Z.mod_small (md_n dY)) by lia.
        rewrite (unsigned_lit (md_n dY)) by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. }
      rewrite LEN4. clear LEN4 CELLY.
      zstep.
      pose proof HZF as ZFS. unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE in ZFS.
      pose proof (u32arr_cells _ _ _ _ LIMBS) as LBYTES.
      replace (4 * length (md_limbs dY))%nat with (Z.to_nat (4 * md_n dY)) in LBYTES by lia.
      eapply aevtM_cut.
      { eapply ZFS with (buf := md_p dY) (len := 4 * md_n dY) (lo := lo) (junk := u32s (md_limbs dY)).
        - exact HPin.
        - right. split; [exact INB | exact LBYTES].
        - lia.
        - rewrite unsigned_lit by lia. exact STKin.
        - rewrite unsigned_lit by lia. lia.
        - exact ACL.
        - rewrite unsigned_lit by lia. rewrite TOPin. lia.
        - rewrite unsigned_lit by lia. lia.
        - exact DHI.
        - exact TP.
        - exact MIin.
        - exact SOKin.
        - exact CA.
        - reflexivity.
        - reflexivity. }
      intros ms' mo' ZPOST. unfold zeroize_and_free_post in ZPOST.
      destruct ZPOST as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2
                         & ECFG & MI2 & STK2 & MF2 & TOP2 & HP2 & PX2 & SOK2).
      injection ECFG as -> ->.
      rewrite unsigned_lit in STK2, PX2 by lia.
      replace (ret_pc (Z_to_bv 64 135376)) with (Z_to_bv 64 135376) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      pose proof (heap_presx_rw_cells _ _ _ _ _ _ _ _ _ PX2 JY ltac:(intros a Ha; left; cbn in Ha; lia)
                    ltac:(cbn; split; [lia | exact I])) as JY2.
      pose proof (heap_presx_rw_cells _ _ _ _ _ _ _ _ _ PX2 ZCELL ltac:(intros a Ha; left; cbn in Ha; lia)
                    ltac:(cbn; split; [lia | exact I])) as ZCELL2.
      clear JY ZCELL.
      pose proof (fun m3 => mc_release mq moq hq LBq _ dW [] _ [] 1 dY m2 mo2 h2 m3 (md_pad dY) CSin eq_refl OWNY
                              HP2 TOP2 MF2 PX2 SOK2 MI2 STK2) as REL.
      pose proof (heap_mok _ _ _ _ _ _ _ HP2) as MOK2.
      clear HP2 PX2.
      zstep. clear ZCELL2.
      pose proof (munch_refl [(SP + -160, SP + -144)] m2) as MUst.
      pose proof (wmono_refl usegs m2) as WMst.
      zstep. zstep.
      match goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into m3 end.
      pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 0)] _ [C4 (md_pad dY)] JY2) as JY3. clear JY2.
      pose proof (rw_cells_C2_congr _ _ _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1)] _ 0 [C4 (md_pad dY)] JY3
                    ltac:(rewrite unsigned_lit by lia; reflexivity)) as JY4. clear JY3.
      rewrite <- AdY in JY4.
      assert (MU3 : munch [(md_addr dY, md_addr dY + 16)] m2 m3).
      { rewrite AdY. replace (SP + -160 + 16) with (SP + -144) by lia. exact MUst. }
      pose proof (REL m3 MU3 WMst MI2 JY4) as CSout. cbn [set_nth] in CSout.
      eapply (L_c2 m3 mo2 h2 _ dX _ dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r);
        [exact CSout | exact XN | reflexivity | exact LOCAT | exact S68 | exact S12 | exact RBND | exact BABS].
    - exfalso. exact (NSY eq_refl).
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
    intros mq moq hq LBq dX dY dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x0 xa0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin LOCAT S68 S12 RBND BABS.
    pose proof (cs_parts _ _ _ _ _ _ _ CSin) as (HPin & TOPin & MFin & SOKin & MIin & STKin & _ & MOKin).
    pose proof (bv_unsigned_in_range 64 sp) as SPbnd. change (bv_modulus 64) with (2^64) in SPbnd.
    pose proof alloc_ceiling_pos as ACEpos.
    pose proof LOCAT as ADDRS. unfold locals_at in ADDRS. cbn in ADDRS. injection ADDRS as AdX AdY AdZ AdT.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSin (eq_refl : nth_error [dX; dY; dZ; dT] 1 = Some dY))
      as (((YCELL & _) & _) & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSin (eq_refl : nth_error [dX; dY; dZ; dT] 0 = Some dX))
      as (((CELLX & _ & _ & LENX & NBX & OWNF) & SGX) & NSX & _ & _ & _ & _ & HEAPF & _).
    pose proof (struct_cells4 _ _ _ _ _ _ _ 0 dX CSin eq_refl) as JX.
    rewrite AdX in CELLX, JX. rewrite AdY in YCELL. unfold mpi_cells in CELLX, YCELL.
    zstep. zstep.
    destruct (md_own dX) eqn:OWNX.
    - cbn iota in OWNF. destruct OWNF as (PX0 & NX0).
      rewrite PX0. if_true.
      clear CELLX.
      zstep. clear YCELL. zstep.
      pose proof (munch_refl [(SP + -144, SP + -128)] mq) as MUst.
      pose proof (wmono_refl usegs mq) as WMst.
      zstep. zstep.
      match goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into m3 end.
      pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CSin) as (Fc0 & Ftp & Ft2 & Ftc & Freg).
      pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 0)] _ [C4 (md_pad dX)] JX) as JX2. clear JX.
      pose proof (rw_cells_C2_congr _ _ _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1)] _ 0 [C4 (md_pad dX)] JX2
                    ltac:(rewrite unsigned_lit by lia; reflexivity)) as JX3. clear JX2.
      assert (CSout : cstate usegs L HI h LB mo m SP lo SPc dR es m3 moq hq LBq [set_sg dX 1; dY; dZ; dT] dW []
                        (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
      { apply (mc_hi_write mq moq hq LBq _ dW [] _ [] (SP + -144) (SP + -128) [] m3 [set_sg dX 1; dY; dZ; dT] _
                 CSin MUst WMst MIin STKin); [lia | lia | constructor | reflexivity | | | ].
        - intros j d d' Ej Ej'.
          destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
          + injection Ej as <-. injection Ej' as <-.
            right. exists 1. split; [reflexivity |]. split; [left; reflexivity |].
            rewrite AdX, PX0, NX0. exact JX3.
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
          + exfalso. destruct j; discriminate Ej.
        - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd].
          + eapply rw_cells_transport; [exact Fc0| exact MUst| exact WMst|]. rewrite S68. cbn. lia.
          + eapply rw_cells_transport; [exact Ftp| exact MUst| exact WMst|]. rewrite S12. cbn. lia.
          + eapply rw_cells_transport; [exact Ft2| exact MUst| exact WMst|]. cbn. lia.
          + eapply rw_cells_transport; [exact Ftc| exact MUst| exact WMst|]. cbn. lia.
          + eapply rw_cells_transport; [exact Freg| exact MUst| exact WMst|]. cbn. lia.
        - apply frame_chs; [exact LOCAT| exact S68| exact S12| reflexivity]. }
      eapply (L_c1 m3 moq hq LBq _ dY dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r);
        [exact CSout | exact OWNX | exact LOCAT | exact S68 | exact S12 | exact RBND | exact BABS].
    - cbn iota in OWNF. destruct OWNF as (NGE1 & INB & PAL & LIMBS).
      destruct (HEAPF eq_refl) as (PPOS & PEND & _ & _ & _).
      assert (PNZ : bv_eqb (Z_to_bv 64 (md_p dX)) (Z_to_bv 64 0) = false).
      { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
      rewrite PNZ. cbv_concl_iota.
      unfold MPI_MAX_LIMBS in NBX.
      zstep. zstep.
      assert (LEN4 : Z_to_bv 64 (bv_unsigned (zx16 (Z_to_bv 64 (md_n dX))) ≪ 2) = Z_to_bv 64 (4 * md_n dX)).
      { unfold zx16. rewrite (unsigned_lit (md_n dX)) by lia. rewrite (Z.mod_small (md_n dX)) by lia.
        rewrite (unsigned_lit (md_n dX)) by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. }
      rewrite LEN4. clear LEN4 CELLX.
      zstep.
      pose proof HZF as ZFS. unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE in ZFS.
      pose proof (u32arr_cells _ _ _ _ LIMBS) as LBYTES.
      replace (4 * length (md_limbs dX))%nat with (Z.to_nat (4 * md_n dX)) in LBYTES by lia.
      eapply aevtM_cut.
      { eapply ZFS with (buf := md_p dX) (len := 4 * md_n dX) (lo := lo) (junk := u32s (md_limbs dX)).
        - exact HPin.
        - right. split; [exact INB | exact LBYTES].
        - lia.
        - rewrite unsigned_lit by lia. exact STKin.
        - rewrite unsigned_lit by lia. lia.
        - exact ACL.
        - rewrite unsigned_lit by lia. rewrite TOPin. lia.
        - rewrite unsigned_lit by lia. lia.
        - exact DHI.
        - exact TP.
        - exact MIin.
        - exact SOKin.
        - exact CA.
        - reflexivity.
        - reflexivity. }
      intros ms' mo' ZPOST. unfold zeroize_and_free_post in ZPOST.
      destruct ZPOST as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2
                         & ECFG & MI2 & STK2 & MF2 & TOP2 & HP2 & PX2 & SOK2).
      injection ECFG as -> ->.
      rewrite unsigned_lit in STK2, PX2 by lia.
      replace (ret_pc (Z_to_bv 64 135344)) with (Z_to_bv 64 135344) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      pose proof (heap_presx_rw_cells _ _ _ _ _ _ _ _ _ PX2 JX ltac:(intros a Ha; left; cbn in Ha; lia)
                    ltac:(cbn; split; [lia | exact I])) as JX2.
      pose proof (heap_presx_rw_cells _ _ _ _ _ _ _ _ _ PX2 YCELL ltac:(intros a Ha; left; cbn in Ha; lia)
                    ltac:(cbn; split; [lia | exact I])) as YCELL2.
      clear JX YCELL.
      pose proof (fun m3 => mc_release mq moq hq LBq _ dW [] _ [] 0 dX m2 mo2 h2 m3 (md_pad dX) CSin eq_refl OWNX
                              HP2 TOP2 MF2 PX2 SOK2 MI2 STK2) as REL.
      pose proof (heap_mok _ _ _ _ _ _ _ HP2) as MOK2.
      clear HP2 PX2.
      zstep. clear YCELL2. zstep.
      pose proof (munch_refl [(SP + -144, SP + -128)] m2) as MUst.
      pose proof (wmono_refl usegs m2) as WMst.
      zstep. zstep.
      match goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into m3 end.
      pose proof (rw_cells_split_C4 _ _ _ [C8 (Z_to_bv 64 0)] _ [C4 (md_pad dX)] JX2) as JX3. clear JX2.
      pose proof (rw_cells_C2_congr _ _ _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1)] _ 0 [C4 (md_pad dX)] JX3
                    ltac:(rewrite unsigned_lit by lia; reflexivity)) as JX4. clear JX3.
      rewrite <- AdX in JX4.
      assert (MU3 : munch [(md_addr dX, md_addr dX + 16)] m2 m3).
      { rewrite AdX. replace (SP + -144 + 16) with (SP + -128) by lia. exact MUst. }
      pose proof (REL m3 MU3 WMst MI2 JX4) as CSout. cbn [set_nth] in CSout.
      eapply (L_c1 m3 mo2 h2 _ _ dY dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r);
        [exact CSout | reflexivity | exact LOCAT | exact S68 | exact S12 | exact RBND | exact BABS].
    - exfalso. exact (NSX eq_refl).
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
    intros mq moq hq LBq dX dY dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin LOCAT S68 S12 RBND BABS.
    pose proof (cs_parts _ _ _ _ _ _ _ CSin) as (_ & _ & _ & _ & _ & _ & _ & MOKin).
    zstep.
    exact (L_c0 mq moq hq LBq dX dY dZ dT dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x0 (Z_to_bv 64 r) x1 x2 x3 x4 x5 x6 x7 x8 x9 x11
             t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin LOCAT S68 S12 RBND BABS).
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
    intros mq moq hq LBq dX dY dZ dT cs0 tpc j68 t160 t164 t168 t176 t180
      xra x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin LOCS SIZE0 SIZE1 BNZ.
    pose proof (bv_unsigned_in_range 64 sp) as SPbnd. change (bv_modulus 64) with (2^64) in SPbnd.
    pose proof alloc_ceiling_pos as CEILpos.
    pose proof (cs_parts _ _ _ _ _ _ _ CSin) as (HEAPq & TOPeq & MOFR & STATq & MINVq & STKq & _ & MOKq).
    destruct facts0 as (RADDRpos & RADDRal & RADDRside & _ & _ & _ & _ & _).
    assert (LX : md_addr dX = SP + -144 /\ md_addr dY = SP + -160 /\ md_addr dZ = SP + -176 /\ md_addr dT = SP + -192).
    { unfold locals_at in LOCS. cbn in LOCS. injection LOCS as AX AY AZ AT. auto. }
    destruct LX as (AXeq & _).
    destruct (a_cells _ _ _ _ _ _ CSin) as (ACELLS & ASIGN).
    destruct (struct_cells _ _ _ _ _ _ _ 0%nat dX CSin eq_refl) as (XCELLS & XSIGN & _).
    rewrite AXeq in XCELLS. unfold mpi_cells in ACELLS, XCELLS.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CSin) as (FR0 & FR1 & FR2 & FR3 & FR4).
    unfold t2cells in FR2.
    pose proof (munch_refl [(SP + -136, SP + -134)] mq) as MUs.
    pose proof (wmono_refl usegs mq) as WMs.
    do 2 zstep.
    assert (SXeq : sx16 (Z_to_bv 64 (md_sg dA)) = Z_to_bv 64 (md_sg dA)).
    { destruct ASIGN as [SG1 | SG1]; rewrite SG1; apply bv_eq; vm_compute; reflexivity. }
    rewrite SXeq in XCELLS |- *.
    set (dX1 := set_sg dX (md_sg dA)).
    assert (LOCS1 : locals_at [dX1; dY; dZ; dT]) by (unfold locals_at in LOCS |- *; exact LOCS).
    assert (CS1 : CST m0 moq hq LBq [dX1; dY; dZ; dT] dR [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_hi_write mq moq hq LBq _ dR [] _ [] (SP + -136) (SP + -134) [] m0 [dX1; dY; dZ; dT] _ CSin MUs WMs MINVq STKq);
        [lia | lia | constructor | reflexivity | | | apply frame_chs; [exact LOCS1 | exact SIZE0 | exact SIZE1 | reflexivity]].
      - intros j d d' NTH NTH'.
        destruct j as [|[|[|[|j]]]]; cbn in NTH, NTH'; try (destruct j; discriminate NTH);
          injection NTH as <-; injection NTH' as <-.
        + right. exists (md_sg dA). split; [reflexivity|]. split; [exact ASIGN|].
          rewrite AXeq. exact XCELLS.
        + left. unfold locals_at in LOCS. cbn in LOCS. injection LOCS as _ AY _ _. split; [lia | reflexivity].
        + left. unfold locals_at in LOCS. cbn in LOCS. injection LOCS as _ _ AZ _. split; [lia | reflexivity].
        + left. unfold locals_at in LOCS. cbn in LOCS. injection LOCS as _ _ _ AT. split; [lia | reflexivity].
      - unfold frame. constructor; [exact FR0|]. constructor; [exact FR1|]. constructor; [exact FR2|].
        constructor; [exact FR3|]. constructor; [exact FR4| constructor]. }
    clear FR0 FR1 FR2 FR3 FR4 MUs WMs XCELLS.
    do 3 zstep.
    destruct (mc_w_facts _ _ _ _ _ _ _ _ _ CS1) as (MATR & _ & _ & WRq & _).
    destruct (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX1 CS1 eq_refl) as (MATX1 & _ & _ & _ & CRX1 & CRLX1 & _).
    destruct (mc_opnd_sep_wl _ _ _ _ _ _ _ _ _ 0%nat dX1 CS1 eq_refl) as (SEPRX & OSRX).
    assert (CPSEP : copy_sep dR dX1 lo SPc).
    { apply copy_sep_of_opnd; [exact OSRX|]. cbn [dX1 set_sg md_addr]. lia. }
    pose proof HCOPY as COPYSPEC. unfold mpi_copy_stmt_x, U_MPI_COPY in COPYSPEC.
    eapply aevtM_cut; [eapply COPYSPEC with (dX := dR) (dY := dX1) (lo := lo) (LB := LBq) (h := hq);
      rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity; try lia | ].
    { unfold dX1, set_sg. cbn [md_addr]. rewrite AXeq. reflexivity. }
    intros ms' mo' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & mo2 & h2 & LB2 & dR2 & rc &
                    CFG & MINV2 & STK2 & MOFR2 & TOP2 & HEAP2 & MAT2 & OUT2 & PRES2 & STAT2 & RES2).
    injection CFG as -> ->.
    rewrite (unsigned_lit (SP + -288)) in STK2, PRES2 by lia.
    destruct RES2 as ((OUTCOME & ADDR2 & PAD2 & BLK2) & _).
    assert (CS2 : CST m2 mo2 h2 LB2 [dX1; dY; dZ; dT] dR2 [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_binop_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ CS1 HEAP2 TOP2 MOFR2 MAT2 OUT2 PRES2 STAT2 MINV2 STK2 BLK2 PAD2).
      destruct OUTCOME as [(_ & _ & NGROW & _) | (_ & NSAME & _)]; lia. }
    replace (ret_pc (Z_to_bv 64 136640)) with (Z_to_bv 64 136640) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (_ & _ & _ & _ & _ & _ & _ & MOK2).
    destruct OUTCOME as [(-> & _) | (-> & _)].
    2:{ unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
        replace (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
        eapply L_err; [exact CS2 | exact LOCS1 | exact SIZE0 | exact SIZE1 | lia | exact BNZ]. }
    zstep. rewrite bv_eqb_refl. cbv [negb].
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CS2) as (FR0 & FR1 & FR2 & FR3 & FR4).
    unfold t2cells in FR2. unfold tcells in FR3.
    pose proof (munch_refl [(SP + -128, SP + -104)] m2) as MUt.
    pose proof (wmono_refl usegs m2) as WMt.
    do 9 zstep.
    assert (CS3 : CST m1 mo2 h2 LB2 [dX1; dY; dZ; dT] dR2 []
                    (frame cs0 tpc j68 (tcells t160 (Z_to_bv 64 0) (Z_to_bv 64 (SP + -124)) (Z_to_bv 64 65537) t180)) []).
    { apply (cs_frame_updT _ _ _ _ _ _ _ _ _ _ (SP + -128) (SP + -104) m1 _ CS2 LOCS1 MUt WMt MINV2 STK2);
        [lia | lia | exact FR3 | reflexivity | exact SIZE0 | exact SIZE1]. }
    set (Tm := {| md_addr := SP + -120; md_sg := 1; md_n := 1; md_p := SP + -124; md_limbs := [Z_to_bv 64 0];
                  md_pad := t180; md_own := LStatic |}).
    assert (TOPND : MpiOpnd.stack_opnd usegs m1 (SP + -288) Tm).
    { pose proof FR3 as TC. take TC 1%nat C160. take TC 1%nat C164.
      apply (rw_cells_split_C4 usegs m1 (SP + -120) [C8 (Z_to_bv 64 (SP + -124))] _ [C4 t180]) in TC.
      rewrite (unsigned_lit 65537) in TC by lia. cbn [app] in TC.
      apply (rw_cells_C2_congr usegs m1 (SP + -120) [C8 (Z_to_bv 64 (SP + -124))] 65537 1 _) in TC; [| reflexivity].
      apply (rw_cells_C2_congr usegs m1 (SP + -120) [C8 (Z_to_bv 64 (SP + -124)); C2 (Z_to_bv 64 1)] (65537 / 2 ^ 16) 1 _)
        in TC; [| reflexivity].
      pose proof (LxPMpiTac.u32arr_of_rw_cells m1 (SP + -124) [Z_to_bv 64 0] C164) as (LIMBS & _).
      unfold MpiOpnd.stack_opnd. cbn [Tm md_own md_addr md_sg md_n md_p md_limbs md_pad].
      split; [reflexivity|]. split; [exact TC|].
      split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact LIMBS|]. split; [lia|]. split; [lia|].
      left; reflexivity. }
    destruct (mc_w_facts _ _ _ _ _ _ _ _ _ CS3) as (MATR3 & _ & _ & _ & _ & _ & _ & HPR3 & _).
    pose proof HCMPO as CMPSPEC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in CMPSPEC.
    eapply aevtM_cut_evt; [exact MOK2 | eapply CMPSPEC with (dX := dR2) (dY := Tm) (LB := LB2);
      rewrite ?(unsigned_lit (SP + -288)) by lia |].
    { left. exact MATR3. }
    { right. exact TOPND. }
    { intros OWNH. destruct (HPR3 OWNH) as (PPOS & _). exact PPOS. }
    { intros OWNT. cbn [Tm md_own] in OWNT. discriminate OWNT. }
    { exact MINV2. }
    { rewrite ADDR2. reflexivity. }
    { reflexivity. }
    intros ms' CPO. unfold mpi_cmp_post in CPO.
    destruct CPO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & -> & _ & _ & _).
    replace (ret_pc (Z_to_bv 64 136680)) with (Z_to_bv 64 136680) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep.
    destruct (Z.lt_trichotomy (mpd_val dR2 - mpd_val Tm) 0) as [CNEG | [CZERO | CPOS]].
    - rewrite (Z.sgn_neg _ CNEG).
      assert (NEm1 : bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = false) by (vm_compute; reflexivity).
      rewrite NEm1. do 2 zstep.
      eapply L_c0; [exact CS3 | exact LOCS1 | exact SIZE0 | exact SIZE1 | lia | exact BNZ].
    - rewrite (Z.sgn_null _ CZERO), bv_eqb_refl.
      destruct (w_cells _ _ _ _ _ _ _ CS3) as (RC3 & _).
      pose proof (rw_cells_bound _ _ _ _ RC3) as RBND3. cbn [cells_size csize mpi_cells Nat.add] in RBND3.
      zstep.
      assert (LAND0 : Z.land (md_addr dR) 7 = 0).
      { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact RADDRal. }
      rewrite LAND0. zstep. rewrite bv_eqb_refl. cbv [negb].
      unfold mpi_cells in RC3. clear MUt WMt.
      pose proof (munch_refl [(md_addr dR, md_addr dR + 16)] m1) as MUr.
      pose proof (wmono_refl usegs m1) as WMr.
      do 3 zstep.
      assert (CS4 : CST m3 mo2 h2 LB2 [dX1; dY; dZ; dT] (set_sg dR2 1) []
                      (frame cs0 tpc j68 (tcells t160 (Z_to_bv 64 0) (Z_to_bv 64 (SP + -124)) (Z_to_bv 64 65537) t180)) []).
      { rewrite <- ADDR2 in MUr, RC3.
        apply (mc_sign_w _ _ _ _ _ _ _ _ _ m3 1 CS3 MUr WMr MINV2 RC3). left; reflexivity. }
      zstep.
      eapply L_c0; [exact CS4 | exact LOCS1 | exact SIZE0 | exact SIZE1 | lia | exact BNZ].
    - rewrite (Z.sgn_pos _ CPOS).
      assert (NEp1 : bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0) = false) by (vm_compute; reflexivity).
      rewrite NEp1. do 2 zstep.
      eapply L_c0; [exact CS3 | exact LOCS1 | exact SIZE0 | exact SIZE1 | lia | exact BNZ].
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
    intros mq moq hq LBq dX dY dZ dT j0 w8 w16 w24 w40 w48 w56 j64 tpc j68 t160 t164 t168 t176 t180 k
      xra x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin LOCS SIZE1 KRNG BNZ.
    pose proof (bv_unsigned_in_range 64 sp) as SPbnd. change (bv_modulus 64) with (2^64) in SPbnd.
    pose proof alloc_ceiling_pos as CEILpos.
    pose proof (cs_parts _ _ _ _ _ _ _ CSin) as (HEAPq & TOPeq & MOFR & STATq & MINVq & STKq & _ & MOKq).
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CSin) as (FR0 & FR1 & FR2 & FR3 & FR4).
    destruct facts0 as (RADDRpos & _ & _ & _ & _ & _ & _ & _).
    destruct (w_cells _ _ _ _ _ _ _ CSin) as (RCELLS & _).
    pose proof (rw_cells_bound _ _ _ _ RCELLS) as RBND. cbn [cells_size csize mpi_cells Nat.add] in RBND.
    zstep. rewrite bv_eqb_refl.
    zstep.
    rewrite (bv_eqb_neq (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 0)) by
      (intros E0; apply (f_equal bv_unsigned) in E0; rewrite !unsigned_lit in E0 by lia; lia).
    do 3 zstep.
    assert (LX : md_addr dX = SP + -144 /\ md_addr dY = SP + -160 /\ md_addr dZ = SP + -176 /\ md_addr dT = SP + -192).
    { unfold locals_at in LOCS. cbn in LOCS. injection LOCS as AX AY AZ AT. auto. }
    destruct LX as (AXeq & _).
    destruct (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX CSin eq_refl)
      as (MATX & NSTX & WRX & _ & _ & _ & HPX & _).
    destruct (struct_cells _ _ _ _ _ _ _ 0%nat dX CSin eq_refl) as (_ & _ & NRNG & NULLX & _).
    pose proof HSHR as SHRSPEC. unfold mpi_shift_r_stmt, U_MPI_SHIFT_R in SHRSPEC.
    eapply aevtM_cut_evt; [exact MOKq | eapply SHRSPEC with (dX := dX) (count := k) (lo := lo) (LB := LBq);
      rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity; try lia |].
    { intros OWNH. destruct (HPX OWNH) as (PPOS & PEND & _). lia. }
    { destruct WRX as (_ & _ & SEPX). exact SEPX. }
    { rewrite AXeq. reflexivity. }
    intros ms' PO. unfold mpi_shift_r_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & xs2 &
                    -> & MU2 & WM2 & MINV2 & STK2 & MAT2 & LEN2 & _).
    rewrite (unsigned_lit (SP + -288)) in MU2, STK2 by lia.
    replace (ret_pc (Z_to_bv 64 136620)) with (Z_to_bv 64 136620) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (OWNcases : md_own dX = LNull \/ md_own dX = LHeap).
    { destruct (md_own dX); [left; reflexivity | right; reflexivity | exfalso; apply NSTX; reflexivity]. }
    set (dX2 := {| md_addr := md_addr dX; md_sg := md_sg dX; md_n := md_n dX; md_p := md_p dX; md_limbs := xs2;
                   md_pad := md_pad dX; md_own := md_own dX |}) in *.
    assert (WSEL : exists Wsel, munch Wsel mq m2 /\
                     Forall (w_ok lo SPc [dX; dY; dZ; dT] (Some 0%nat) false false dR []) Wsel).
    { destruct OWNcases as [OWNX | OWNX].
      - exists [(SP + -288 - 48, SP + -288)]. split.
        + eapply munch_weaken; [| exact MU2]. destruct (NULLX OWNX) as (P0 & N0).
          intros x (OUT1 & _). cbn. rewrite P0, N0. split; [exact OUT1 | split; [lia | exact I]].
        + constructor; [left; cbn; lia | constructor].
      - exists [(SP + -288 - 48, SP + -288); (md_p dX, md_p dX + 4 * md_n dX)]. split; [exact MU2|].
        constructor; [left; cbn; lia|]. constructor; [|constructor].
        right; left. exists 0%nat, dX. cbn. repeat split; [exact OWNX | lia | lia]. }
    destruct WSEL as (Wsel & MUsel & WOKsel).
    assert (CS2 : CST m2 moq hq LBq [dX2; dY; dZ; dT] dR []
                    (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 w56; CB 4 j64]
                       tpc j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_munch _ _ _ _ _ _ _ _ _ (Some 0%nat) false false Wsel m2 [dX2; dY; dZ; dT] dR [] CSin MUsel WM2 MINV2 STK2
               WOKsel eq_refl).
      - intros j d d' NTH NTH'.
        destruct j as [|[|[|[|j]]]]; cbn in NTH, NTH'; try (destruct j; discriminate NTH);
          injection NTH as <-; injection NTH' as <-.
        + cbn [md_addr md_sg md_n md_p md_pad md_own dX2].
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
          * intros NOTHEAP.
            assert (XSnil : xs2 = md_limbs dX).
            { destruct MATX as ((_ & _ & _ & LENX & _ & _) & _).
              destruct OWNcases as [OWNX | OWNX]; [| exfalso; apply NOTHEAP; split; [reflexivity | exact OWNX]].
              destruct (NULLX OWNX) as (_ & N0). rewrite N0 in LENX.
              assert (L0 : length (md_limbs dX) = 0%nat) by lia.
              apply length_zero_iff_nil in L0. rewrite L0 in LEN2 |- *.
              apply length_zero_iff_nil in LEN2. exact LEN2. }
            subst dX2. rewrite XSnil. destruct dX; reflexivity.
          * intros _ OWNH. destruct MAT2 as ((_ & _ & _ & LENX2 & _ & OWNP2) & _).
            cbn [md_own md_p md_limbs dX2] in OWNP2, LENX2 |- *. rewrite OWNH in OWNP2.
            destruct OWNP2 as (_ & _ & _ & U32). split; [exact U32 | exact LENX2].
        + do 6 (split; [reflexivity|]). split; [intros _; reflexivity | intros E1; discriminate E1].
        + do 6 (split; [reflexivity|]). split; [intros _; reflexivity | intros E1; discriminate E1].
        + do 6 (split; [reflexivity|]). split; [intros _; reflexivity | intros E1; discriminate E1].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity | intros E1; discriminate E1].
      - intros; reflexivity.
      - intros E1; discriminate E1. }
    eapply L_fin2; [exact CS2 | | reflexivity | exact SIZE1 | exact BNZ].
    unfold locals_at in LOCS |- *. cbn [map md_addr dX2]. exact LOCS.
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
  Proof using sp.
    intros mq LBq d ((_ & _ & _ & _ & _ & OWNF) & _) NOTST ONE.
    destruct (md_own d) eqn:OWNd; [| reflexivity | exfalso; exact (NOTST eq_refl)].
    destruct OWNF as [_ ZEROn]. lia.
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
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [] ->
    locals_at [dX; dY; dZ; dT] ->
    loop_loc dX dY dZ dT n t zp ->
    t < i <= ib -> i < n ->
    aevtM usegs moq POST
      (MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) x4 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (4 * t))
               x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) x9 x10 (Z_to_bv 64 zp) t3 t4 t5 t6)
          F (Z_to_bv 64 0x211ec) fc None mq (seg_rom usegs)).

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
    intros n t zp k ib j0 j64 Kont mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x5 x7 x10 CSq LOCq LLq Tnn Irng Iib Nmax Krng.
    unfold lframe in CSq.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CSq) as (FRcs & _ & _ & _ & _).
    pose proof (cs_parts _ _ _ _ _ _ _ CSq) as (_ & _ & _ & _ & _ & _ & _ & MOKq).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    do 4 zstep.
    rewrite bv_ltu_Z, (unsigned_lit t), (unsigned_lit (i + -1)) by lia.
    destruct (Z.ltb_spec t (i + -1)) as [MORE| LAST].
    - replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + -1 + 1)) by (f_equal; lia).
      exact (Kont mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 (i + -1)
               xra t0 t1 t2 (Z_to_bv 64 t) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 (Z_to_bv 64 (i + -1 + 1)) x10
               CSq LOCq LLq ltac:(lia) ltac:(lia)).
    - unfold loop_loc in LLq.
      exact (L_fin mq moq hq LBq dX dY dZ dT j0 _ _ _ _ _ _ j64 _ j68 t160 t164 t168 t176 t180 k
               xra x4 (Z_to_bv 64 i) (Z_to_bv 64 (4 * t)) x7 (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) x10 (Z_to_bv 64 zp)
               t0 t1 t2 (Z_to_bv 64 (i + -1)) (Z_to_bv 64 t) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
               CSq LOCq eq_refl Krng (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 LLq))))))))) ).
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
    intros n t zp k ib j0 j64 Kont Tnn Nmax Krng mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 CSq LOCq LLq Irng Iib.
    pose proof (cs_parts _ _ _ _ _ _ _ CSq) as (HPq & TOPq & MFq & SOKq & MIq & STKq & _ & MOKq).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    pose proof LOCq as ADq. unfold locals_at in ADq. cbn [map] in ADq. injection ADq as ADX ADY ADZ ADT.
    pose proof LLq as LLparts. unfold loop_loc in LLparts.
    destruct LLparts as (OWX & NX & OWY & NY & OWZ & PZ & NZ & OWT & NT & BABS).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 2%nat dZ CSq eq_refl) as (MZ & _ & _ & _ & _ & _ & HZ & _).
    destruct (HZ OWZ) as (PZpos & PZtop & _).
    destruct MZ as ((_ & _ & _ & LENZ & _ & OWNZ) & _). rewrite OWZ in OWNZ. destruct OWNZ as (_ & _ & _ & ARRZ).
    destruct (nth_error (md_limbs dZ) (Z.to_nat (i - t - 1))) as [wq|] eqn:NTHq.
    2: { exfalso. apply nth_error_None in NTHq. lia. }
    rewrite PZ in ARRZ.
    rdq ARRZ NTHq (i - t - 1).
    do 3 zstep.
    assert (A2lo : bv_unsigned (sx32 wq) mod 2^32 = w32 wq).
    { rewrite w32_sx32. unfold sxz, w32. pose proof (Z.mod_pos_bound (bv_unsigned wq) (2^32) ltac:(lia)) as WB.
      destruct (Z.ltb_spec (bv_unsigned wq mod 2^32) (2^31)); lia. }
    assert (A2z : bv_unsigned (sx32 wq) = 0 <-> w32 wq = 0).
    { rewrite w32_sx32. unfold sxz, w32. pose proof (Z.mod_pos_bound (bv_unsigned wq) (2^32) ltac:(lia)) as WB.
      destruct (Z.ltb_spec (bv_unsigned wq mod 2^32) (2^31)); lia. }
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT CSq eq_refl) as (MT & NST & WRT & LOT & _ & _ & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 1%nat dY CSq eq_refl) as (MY & _ & _ & _ & CRY & CRLY & _).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 3%nat 1%nat dT dY CSq eq_refl eq_refl) as (SEPTY & OSTY).
    pose proof HMULI as MULI. unfold mpi_mul_int_stmt_g, U_MPI_MUL_INT in MULI.
    eapply aevtM_cut; [eapply MULI with (dX := dT) (dA := dY) (b := w32 wq) (lo := lo) (h := hq) (LB := LBq);
      rewrite ?(unsigned_lit (SP + -288)) by lia;
      first [eassumption | reflexivity | (rewrite ?ADX, ?ADY, ?ADZ, ?ADT; reflexivity) | (rewrite TOPq; lia)
            | (unfold w32; apply Z.mod_pos_bound; lia) | lia | idtac] |].
    intros ms1 mo1 PO1.
    binop_post PO1 m1 mo1' h1 LB1 dT1 r1 E1 MI1 ST1 MF1 HT1 HH1 MA1 OUT1 PX1 SOK1 RR1.
    replace (ret_pc (Z_to_bv 64 136376)) with (Z_to_bv 64 136376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR1 as (RES1 & KEEP1).
    pose proof KEEP1 as (ADT1 & _ & BLK1 & NT1).
    pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 3%nat dT m1 mo1' h1 LB1 dT1 CSq eq_refl HH1 HT1 MF1 MA1 OUT1 PX1 SOK1 MI1 ST1 BLK1)
      as CS1.
    cbn [set_nth] in CS1.
    assert (LOC1 : locals_at [dX; dY; dZ; dT1]).
    { unfold locals_at. cbn [map]. rewrite ADT1, ADX, ADY, ADZ, ADT. reflexivity. }
    pose proof (cs_parts _ _ _ _ _ _ _ CS1) as (HP1 & TOP1 & _ & SOKq1 & MIq1 & STK1 & _ & MOK1).
    destruct RES1 as [(R1z & _) | R1e]; subst r1.
    2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
         change (negb (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0))) with true. cbn iota.
         eapply L_err; [exact CS1 | exact LOC1 | reflexivity | reflexivity | lia | exact BABS]. }
    zstep.
    change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbn iota.
    do 4 zstep.
    replace ((i - t - 1) ≪ 5) with (32 * (i - t - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT1 CS1 eq_refl) as (MT1 & NST1 & WRT1 & LOT1 & _).
    pose proof HSHL as SHL. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SHL.
    eapply aevtM_cut; [eapply SHL with (dX := dT1) (count := 32 * (i - t - 1)) (lo := lo) (h := h1) (LB := LB1);
      rewrite ?(unsigned_lit (SP + -288)) by lia;
      first [eassumption | reflexivity | (rewrite ?ADT1, ?ADT; reflexivity) | (rewrite TOP1; lia)
            | (rewrite unsigned_lit by lia; reflexivity) | lia | idtac] |].
    intros ms2 mo2 PO2.
    binop_post PO2 m2 mo2' h2 LB2 dT2 r2 E2 MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
    replace (ret_pc (Z_to_bv 64 136396)) with (Z_to_bv 64 136396) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR2 as (RES2 & KEEP2).
    pose proof KEEP2 as (ADT2 & _ & BLK2 & NT2).
    pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 3%nat dT1 m2 mo2' h2 LB2 dT2 CS1 eq_refl HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2 BLK2)
      as CS2.
    cbn [set_nth] in CS2.
    assert (LOC2 : locals_at [dX; dY; dZ; dT2]).
    { unfold locals_at. cbn [map]. rewrite ADT2, ADT1, ADX, ADY, ADZ, ADT. reflexivity. }
    pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (HP2 & TOP2 & _ & SOKq2 & MIq2 & STK2 & _ & MOK2).
    destruct RES2 as [(R2z & _) | R2e]; subst r2.
    2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
         change (negb (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0))) with true. cbn iota.
         eapply L_err; [exact CS2 | exact LOC2 | reflexivity | reflexivity | lia | exact BABS]. }
    zstep.
    change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbn iota.
    do 5 zstep.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX CS2 eq_refl) as (MX2 & NSX2 & WRX2 & LOX2 & CRX2 & CRLX2 & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT2 CS2 eq_refl) as (MT2 & _ & _ & _ & CRT2 & CRLT2 & _).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0%nat 0%nat dX dX CS2 eq_refl eq_refl) as (_ & OSXX2).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0%nat 3%nat dX dT2 CS2 eq_refl eq_refl) as (SEPXT2 & OSXT2).
    pose proof HAS as ASUB. unfold add_sub_mpi_stmt, U_ADD_SUB_MPI in ASUB.
    eapply aevtM_cut; [eapply ASUB with (flip := -1) (dX := dX) (dA := dX) (dB := dT2) (lo := lo) (h := h2) (LB := LB2);
      rewrite ?(unsigned_lit (SP + -288)) by lia;
      first [eassumption | reflexivity | (left; reflexivity) | (right; reflexivity)
            | (rewrite ?ADT2, ?ADT1, ?ADT, ?ADX; reflexivity) | (rewrite TOP2; lia) | lia | idtac] |].
    intros ms3 mo3 PO3.
    binop_post PO3 m3 mo3' h3 LB3 dX3 r3 E3 MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR3.
    replace (ret_pc (Z_to_bv 64 136420)) with (Z_to_bv 64 136420) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR3 as (RES3 & KEEP3).
    pose proof KEEP3 as (ADX3 & _ & BLK3 & NX3).
    pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 0%nat dX m3 mo3' h3 LB3 dX3 CS2 eq_refl HH3 HT3 MF3 MA3 OUT3 PX3 SOK3 MI3 ST3 BLK3)
      as CS3.
    cbn [set_nth] in CS3.
    assert (LOC3 : locals_at [dX3; dY; dZ; dT2]).
    { unfold locals_at. cbn [map]. rewrite ADX3, ADT2, ADT1, ADX, ADY, ADZ, ADT. reflexivity. }
    pose proof (cs_parts _ _ _ _ _ _ _ CS3) as (HP3 & TOP3 & _ & SOKq3 & MIq3 & STK3 & _ & MOK3).
    destruct RES3 as [(R3z & _) | R3e]; subst r3.
    2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
         change (negb (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0))) with true. cbn iota.
         eapply L_err; [exact CS3 | exact LOC3 | reflexivity | reflexivity | lia | exact BABS]. }
    zstep.
    change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbn iota.
    unfold lframe in CS3.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CS3) as (FRcs3 & _ & _ & FRtc3 & _).
    unfold tcells in FRtc3.
    pose proof (munch_refl [(SP + -128, SP + -104)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    do 5 zstep.
    rename m0 into m4.
    pose proof (cs_frame_updT _ _ _ _ _ _ _ _ _ _ _ _ _ _ CS3 LOC3 MU WM MIq3 STK3 ltac:(lia) ltac:(lia) FRtc3 eq_refl eq_refl eq_refl)
      as CS4.
    clear MU WM.
    take FRtc3 1%nat TCpad. take FRtc3 1%nat TClimb.
    assert (TOPND : MpiOpnd.stack_opnd usegs m4 SPc (mkMPD (SP + -120) 1 1 (SP + -124) [Z_to_bv 64 0] t180 LStatic)).
    { pose proof (rw_cells_split_C4 usegs m4 (SP + -120) [C8 (Z_to_bv 64 (SP + -124))] (Z_to_bv 64 65537) [C4 t180] FRtc3)
        as HDR2.
      cbn [app] in HDR2.
      apply (rw_cells_C2_congr usegs m4 (SP + -120) [C8 (Z_to_bv 64 (SP + -124))] 65537 1) in HDR2; [| reflexivity].
      cbn [app] in HDR2.
      apply (rw_cells_C2_congr usegs m4 (SP + -120) [C8 (Z_to_bv 64 (SP + -124)); C2 (Z_to_bv 64 1)]
               (bv_unsigned (Z_to_bv 64 65537) / 2 ^ 16) 1) in HDR2; [| reflexivity].
      cbn [app] in HDR2.
      unfold MpiOpnd.stack_opnd. cbn [md_own md_addr md_p md_sg md_n md_pad md_limbs length Z.of_nat].
      split; [reflexivity|]. split; [exact HDR2|].
      split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; [lia|].
      split; [lia|]. split; [lia|].
      split; [exact (u32arr_ro _ _ _ _ (LxPMpiTac.u32arr_of_rw_cells m4 (SP + -124) [Z_to_bv 64 0] TClimb))|].
      split; [lia|]. split; [lia|]. left; reflexivity. }
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX3 CS4 eq_refl) as (MX4 & NSX4 & _ & _ & _ & _ & HX4 & _).
    do 3 zstep.
    pose proof HCMPO as CMPO. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in CMPO.
    eapply aevtM_cut_evt; [exact MOK3 | eapply CMPO with (dX := dX3) (dY := mkMPD (SP + -120) 1 1 (SP + -124) [Z_to_bv 64 0] t180 LStatic) (LB := LB3);
      rewrite ?(unsigned_lit (SP + -288)) by lia;
      first [exact MIq3 | (left; exact MX4) | (right; exact TOPND) | (intros OWN4; exact (proj1 (HX4 OWN4)))
            | (cbn; discriminate) | (rewrite ADX3, ADX; reflexivity) | reflexivity | idtac] |].
    intros ms4 PO4. unfold mpi_cmp_post in PO4.
    destruct PO4 as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & -> & _ & _ & MI4).
    replace (ret_pc (Z_to_bv 64 136456)) with (Z_to_bv 64 136456) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT2 CS4 eq_refl) as (MT4 & NST4 & _).
    assert (OWT2 : md_own dT2 = LHeap) by (apply (out_heap m4 LB3 dT2 MT4 NST4); lia).
    assert (OWX3 : md_own dX3 = LHeap) by (apply (out_heap m4 LB3 dX3 MX4 NSX4); lia).
    assert (LL4 : loop_loc dX3 dY dZ dT2 n t zp).
    { apply (loop_loc_X dX dY dZ dT2 n t zp dX3); [apply (loop_loc_T dX dY dZ dT n t zp dT2); [exact LLq| exact OWT2| lia]
      | exact OWX3 | lia]. }
    match goal with |- context [Z_to_bv 64 (Z.sgn ?v)] =>
      destruct (Z.lt_trichotomy v 0) as [NEG4 | [ZER4 | POS4]];
      [rewrite (Z.sgn_neg v NEG4) | rewrite ZER4; change (Z.sgn 0) with 0 | rewrite (Z.sgn_pos v POS4)]
    end;
    (match goal with |- context [if ?c then _ else _] => let c' := eval vm_compute in c in change c with c'; cbn iota end).
    2,3: (eapply (L_ltest n t zp k ib j0 j64 Kont); [exact CS4 | exact LOC3 | exact LL4 | lia | lia | lia | lia | exact Krng]).
    (* X < 0: add T1 back once and decrement the quotient limb *)
    pose proof (cs_parts _ _ _ _ _ _ _ CS4) as (HP4 & TOP4 & _ & SOKq4 & MIq4 & STK4 & _ & MOK4).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT2 CS4 eq_refl) as (_ & _ & WRT4 & LOT4 & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 1%nat dY CS4 eq_refl) as (MY4 & _ & _ & _ & CRY4 & CRLY4 & _ & YLO4 & _).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 3%nat 1%nat dT2 dY CS4 eq_refl eq_refl) as (SEPTY4 & OSTY4).
    pose proof (copy_sep_of_opnd dT2 dY lo SPc OSTY4 ltac:(lia)) as CPS4.
    do 3 zstep.
    pose proof HCOPY as CPY. unfold mpi_copy_stmt_x, U_MPI_COPY in CPY.
    eapply aevtM_cut; [eapply CPY with (dX := dT2) (dY := dY) (lo := lo) (h := h3) (LB := LB3);
      rewrite ?(unsigned_lit (SP + -288)) by lia;
      first [eassumption | reflexivity | (rewrite ?ADT2, ?ADT1, ?ADT, ?ADY; reflexivity) | (rewrite TOP4; lia) | lia | idtac] |].
    intros ms5 mo5 PO5.
    binop_post PO5 m5 mo5' h5 LB5 dT5 r5 E5 MI5 ST5 MF5 HT5 HH5 MA5 OUT5 PX5 SOK5 RR5.
    replace (ret_pc (Z_to_bv 64 136472)) with (Z_to_bv 64 136472) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR5 as ((RES5 & ADT5 & _ & BLK5) & _).
    pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 3%nat dT2 m5 mo5' h5 LB5 dT5 CS4 eq_refl HH5 HT5 MF5 MA5 OUT5 PX5 SOK5 MI5 ST5 BLK5)
      as CS5.
    cbn [set_nth] in CS5.
    assert (LOC5 : locals_at [dX3; dY; dZ; dT5]).
    { unfold locals_at. cbn [map]. rewrite ADT5, ADX3, ADT2, ADT1, ADX, ADY, ADZ, ADT. reflexivity. }
    pose proof (cs_parts _ _ _ _ _ _ _ CS5) as (HP5 & TOP5 & _ & SOKq5 & MIq5 & STK5 & _ & MOK5).
    destruct RES5 as [(R5z & _ & NT5 & _) | (R5e & _)]; subst r5.
    2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
         change (negb (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0))) with true. cbn iota.
         eapply L_err; [exact CS5 | exact LOC5 | reflexivity | reflexivity | lia | exact BABS]. }
    zstep.
    change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbn iota.
    do 3 zstep.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT5 CS5 eq_refl) as (MT5 & NST5 & WRT5 & LOT5 & _).
    eapply aevtM_cut; [eapply SHL with (dX := dT5) (count := 32 * (i - t - 1)) (lo := lo) (h := h5) (LB := LB5);
      rewrite ?(unsigned_lit (SP + -288)) by lia;
      first [eassumption | reflexivity | (rewrite ?ADT5, ?ADT2, ?ADT1, ?ADT; reflexivity) | (rewrite TOP5; lia)
            | (rewrite unsigned_lit by lia; reflexivity) | lia | idtac] |].
    intros ms6 mo6 PO6.
    binop_post PO6 m6 mo6' h6 LB6 dT6 r6 E6 MI6 ST6 MF6 HT6 HH6 MA6 OUT6 PX6 SOK6 RR6.
    replace (ret_pc (Z_to_bv 64 136488)) with (Z_to_bv 64 136488) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR6 as (RES6 & KEEP6).
    pose proof KEEP6 as (ADT6 & _ & BLK6 & NT6).
    pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 3%nat dT5 m6 mo6' h6 LB6 dT6 CS5 eq_refl HH6 HT6 MF6 MA6 OUT6 PX6 SOK6 MI6 ST6 BLK6)
      as CS6.
    cbn [set_nth] in CS6.
    assert (LOC6 : locals_at [dX3; dY; dZ; dT6]).
    { unfold locals_at. cbn [map]. rewrite ADT6, ADT5, ADX3, ADT2, ADT1, ADX, ADY, ADZ, ADT. reflexivity. }
    pose proof (cs_parts _ _ _ _ _ _ _ CS6) as (HP6 & TOP6 & _ & SOKq6 & MIq6 & STK6 & _ & MOK6).
    destruct RES6 as [(R6z & _) | R6e]; subst r6.
    2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
         change (negb (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0))) with true. cbn iota.
         eapply L_err; [exact CS6 | exact LOC6 | reflexivity | reflexivity | lia | exact BABS]. }
    zstep.
    change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbn iota.
    do 5 zstep.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX3 CS6 eq_refl) as (MX6 & NSX6 & WRX6 & LOX6 & CRX6 & CRLX6 & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT6 CS6 eq_refl) as (MT6 & _ & _ & _ & CRT6 & CRLT6 & _).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0%nat 0%nat dX3 dX3 CS6 eq_refl eq_refl) as (_ & OSXX6).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0%nat 3%nat dX3 dT6 CS6 eq_refl eq_refl) as (SEPXT6 & OSXT6).
    eapply aevtM_cut; [eapply ASUB with (flip := 1) (dX := dX3) (dA := dX3) (dB := dT6) (lo := lo) (h := h6) (LB := LB6);
      rewrite ?(unsigned_lit (SP + -288)) by lia;
      first [eassumption | reflexivity | (left; reflexivity)
            | (rewrite ?ADT6, ?ADT5, ?ADT2, ?ADT1, ?ADT, ?ADX3, ?ADX; reflexivity) | (rewrite TOP6; lia) | lia | idtac] |].
    intros ms7 mo7 PO7.
    binop_post PO7 m7 mo7' h7 LB7 dX7 r7 E7 MI7 ST7 MF7 HT7 HH7 MA7 OUT7 PX7 SOK7 RR7.
    replace (ret_pc (Z_to_bv 64 136512)) with (Z_to_bv 64 136512) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR7 as (RES7 & KEEP7).
    pose proof KEEP7 as (ADX7 & _ & BLK7 & NX7).
    pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 0%nat dX3 m7 mo7' h7 LB7 dX7 CS6 eq_refl HH7 HT7 MF7 MA7 OUT7 PX7 SOK7 MI7 ST7 BLK7)
      as CS7.
    cbn [set_nth] in CS7.
    assert (LOC7 : locals_at [dX7; dY; dZ; dT6]).
    { unfold locals_at. cbn [map]. rewrite ADX7, ADT6, ADT5, ADX3, ADT2, ADT1, ADX, ADY, ADZ, ADT. reflexivity. }
    pose proof (cs_parts _ _ _ _ _ _ _ CS7) as (HP7 & TOP7 & _ & SOKq7 & MIq7 & STK7 & _ & MOK7).
    destruct RES7 as [(R7z & _) | R7e]; subst r7.
    2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
         change (negb (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0))) with true. cbn iota.
         eapply L_err; [exact CS7 | exact LOC7 | reflexivity | reflexivity | lia | exact BABS]. }
    zstep.
    change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbn iota.
    zstep.
    rewrite bv_ltu_Z, (unsigned_lit (18446744073709551615 - zp)), (unsigned_lit (4 * (i - t - 1))) by lia.
    destruct (Z.ltb_spec (18446744073709551615 - zp) (4 * (i - t - 1))) as [TRAP | NOTRAP].
    { exfalso. clear - TRAP PZtop PZ NZ Irng Tnn ACL SLO SPrng HLS. lia. }
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 2%nat dZ CS7 eq_refl) as (MZ7 & _).
    destruct MZ7 as ((_ & _ & _ & _ & _ & OWNZ7) & _). rewrite OWZ in OWNZ7. destruct OWNZ7 as (_ & _ & _ & ARRZ7).
    rewrite PZ in ARRZ7.
    pose proof (LxPMpiTac.u32rw_cell_at m7 zp (md_limbs dZ) (i - t - 1) (zp + 4 * (i - t - 1)) wq ARRZ7 NTHq ltac:(lia) eq_refl)
      as CELLq.
    pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] m7) as MU. pose proof (wmono_refl usegs m7) as WM.
    rdq ARRZ7 NTHq (i - t - 1).
    zstep.
    remember (zp + 4 * (i - t - 1)) as eq eqn:EQq.
    zstep.
    rename m0 into m8.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 2%nat dZ CS7 eq_refl) as (MZ7b & _).
    destruct MZ7b as ((_ & _ & _ & _ & _ & OWNZ7b) & _). rewrite OWZ, PZ in OWNZ7b. destruct OWNZ7b as (_ & _ & _ & ARRZ7).
    pose proof (LxPMpiTac.u32arr_upd_of_cell m7 m8 zp (md_limbs dZ) (i - t - 1) eq wq
                  (Z_to_bv 64 (bv_unsigned (sx32 wq) + -1)) ARRZ7 NTHq ltac:(lia) EQq MU WM CELLq) as ARR8.
    set (zs := upd (md_limbs dZ) (Z.to_nat (i - t - 1)) (Z_to_bv 64 (bv_unsigned (sx32 wq) + -1))) in ARR8.
    assert (WOK8 : Forall (w_ok lo SPc [dX7; dY; dZ; dT6] (Some 2%nat) false false dR []) [(eq, eq + 4)]).
    { constructor; [| constructor]. unfold w_ok. right; left. exists 2%nat, dZ. cbn [nth_error fst snd].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact OWZ|]. rewrite PZ. lia. }
    assert (IDX8 : forall (j : nat) (d d' : mpd), nth_error [dX7; dY; dZ; dT6] j = Some d ->
              nth_error [dX7; dY; set_limbs dZ zs; dT6] j = Some d' ->
              md_addr d' = md_addr d /\ md_sg d' = md_sg d /\ md_n d' = md_n d /\ md_p d' = md_p d /\
              md_pad d' = md_pad d /\ md_own d' = md_own d /\
              (~ (Some 2%nat = Some j /\ md_own d = LHeap) -> d' = d) /\
              (Some 2%nat = Some j -> md_own d = LHeap ->
                 u32arr usegs m8 (md_p d) (md_limbs d') /\ Z.of_nat (length (md_limbs d')) = md_n d)).
    { intros j d d' Ej Ej'.
      destruct j as [|[|[|[|j]]]]; cbn [nth_error] in Ej, Ej';
        [injection Ej as <-; injection Ej' as <- .. | destruct j; cbn in Ej; discriminate Ej].
      1,2,4: (refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
                 (conj (fun _ => eq_refl) (fun JE => _)))))))); discriminate JE).
      refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
        (conj (fun NOT => False_ind _ (NOT (conj eq_refl OWZ))) (fun _ _ => _)))))))).
      cbn [set_limbs md_limbs md_p md_n]. rewrite PZ.
      split; [exact ARR8| apply LxPMpiTac.upd_length_Z; exact LENZ]. }
    assert (DW8 : md_addr dR = md_addr dR /\ md_sg dR = md_sg dR /\ md_n dR = md_n dR /\ md_p dR = md_p dR /\
              md_pad dR = md_pad dR /\ md_own dR = md_own dR /\ (~ (false = true /\ md_own dR = LHeap) -> dR = dR) /\
              (false = true -> md_own dR = LHeap ->
                 u32arr usegs m8 (md_p dR) (md_limbs dR) /\ Z.of_nat (length (md_limbs dR)) = md_n dR)).
    { exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
        (conj (fun _ => eq_refl) (fun FT => False_ind _ (diff_false_true FT))))))))). }
    pose proof (mc_munch _ _ _ _ _ _ _ _ _ (Some 2%nat) false false [(eq, eq + 4)] m8 [dX7; dY; set_limbs dZ zs; dT6] dR []
                  CS7 MU WM MIq7 STK7 WOK8 eq_refl IDX8 DW8 (fun _ => eq_refl) (fun FT => False_ind _ (diff_false_true FT))) as CS8.
    assert (LOC8 : locals_at [dX7; dY; set_limbs dZ zs; dT6]).
    { unfold locals_at. cbn [map set_limbs md_addr]. rewrite ADX7, ADT6, ADT5, ADX3, ADT2, ADT1, ADX, ADY, ADZ, ADT. reflexivity. }
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX7 CS8 eq_refl) as (MX8 & NSX8 & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT6 CS8 eq_refl) as (MT8 & NST8 & _).
    assert (OWX7 : md_own dX7 = LHeap) by (apply (out_heap m8 LB7 dX7 MX8 NSX8); lia).
    assert (OWT6 : md_own dT6 = LHeap) by (apply (out_heap m8 LB7 dT6 MT8 NST8); lia).
    assert (LL8 : loop_loc dX7 dY (set_limbs dZ zs) dT6 n t zp).
    { apply (loop_loc_X dX3 dY (set_limbs dZ zs) dT6 n t zp dX7); [| exact OWX7 | lia].
      apply (loop_loc_T dX3 dY (set_limbs dZ zs) dT2 n t zp dT6); [| exact OWT6 | lia].
      apply (loop_loc_Z dX3 dY dZ dT2 n t zp zs). exact LL4. }
    eapply (L_ltest n t zp k ib j0 j64 Kont); [exact CS8 | exact LOC8 | exact LL8 | lia | lia | lia | lia | exact Krng].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ISTATE (n t zp k : Z) (j0 j64 : list byte) (i q : Z) (moq : Model) (ms : machine_state) : Prop :=
    exists (mq : mem) (hq : HST usegs L HI) (LBq : list blk) (dX dY dZ dT : mpd)
      (u0 u1 u2 j68 t160 t164 t168 t176 t180 wd : word)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 : word),
      ms = MS (mkR xra (Z_to_bv 64 SPc) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) (Z_to_bv 64 (zp + 4 * (i - t - 1))) x5 (Z_to_bv 64 (4 * t))
                 (Z_to_bv 64 (4 * (i - t - 1))) (Z_to_bv 64 (0xffffffffffffffff - zp)) (Z_to_bv 64 i) (Z_to_bv 64 (i - t - 1)) (Z_to_bv 64 zp) t3 t4 t5 t6)
             F (Z_to_bv 64 0x213e4) fc None mq (seg_rom usegs)
      /\ cstate usegs L HI h LB mo m SP lo SPc dR es mq moq hq LBq [dX; dY; dZ; dT] dR []
           (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []
      /\ locals_at [dX; dY; dZ; dT]
      /\ loop_loc dX dY dZ dT n t zp
      /\ nth_error (md_limbs dZ) (Z.to_nat (i - t - 1)) = Some wd
      /\ bv_unsigned wd mod 2^32 = q.

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
    intros n t zp k ib j0 j64 KT TNN NCAP KRNG i q mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 wq
      xra t0 t1 t2 a0 v1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 BACK IRNG IBND QRNG CSq LOC LLq ZDIG ZVAL.
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    pose proof (cs_parts _ _ _ _ _ _ _ CSq) as (_ & _ & _ & _ & MEMq & STKq & _ & MOKq).
    pose proof LOC as LOC'. unfold locals_at in LOC'. cbn in LOC'. injection LOC' as AX AY AZ AT.
    destruct LLq as (OX & NX & OY & NY & OZ & PZ & NZ & OT & NT & BPOS).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSq (eq_refl : nth_error [dX; dY; dZ; dT] 3 = Some dT))
      as ((MTq & _) & _ & _ & _ & _ & _ & HPt & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSq (eq_refl : nth_error [dX; dY; dZ; dT] 1 = Some dY))
      as ((MYq & _) & _ & _ & _ & _ & _ & HPy & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSq (eq_refl : nth_error [dX; dY; dZ; dT] 2 = Some dZ))
      as ((MZq & _) & _ & _ & _ & _ & _ & HPz & _).
    destruct MTq as (STRt & _ & _ & LENt & _ & OWNt). rewrite OT in OWNt. destruct OWNt as (_ & _ & ALt & ARRt).
    destruct MYq as (STRy & _ & _ & LENy & _ & OWNy). rewrite OY in OWNy. destruct OWNy as (_ & _ & ALy & _).
    destruct MZq as (_ & _ & _ & LENz & _ & _).
    specialize (HPt OT) as (PTpos & PTtop & _). specialize (HPy OY) as (PYpos & PYtop & _). specialize (HPz OZ) as (PZpos & PZtop & _).
    rewrite AT in STRt. rewrite AY in STRy. unfold mpi_cells in STRt, STRy.
    assert (TPnz : bv_eqb (Z_to_bv 64 (md_p dT)) (Z_to_bv 64 0) = false)
      by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    assert (TPal : Z.land (md_p dT) 3 = 0)
      by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - ALt; lia).
    assert (LIMB : forall (ws : list word) (j : Z), 0 <= j < Z.of_nat (length ws) -> exists w, nth_error ws (Z.to_nat j) = Some w).
    { intros ws j JR. destruct (nth_error ws (Z.to_nat j)) as [w|] eqn:NE; [exists w; reflexivity|].
      apply nth_error_None in NE. lia. }
    destruct (LIMB (md_limbs dT) 0 ltac:(lia)) as (w0 & W0).
    destruct (LIMB (md_limbs dT) 1 ltac:(lia)) as (w1 & W1).
    destruct (LIMB (md_limbs dY) t ltac:(lia)) as (yt & YT).
    pose proof (LxPMpiTac.u32rw_cell_at mq _ _ 0 (md_p dT) w0 ARRt W0 ltac:(lia) ltac:(lia)) as CT0.
    pose proof (munch_refl [(md_p dT, md_p dT + 4)] mq) as MU1.
    pose proof (wmono_refl usegs mq) as WM1.
    zstep. zstep. rewrite TPnz; cbv_concl_iota. zstep. zstep. rewrite TPal, bv_eqb_refl. change (negb true) with false. cbv_concl_iota.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSq (eq_refl : nth_error [dX; dY; dZ; dT] 3 = Some dT)) as ((MTq0 & _) & _).
    destruct MTq0 as (_ & _ & _ & _ & _ & OWNt0). rewrite OT in OWNt0. destruct OWNt0 as (_ & _ & _ & ARRt0).
    pose proof (LxPMpiTac.u32arr_upd_of_cell mq m1 _ _ 0 (md_p dT) w0 v1 ARRt0 W0 ltac:(lia) ltac:(lia) MU1 WM1 CT0) as ARRt1.
    assert (CS1 : CST m1 moq hq LBq [dX; dY; dZ; set_limbs dT (upd (md_limbs dT) (Z.to_nat 0) v1)] dR []
                    (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_munch mq moq hq LBq _ dR [] _ [] (Some 3%nat) false false [(md_p dT, md_p dT + 4)] m1 _ dR [] CSq MU1 WM1 MEMq STKq).
      - constructor; [| constructor]. right; left. exists 3%nat, dT.
        split; [reflexivity|]. split; [reflexivity|]. split; [exact OT|]. cbn [fst snd]. lia.
      - reflexivity.
      - intros j d d' Ej Ej'.
        destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
        + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
        + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
        + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
        + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). split.
          * intros NO. exfalso. exact (NO (conj eq_refl OT)).
          * intros _ _. cbn [set_limbs md_limbs md_p]. split; [exact ARRt1 | rewrite upd_length; exact LENt].
        + destruct j; cbn in Ej; discriminate Ej.
      - repeat (split; [reflexivity|]). intros FT; discriminate FT.
      - intros _; reflexivity.
      - intros FT; discriminate FT. }
    clear MU1 WM1 ARRt0.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS1 (eq_refl : nth_error [dX; dY; dZ; _] 1 = Some dY)) as ((MY1 & _) & _).
    destruct MY1 as (_ & _ & _ & _ & _ & OWNy1). rewrite OY in OWNy1. destruct OWNy1 as (_ & _ & _ & ARRy1).
    zstep. zstep. zstep.
    rewrite bv_ltu_Z, !unsigned_lit by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv_concl_iota.
    zstep. zstep. zstep. zstep.
    rewrite (proj2 (Z.ltb_lt 0 (md_p dY))) by lia. rewrite (proj2 (Z.ltb_ge (md_p dY + 4 * t) 1)) by lia.
    change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
    rewrite (bv_eqb_Z (Z_to_bv 64 1)), !unsigned_lit by lia. change (1 =? 0) with false. cbv_concl_iota.
    assert (TYnz : bv_eqb (Z_to_bv 64 (md_p dY)) (Z_to_bv 64 0) = false)
      by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
    assert (TYal : Z.land (md_p dY + 4 * t) 3 = 0)
      by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - ALy; lia).
    zstep. rewrite TYnz; cbv_concl_iota. zstep. zstep. rewrite TYal, bv_eqb_refl. change (negb true) with false. cbv_concl_iota.
    assert (TPm4 : bv_eqb (Z_to_bv 64 (md_p dT)) (Z_to_bv 64 (-4)) = false).
    { unfold bv_eqb. rewrite unsigned_lit by lia. change (bv_unsigned (Z_to_bv 64 (-4))) with 18446744073709551612.
      apply Z.eqb_neq. lia. }
    zstep. zstep. rewrite TPm4; cbv_concl_iota. zstep. rewrite TPnz; cbv_concl_iota.
    rdq ARRy1 YT t.
    assert (W1u : nth_error (upd (md_limbs dT) (Z.to_nat 0) v1) (Z.to_nat 1) = Some w1)
      by (rewrite <- W1; destruct (md_limbs dT); reflexivity).
    pose proof (LxPMpiTac.u32rw_cell_at m1 _ _ 1 (md_p dT + 4) w1 ARRt1 W1u ltac:(lia) ltac:(lia)) as CT1.
    clear ARRt1.
    pose proof (munch_refl [(md_p dT + 4, md_p dT + 4 + 4)] m1) as MU2.
    pose proof (wmono_refl usegs m1) as WM2.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS1 (eq_refl : nth_error [dX; dY; dZ; _] 3 = Some _)) as ((MT1 & _) & _).
    destruct MT1 as (_ & _ & _ & _ & _ & OWNt1). cbn [set_limbs md_own md_p md_limbs] in OWNt1. rewrite OT in OWNt1.
    destruct OWNt1 as (_ & _ & _ & ARRt1).
    pose proof (LxPMpiTac.u32arr_upd_of_cell m1 m2 _ _ 1 (md_p dT + 4) w1 (sx32 yt) ARRt1 W1u ltac:(lia) ltac:(lia) MU2 WM2 CT1) as ARRt2.
    assert (CS2 : CST m2 moq hq LBq [dX; dY; dZ; set_limbs dT (upd (upd (md_limbs dT) (Z.to_nat 0) v1) (Z.to_nat 1) (sx32 yt))] dR []
                    (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_munch m1 moq hq LBq _ dR [] _ [] (Some 3%nat) false false [(md_p dT + 4, md_p dT + 4 + 4)] m2 _ dR [] CS1 MU2 WM2 MEMq STKq).
      - constructor; [| constructor]. right; left. exists 3%nat, (set_limbs dT (upd (md_limbs dT) (Z.to_nat 0) v1)).
        split; [reflexivity|]. split; [reflexivity|]. split; [exact OT|]. cbn [fst snd set_limbs md_p md_n]. lia.
      - reflexivity.
      - intros j d d' Ej Ej'.
        destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
        + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
        + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
        + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
        + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). split.
          * intros NO. exfalso. exact (NO (conj eq_refl OT)).
          * intros _ _. cbn [set_limbs md_limbs md_p md_n]. split; [exact ARRt2 | rewrite !upd_length; exact LENt].
        + destruct j; cbn in Ej; discriminate Ej.
      - repeat (split; [reflexivity|]). intros FT; discriminate FT.
      - intros _; reflexivity.
      - intros FT; discriminate FT. }
    clear MU2 WM2 ARRt1.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS2 (eq_refl : nth_error [dX; dY; dZ; _] 2 = Some dZ)) as ((MZ2 & _) & _).
    destruct MZ2 as (_ & _ & _ & _ & _ & OWNz2). rewrite OZ in OWNz2. destruct OWNz2 as (_ & _ & _ & ARRz2).
    rewrite PZ in ARRz2.
    rdq ARRz2 ZDIG (i - t - 1).
    zstep. zstep. zstep.
    set (dT2 := set_limbs dT (upd (upd (md_limbs dT) (Z.to_nat 0) v1) (Z.to_nat 1) (sx32 yt))) in *.
    pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (HEAP2 & HT2 & MF2 & STAT2 & MEM2 & STK2 & _ & MOK2).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS2 (eq_refl : nth_error [dX; dY; dZ; dT2] 3 = Some dT2))
      as (MT2 & NST2 & WR2 & LO2 & CR2 & CRL2 & _).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 3 3 dT2 dT2 CS2 eq_refl eq_refl) as (SEPs & OSEP).
    assert (AT2 : md_addr dT2 = SP + -192) by exact AT.
    pose proof HMULI as MULI. unfold mpi_mul_int_stmt_g, U_MPI_MUL_INT in MULI.
    eapply aevtM_cut.
    { eapply MULI with (h := hq) (LB := LBq) (dX := dT2) (dA := dT2) (b := q) (lo := lo).
      all: rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity; try lia.
      - rewrite bv_unsigned_sx32, sxz_mod32; [exact ZVAL | apply Z.mod_pos_bound; lia].
      - rewrite bv_unsigned_sx32, ZVAL. apply sxz_zero_iff. lia.
      - rewrite AT2. reflexivity.
      - rewrite AT2. reflexivity. }
    intros ms3 moc PO3.
    binop_post PO3 m3 mo3 h3 LB3 dT3 r3 E3 MEM3 STK3 MF3 HT3 HEAP3 MT3 OUT3 PX3 STAT3 RR3.
    replace (ret_pc (Z_to_bv 64 136340)) with (Z_to_bv 64 136340) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    destruct RR3 as (RES3 & KA3 & _ & KB3 & KN3).
    assert (CS3 : CST m3 mo3 h3 LB3 [dX; dY; dZ; dT3] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [])
      by exact (mc_binop_l _ _ _ _ _ _ _ _ _ 3%nat dT2 m3 mo3 h3 LB3 dT3 CS2 eq_refl HEAP3 HT3 MF3 MT3 OUT3 PX3 STAT3 MEM3 STK3 KB3).
    pose proof (cs_parts _ _ _ _ _ _ _ CS3) as (_ & _ & _ & _ & _ & _ & _ & MOK3).
    assert (LOC3 : locals_at [dX; dY; dZ; dT3]).
    { unfold locals_at in *. cbn [map] in *. rewrite KA3. exact LOC. }
    destruct RES3 as [(R0 & VAL3 & N3) | RF].
    2:{ subst r3. change MBEDTLS_ERR_MPI_ALLOC_FAILED with (-16). zstep.
        change (negb (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0))) with true. cbv_concl_iota.
        eapply L_err; [exact CS3 | exact LOC3 | reflexivity | reflexivity | lia | exact BPOS]. }
    subst r3. zstep. rewrite bv_eqb_refl. change (negb true) with false. cbv_concl_iota.
    zstep. zstep. zstep.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CS3) as (_ & FRtp3 & FRt23 & _ & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS3 (eq_refl : nth_error [dX; dY; dZ; dT3] 3 = Some dT3))
      as (_ & NST3 & _ & _ & _ & _ & HP3 & _).
    pose (dP := mkMPD (SP + -208) 1 3 (SP + -220) [u0; u1; u2] j68 LStatic).
    assert (OPP : MpiOpnd.opnd_at usegs m3 LB3 SPc dP).
    { right. unfold MpiOpnd.stack_opnd, dP. cbn [md_own md_addr md_p md_sg md_n md_pad md_limbs].
      split; [reflexivity|]. split; [exact FRt23|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
      split; [split; [lia | unfold MPI_MAX_LIMBS; lia]|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact (u32arr_ro _ _ _ _ (LxPMpiTac.u32arr_of_rw_cells m3 (SP + -220) [u0; u1; u2] FRtp3))|].
      split; [lia|]. split; [lia|]. left; reflexivity. }
    pose proof HCMPO as CMPO. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in CMPO.
    eapply aevtM_cut_evt; [exact MOK3 | eapply CMPO with (LB := LB3) (dX := dT3) (dY := dP) | ].
    - rewrite unsigned_lit by lia. apply MpiOpnd.opnd_at_mpd. exact MT3.
    - rewrite unsigned_lit by lia. exact OPP.
    - intros OH. exact (proj1 (HP3 OH)).
    - cbn. intros OH. discriminate OH.
    - exact MEM3.
    - rewrite KA3, AT2. reflexivity.
    - reflexivity.
    - intros ms4 PO4. unfold mpi_cmp_post in PO4.
      destruct PO4 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & -> & _ & _ & _).
      replace (ret_pc (Z_to_bv 64 136356)) with (Z_to_bv 64 136356) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      zstep.
      assert (LL3 : loop_loc dX dY dZ dT3 n t zp).
      { assert (N2 : md_n dT2 = md_n dT) by reflexivity.
        pose proof (out_heap m3 LB3 dT3 MT3 NST3 ltac:(lia)) as OT3.
        unfold loop_loc. repeat (split; [assumption|]). split; [lia | exact BPOS]. }
      assert (VP : 0 <= mpd_val dP).
      { unfold mpd_val, dP. cbn [md_sg md_limbs]. pose proof (limbs_val_nonneg [u0; u1; u2]). lia. }
      destruct (Z.lt_trichotomy (mpd_val dT3 - mpd_val dP) 0) as [NEG | [ZER | POS]].
      + rewrite (Z.sgn_neg _ NEG). change (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv_concl_iota.
        eapply (L_bodyB n t zp k ib j0 j64 KT TNN NCAP KRNG); [exact CS3 | exact LOC3 | exact LL3 | lia | lia].
      + rewrite (Z.sgn_null _ ZER). change (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 0)) with false. cbv_concl_iota.
        eapply (L_bodyB n t zp k ib j0 j64 KT TNN NCAP KRNG); [exact CS3 | exact LOC3 | exact LL3 | lia | lia].
      + rewrite (Z.sgn_pos _ POS). change (bv_lts (Z_to_bv 64 0) (Z_to_bv 64 1)) with true. cbv_concl_iota.
        assert (Q1 : 1 <= q).
        { destruct (Z.eq_dec q 0) as [Q0 | QN]; [| lia]. rewrite Q0, Z.mul_0_r in VAL3. lia. }
        (* the back edge lands on 0x213d8, where the code takes one off Z.p[i-t-1] before the next pass *)
        pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS3 (eq_refl : nth_error [dX; dY; dZ; dT3] 2 = Some dZ)) as ((ATz3 & _) & _).
        destruct ATz3 as (_ & _ & _ & _ & _ & LIMBz3). rewrite OZ in LIMBz3. destruct LIMBz3 as (_ & _ & _ & ARRz3).
        rewrite PZ in ARRz3.
        pose proof (LxPMpiTac.u32rw_cell_at m3 _ _ (i - t - 1) (zp + 4 * (i - t - 1)) wq ARRz3 ZDIG ltac:(lia) ltac:(lia)) as CELLz.
        rdq ARRz3 ZDIG (i - t - 1).
        zstep.
        pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] m3) as MU4.
        pose proof (wmono_refl usegs m3) as WM4.
        set (ZA := zp + 4 * (i - t - 1)) in *. zstep. subst ZA.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        set (dec := Z_to_bv 64 (bv_unsigned (sx32 wq) + -1)) in *.
        assert (DEC : bv_unsigned dec mod 2 ^ 32 = q - 1).
        { unfold dec. rewrite Z_to_bv_unsigned, bv_unsigned_sx32. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
          rewrite ZVAL. unfold sxz. destruct (Z.ltb_spec q (2 ^ 31)); clear - Q1 QRNG; lia. }
        pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS3 (eq_refl : nth_error [dX; dY; dZ; dT3] 2 = Some dZ)) as ((ATz3' & _) & _).
        destruct ATz3' as (_ & _ & _ & _ & _ & LIMBz3'). rewrite OZ in LIMBz3'. destruct LIMBz3' as (_ & _ & _ & ARRz3').
        pose proof (LxPMpiTac.u32arr_upd_of_cell m3 m4 _ _ (i - t - 1) (zp + 4 * (i - t - 1)) wq dec ARRz3' ZDIG ltac:(lia) ltac:(lia) MU4 WM4 CELLz) as ARRz4.
        set (zs := upd (md_limbs dZ) (Z.to_nat (i - t - 1)) dec) in ARRz4.
        assert (CS4 : CST m4 mo3 h3 LB3 [dX; dY; set_limbs dZ zs; dT3] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
        { apply (mc_munch m3 mo3 h3 LB3 _ dR [] _ [] (Some 2%nat) false false [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] m4 _ dR [] CS3 MU4 WM4 MEM3 STK3).
          - constructor; [| constructor]. right; left. exists 2%nat, dZ.
            split; [reflexivity|]. split; [reflexivity|]. split; [exact OZ|]. cbn [fst snd]. lia.
          - reflexivity.
          - intros j d d' Ej Ej'.
            destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
            + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
            + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
            + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). split.
              * intros NO. exfalso. exact (NO (conj eq_refl OZ)).
              * intros _ _. cbn [set_limbs md_limbs md_p]. split; [exact ARRz4 | unfold zs; rewrite upd_length; exact LENz].
            + injection Ej as <-. injection Ej' as <-. repeat (split; [reflexivity|]). intros SJ; discriminate SJ.
            + destruct j; cbn in Ej; discriminate Ej.
          - repeat (split; [reflexivity|]). intros FT; discriminate FT.
          - intros _; reflexivity.
          - intros FT; discriminate FT. }
        apply (BACK Q1 mo3). unfold ISTATE.
        exists m4, h3, LB3, dX, dY, (set_limbs dZ zs), dT3, u0, u1, u2, j68, t160, t164, t168, t176, t180, dec.
        do 17 eexists. split; [reflexivity|].
        split; [exact CS4|]. split; [exact LOC3|]. split; [exact (loop_loc_Z dX dY dZ dT3 n t zp zs LL3)|].
        split; [unfold zs; cbn [set_limbs md_limbs]; apply nth_error_upd_same; lia | exact DEC].
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
    intros n t zp k ib j0 j64 KT TNN NCAP KRNG i q moq ms BACK IRNG IBND QRNG IST.
    destruct IST as (mq & hq & LBq & dX & dY & dZ & dT & u0 & u1 & u2 & j68 & t160 & t164 & t168 & t176 & t180 & wd
      & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x5 & -> & CSq & LOC & LLq & ZD & ZV).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    pose proof LOC as LOC'. unfold locals_at in LOC'. cbn in LOC'. injection LOC' as AX AY AZ AT.
    pose proof LLq as LL0. destruct LL0 as (OX & NX & OY & NY & OZ & PZ & NZ & OT & NT & BPOS).
    pose proof (cs_parts _ _ _ _ _ _ _ CSq) as (HEAPq & TOPq & FRMq & SOKq & MEMq & STKq & _ & MOKq).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CSq (eq_refl : nth_error [dX; dY; dZ; dT] 3 = Some dT))
      as (MTq & NSTt & WRt & _).
    zstep. zstep. zstep.
    pose proof HLSET as LSET. unfold mpi_lset_stmt, U_MPI_LSET in LSET.
    eapply aevtM_cut.
    { eapply LSET with (h := hq) (LB := LBq) (dX := dT) (z := 0) (lo := lo).
      all: rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity; try lia.
      rewrite AT. reflexivity. }
    intros ms2 moc PO2.
    binop_post PO2 m2 mo2 h2 LB2 dT2 r2 E2 MEM2 STK2 MF2 HT2 HEAP2 MT2 OUT2 PX2 STAT2 RR2.
    replace (ret_pc (Z_to_bv 64 136176)) with (Z_to_bv 64 136176) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    destruct RR2 as (RES2 & KA2 & KB2).
    assert (CS2 : CST m2 mo2 h2 LB2 [dX; dY; dZ; dT2] dR [] (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [])
      by exact (mc_binop_l _ _ _ _ _ _ _ _ _ 3%nat dT m2 mo2 h2 LB2 dT2 CSq eq_refl HEAP2 HT2 MF2 MT2 OUT2 PX2 STAT2 MEM2 STK2 KB2).
    pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (_ & _ & _ & _ & _ & _ & _ & MOK2).
    assert (LOC2 : locals_at [dX; dY; dZ; dT2]).
    { unfold locals_at in *. cbn [map] in *. rewrite KA2. exact LOC. }
    destruct RES2 as [(R0 & N2 & O2 & _) | (RF & DT2)].
    2:{ subst r2. change MBEDTLS_ERR_MPI_ALLOC_FAILED with (-16). zstep.
        change (negb (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0))) with true. cbv_concl_iota.
        eapply L_err; [exact CS2 | exact LOC2 | reflexivity | reflexivity | lia | exact BPOS]. }
    subst r2. zstep. rewrite bv_eqb_refl. change (negb true) with false. cbv_concl_iota.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CS2) as (FR0 & _ & _ & _ & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS2 (eq_refl : nth_error [dX; dY; dZ; dT2] 1 = Some dY))
      as ((MY2 & _) & _ & _ & _ & _ & _ & HPy & _).
    destruct MY2 as (STRy & _ & _ & LENy & _ & OWNy). rewrite OY in OWNy. destruct OWNy as (_ & _ & ALy & ARRy).
    specialize (HPy OY) as (PYpos & PYtop & _).
    rewrite AY in STRy. unfold mpi_cells in STRy.
    assert (LL2 : loop_loc dX dY dZ dT2 n t zp).
    { unfold loop_loc. split; [exact OX|]. split; [exact NX|]. split; [exact OY|]. split; [exact NY|].
      split; [exact OZ|]. split; [exact PZ|]. split; [exact NZ|]. split; [exact O2|]. split; [lia | exact BPOS]. }
    zstep. zstep.
    destruct (Z.eq_dec t 0) as [T0 | TPOS].
    - assert (TB : bv_eqb (Z_to_bv 64 t) (Z_to_bv 64 0) = true) by (rewrite T0; apply bv_eqb_refl).
      rewrite TB. cbv_concl_iota.
      zstep.
      eapply (L_inner_tail n t zp k ib j0 j64 KT TNN NCAP KRNG i q m2 mo2 h2 LB2 dX dY dZ dT2 u0 u1 u2 j68 t160 t164 t168 t176 t180 wd);
        [exact BACK | lia | lia | lia | exact CS2 | exact LOC2 | exact LL2 | exact ZD | exact ZV].
    - assert (TB : bv_eqb (Z_to_bv 64 t) (Z_to_bv 64 0) = false)
        by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
      rewrite TB. cbv_concl_iota.
      destruct (nth_error (md_limbs dY) (Z.to_nat (t - 1))) as [y|] eqn:YT1; [| apply nth_error_None in YT1; lia].
      zstep. zstep. zstep. zstep.
      rewrite bv_ltu_Z, !unsigned_lit by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv_concl_iota.
      zstep. zstep. zstep. zstep.
      rewrite (proj2 (Z.ltb_lt 0 (md_p dY))) by lia. rewrite (proj2 (Z.ltb_ge (md_p dY + 4 * (t - 1)) 1)) by lia.
      change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
      rewrite (bv_eqb_Z (Z_to_bv 64 1)), !unsigned_lit by lia. change (1 =? 0) with false. cbv_concl_iota.
      assert (YPnz : bv_eqb (Z_to_bv 64 (md_p dY)) (Z_to_bv 64 0) = false)
        by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
      assert (YPal : Z.land (md_p dY + 4 * (t - 1)) 3 = 0)
        by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - ALy; lia).
      zstep. rewrite YPnz; cbv_concl_iota. zstep. zstep. rewrite YPal, bv_eqb_refl. change (negb true) with false. cbv_concl_iota.
      rdq ARRy YT1 (t - 1).
      zstep.
      eapply (L_inner_tail n t zp k ib j0 j64 KT TNN NCAP KRNG i q m2 mo2 h2 LB2 dX dY dZ dT2 u0 u1 u2 j68 t160 t164 t168 t176 t180 wd);
        [exact BACK | lia | lia | lia | exact CS2 | exact LOC2 | exact LL2 | exact ZD | exact ZV].
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
    intros n t zp k ib j0 j64 KT TNN NCAP KRNG i IRNG IBND N.
    induction N as [|N' IHN]; intros moq ms NB IST.
    - apply (L_inner_body n t zp k ib j0 j64 KT TNN NCAP KRNG i 0 moq ms); [| exact IRNG | exact IBND | lia | exact IST].
      intros QPOS. exfalso. lia.
    - apply (L_inner_body n t zp k ib j0 j64 KT TNN NCAP KRNG i (Z.of_nat (S N')) moq ms); [| exact IRNG | exact IBND | lia | exact IST].
      intros _ moq' ms' IST'. apply IHN; [lia |].
      replace (Z.of_nat N') with (Z.of_nat (S N') - 1) by lia. exact IST'.
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
    intros n t zp k ib j0 j64 kont tnn nmax krng mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i qw v0
      xra t0 t1 t2 a3 a4 a6 a7 t3 t4 t5 t6 x4 x7 cst locs lloc iwin iub zdig.
    pose proof lloc as (ownX & nX & _ & _ & ownZ & pZ & nZ & _).
    pose proof (cs_parts _ _ _ _ _ _ _ cst) as (_ & _ & _ & _ & miq & stkq & _ & mokq).
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ cst) as (fr0 & fr1 & fr2 & _).
    pose proof (bv_unsigned_in_range 64 sp) as sprng. change (bv_modulus 64) with (2^64) in sprng.
    pose proof alloc_ceiling_pos as acpos.
    assert (ceil64 : alloc_ceiling < 2^64) by lia.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX cst eq_refl) as ((atX & _) & _ & _ & _ & _ & _ & heapX & _).
    destruct (heapX ownX) as (pXpos & pXtop & _ & _). clear heapX.
    destruct atX as (_ & _ & _ & lenX & _ & ownpX). rewrite ownX in ownpX. destruct ownpX as (_ & _ & pXal & arrX).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 2%nat dZ cst eq_refl) as ((atZ & _) & _ & _ & _ & _ & _ & heapZ & _).
    destruct (heapZ ownZ) as (pZpos & pZtop & _ & _). clear heapZ.
    destruct atZ as (_ & _ & _ & lenZ & _ & ownpZ). rewrite ownZ in ownpZ. destruct ownpZ as (_ & _ & pZal & arrZ).
    rewrite pZ in pZpos, pZtop, pZal, arrZ.
    unfold t2cells in fr2.
    (* T2.p (the 3-limb frame buffer at SP-220) gets v0, X.p[i-1], X.p[i]; the stores stay inside its 12 bytes *)
    pose proof (munch_refl [(SP + -220, SP + -208)] mq) as mu1. pose proof (wmono_refl usegs mq) as wm1.
    do 2 zstep. gkill trapA.
    do 2 zstep. gkill trapB.
    zstep. rewrite ?Z.shiftl_mul_pow2 by lia.
    do 4 zstep. gkill trapC.
    do 3 zstep. gkill trapD.
    zstep. gkill trapE.
    do 2 zstep. gkill trapF.
    do 2 zstep. gkill trapG.
    zstep. gkill trapH.
    destruct (nth_error (md_limbs dX) (Z.to_nat (i - 1))) as [wx1|] eqn:nthX1; [| exfalso; apply nth_error_None in nthX1; lia].
    pose proof (u32arr_read usegs m0 (md_p dX) (md_limbs dX) (i - 1) wx1 (Z_to_bv 64 ((i + 1) * 4 + md_p dX + -8)) arrX nthX1
                  ltac:(lia) ltac:(unfold wa; f_equal; lia)) as rdX1.
    zstep. clear rdX1.
    do 2 zstep. gkill trapI.
    do 2 zstep. gkill trapJ.
    destruct (nth_error (md_limbs dX) (Z.to_nat i)) as [wx0|] eqn:nthX0; [| exfalso; apply nth_error_None in nthX0; lia].
    pose proof (u32arr_read usegs _ (md_p dX) (md_limbs dX) i wx0 (Z_to_bv 64 (md_p dX + 4 * i)) arrX nthX0
                  ltac:(lia) ltac:(reflexivity)) as rdX0.
    zstep. clear rdX0 arrX.
    do 5 zstep. gkill trapK.
    zstep. rewrite ?Z.shiftl_mul_pow2 by lia.
    zstep. gkill trapL.
    pose proof (cs_frame_upd mq moq hq LBq _ dR _ _ j68 (tcells t160 t164 t168 t176 t180) (SP + -220) (SP + -208) m0
                  _ _ cst locs mu1 wm1 miq stkq ltac:(lia) ltac:(lia) fr0 eq_refl fr1 eq_refl eq_refl) as cs1.
    clear mu1 wm1.
    (* Z.p[i-t-1] += 1 *)
    replace ((i - t - 1) * 4) with (4 * (i - t - 1)) by ring.
    zstep.
    pose proof (u32arr_read usegs m0 zp (md_limbs dZ) (i - t - 1) qw (Z_to_bv 64 (zp + 4 * (i - t - 1))) arrZ zdig
                  ltac:(lia) ltac:(reflexivity)) as rdZ.
    zstep. clear rdZ.
    zstep.
    pose proof (u32arr_store_ok usegs m0 zp (md_limbs dZ) (i - t - 1) (Z_to_bv 64 (zp + 4 * (i - t - 1))) arrZ
                  ltac:(lia) ltac:(reflexivity)) as okZ.
    pose proof (u32arr_write usegs m0 zp (md_limbs dZ) (i - t - 1) (Z_to_bv 64 (bv_unsigned (sx32 qw) + 1)) arrZ
                  ltac:(lia)) as arrZ2.
    clear arrZ.
    pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] m0) as mu2.
    pose proof (wmono_refl usegs m0) as wm2.
    zstep. store_done.
    set (zs := upd (md_limbs dZ) (Z.to_nat (i - t - 1)) (Z_to_bv 64 (bv_unsigned (sx32 qw) + 1))) in arrZ2.
    assert (cs2 : CST m1 moq hq LBq [dX; dY; set_limbs dZ zs; dT] dR []
                    (LFR t k j0 j64 v0 (sx32 wx1) (sx32 wx0) j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_munch m0 moq hq LBq _ dR [] _ [] (Some 2%nat) false false _ m1 _ dR [] cs1 mu2 wm2 miq stkq).
      - constructor; [| constructor]. right; left. exists 2%nat, dZ. cbn [fst snd].
        split; [reflexivity|]. split; [reflexivity|]. split; [exact ownZ|]. rewrite pZ. lia.
      - reflexivity.
      - intros j d d' Ej Ej'.
        destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'; try (destruct j; discriminate Ej);
          injection Ej as Ej; injection Ej' as Ej'; subst d d'; repeat (split; [reflexivity|]).
        3: split; [intros c; exfalso; apply c; split; [reflexivity| exact ownZ]|].
        3: intros _ _; cbn [set_limbs md_limbs md_p]; rewrite pZ; split; [exact arrZ2| unfold zs; rewrite upd_length; exact lenZ].
        all: intros c; discriminate c.
      - repeat (split; [reflexivity|]). intros c; discriminate c.
      - intros _; reflexivity.
      - intros c; discriminate c. }
    clear mu2 wm2.
    (* fall through to 0x213d8: the do-while body opens by taking one off Z.p[i-t-1] again *)
    set (inc := Z_to_bv 64 (bv_unsigned (sx32 qw) + 1)) in *.
    assert (nthZ : nth_error zs (Z.to_nat (i - t - 1)) = Some inc).
    { unfold zs. apply nth_error_upd_same. lia. }
    pose proof (LxPMpiTac.u32rw_cell_at m1 _ _ (i - t - 1) (zp + 4 * (i - t - 1)) inc arrZ2 nthZ ltac:(lia) ltac:(lia)) as cellZ.
    rdq arrZ2 nthZ (i - t - 1).
    zstep.
    pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] m1) as mu3.
    pose proof (wmono_refl usegs m1) as wm3.
    set (za := zp + 4 * (i - t - 1)) in *. zstep. subst za.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    set (dec := Z_to_bv 64 (bv_unsigned (sx32 inc) + -1)) in *.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 2%nat (set_limbs dZ zs) cs2 eq_refl) as ((atZ1 & _) & _).
    destruct atZ1 as (_ & _ & _ & _ & _ & ownpZ1). cbn [set_limbs md_own md_p md_limbs md_n] in ownpZ1.
    rewrite ownZ in ownpZ1. destruct ownpZ1 as (_ & _ & _ & arrZ1).
    pose proof (LxPMpiTac.u32arr_upd_of_cell m1 m2 _ _ (i - t - 1) (zp + 4 * (i - t - 1)) inc dec arrZ1 nthZ ltac:(lia) ltac:(lia) mu3 wm3 cellZ) as arrZ3.
    set (zs2 := upd zs (Z.to_nat (i - t - 1)) dec) in arrZ3.
    assert (cs3 : CST m2 moq hq LBq [dX; dY; set_limbs dZ zs2; dT] dR []
                    (LFR t k j0 j64 v0 (sx32 wx1) (sx32 wx0) j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_munch m1 moq hq LBq _ dR [] _ [] (Some 2%nat) false false _ m2 _ dR [] cs2 mu3 wm3 miq stkq).
      - constructor; [| constructor]. right; left. exists 2%nat, (set_limbs dZ zs). cbn [fst snd set_limbs md_p md_n].
        split; [reflexivity|]. split; [reflexivity|]. split; [exact ownZ|]. rewrite pZ. lia.
      - reflexivity.
      - intros j d d' Ej Ej'.
        destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'; try (destruct j; discriminate Ej);
          injection Ej as Ej; injection Ej' as Ej'; rewrite <- Ej, <- Ej'; repeat (split; [reflexivity|]).
        3: split; [intros c; exfalso; apply c; split; [reflexivity| exact ownZ]|].
        3: intros _ _; cbn [set_limbs md_limbs md_p]; split; [exact arrZ3| unfold zs2, zs; rewrite !upd_length; exact lenZ].
        all: intros c; discriminate c.
      - repeat (split; [reflexivity|]). intros c; discriminate c.
      - intros _; reflexivity.
      - intros c; discriminate c. }
    pose proof (loop_loc_Z dX dY dZ dT n t zp zs2 lloc) as lloc3.
    pose proof (Z.mod_pos_bound (bv_unsigned qw) (2^32) ltac:(lia)) as qrng.
    assert (bumped : bv_unsigned inc mod 2^32 = (bv_unsigned qw mod 2^32 + 1) mod 2^32).
    { unfold inc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
      rewrite LxSoundMem.mod_mod_pow2 by lia. rewrite bv_unsigned_sx32. apply sxz_add_mod32. exact qrng. }
    assert (digit : bv_unsigned dec mod 2^32 = Z.of_nat (Z.to_nat (bv_unsigned qw mod 2^32))).
    { rewrite Z2Nat.id by lia. unfold dec. rewrite Z_to_bv_unsigned, bv_unsigned_sx32. unfold bv_wrap.
      change (bv_modulus 64) with (2^64).
      remember (bv_unsigned inc mod 2^32) as w eqn:Ew. remember (bv_unsigned qw mod 2^32) as u eqn:Eu.
      pose proof (Z.mod_pos_bound (u + 1) (2^32) ltac:(lia)) as wrng. rewrite <- bumped in wrng.
      unfold sxz. destruct (Z.ltb_spec w (2 ^ 31)); clear - bumped wrng qrng; lia. }
    assert (nthZ2 : nth_error zs2 (Z.to_nat (i - t - 1)) = Some dec).
    { unfold zs2. apply nth_error_upd_same. unfold zs. rewrite upd_length. lia. }
    apply (L_inner n t zp k ib j0 j64 kont tnn nmax krng i iwin iub (Z.to_nat (bv_unsigned qw mod 2^32)) moq).
    { rewrite Z2Nat.id by lia. lia. }
    exists m2, hq, LBq, dX, dY, (set_limbs dZ zs2), dT, v0, (sx32 wx1), (sx32 wx0), j68, t160, t164, t168, t176, t180, dec.
    do 17 eexists.
    split; [reflexivity|]. split; [exact cs3|]. split; [exact locs|]. split; [exact lloc3|]. split; [exact nthZ2| exact digit].
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
    intros n t zp k ib j0 j64 kont tnn nmax krng mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i qw
      xra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 cst locs lloc iwin iub zdig.
    pose proof lloc as (ownX & nX & _).
    pose proof (cs_parts _ _ _ _ _ _ _ cst) as (_ & _ & _ & _ & _ & _ & _ & mokq).
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ cst) as (fr0 & _).
    pose proof (bv_unsigned_in_range 64 sp) as sprng. change (bv_modulus 64) with (2^64) in sprng.
    pose proof alloc_ceiling_pos as acpos.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX cst eq_refl) as ((atX & _) & _ & _ & _ & _ & _ & heapX & _).
    destruct (heapX ownX) as (pXpos & pXtop & _ & _).
    destruct atX as (_ & _ & _ & lenX & _ & ownpX). rewrite ownX in ownpX. destruct ownpX as (_ & _ & pXal & arrX).
    assert (ceil64 : alloc_ceiling < 2^64) by lia.
    (* T2.p[0] = (i < 2 ? 0 : X.p[i-2]) *)
    do 2 zstep. if_cases geq2.
    - zify_cond geq2.
      do 2 zstep. rewrite ?Z.shiftl_mul_pow2 by lia.
      do 3 zstep. gkill trapA.
      do 4 zstep. gkill trapB.
      zstep. gkill trapC.
      zstep. gkill trapD.
      do 2 zstep. gkill trapE.
      destruct (nth_error (md_limbs dX) (Z.to_nat (i - 2))) as [wx|] eqn:nthX; [| exfalso; apply nth_error_None in nthX; lia].
      pose proof (u32arr_read usegs mq (md_p dX) (md_limbs dX) (i - 2) wx (Z_to_bv 64 (md_p dX + (i + -2) * 4)) arrX nthX
                    ltac:(lia) ltac:(unfold wa; f_equal; lia)) as rdX.
      zstep.
      exact (L_bodyA3 n t zp k ib j0 j64 kont tnn nmax krng mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i qw _
               xra t0 t1 t2 _ _ a6 a7 t3 t4 t5 t6 x4 x7 cst locs lloc iwin iub zdig).
    - do 2 zstep.
      exact (L_bodyA3 n t zp k ib j0 j64 kont tnn nmax krng mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i qw _
               xra t0 t1 t2 _ _ a6 a7 t3 t4 t5 t6 x4 x7 cst locs lloc iwin iub zdig).
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
    intros n t zp k ib j0 j64 kont tnn nmax krng mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i
      xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 x9 x10 cst locs lloc iwin iub.
    pose proof lloc as (ownX & nX & ownY & nY & ownZ & pZ & nZ & _).
    pose proof (cs_parts _ _ _ _ _ _ _ cst) as (_ & _ & _ & _ & miq & stkq & _ & mokq).
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ cst) as (fr0 & _).
    pose proof (bv_unsigned_in_range 64 sp) as sprng. change (bv_modulus 64) with (2^64) in sprng.
    pose proof alloc_ceiling_pos as acpos.
    assert (ceil64 : alloc_ceiling < 2^64) by lia.
    pose proof locs as addrs. unfold locals_at in addrs. cbn [map] in addrs.
    injection addrs as adX adY adZ adT.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX cst eq_refl) as ((atX & _) & _ & _ & _ & _ & _ & heapX & _).
    destruct (heapX ownX) as (pXpos & pXtop & _ & _). clear heapX.
    destruct atX as (sX & _ & _ & lenX & _ & ownpX). rewrite ownX in ownpX. destruct ownpX as (_ & _ & pXal & arrX).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 1%nat dY cst eq_refl) as ((atY & _) & _ & _ & _ & _ & _ & heapY & _).
    destruct (heapY ownY) as (pYpos & pYtop & _ & _). clear heapY.
    destruct atY as (sY & _ & _ & lenY & _ & ownpY). rewrite ownY in ownpY. destruct ownpY as (_ & _ & pYal & arrY).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 2%nat dZ cst eq_refl) as ((atZ & _) & _ & _ & _ & _ & _ & heapZ & _).
    destruct (heapZ ownZ) as (pZpos & pZtop & _ & _). clear heapZ.
    destruct atZ as (_ & _ & _ & lenZ & _ & ownpZ). rewrite ownZ in ownpZ. destruct ownpZ as (_ & _ & pZal & arrZ).
    rewrite pZ in pZpos, pZtop, pZal, arrZ.
    rewrite adX in sX. rewrite adY in sY. unfold mpi_cells in sX, sY.
    (* X.p + 4i and the UBSan checks on it, then Y.p + 4t *)
    do 3 zstep. rewrite ?Z.shiftl_mul_pow2 by lia. replace (i * 2 ^ 2) with (4 * i) by ring.
    do 4 zstep.
    replace (0 <? md_p dX) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    gkill trA.
    do 5 zstep. gkill trB.
    zstep. gkill trC.
    do 2 zstep. gkill trD.
    do 3 zstep. gkill trE.
    do 4 zstep. gkill trF.
    zstep. gkill trG.
    do 2 zstep. gkill trH.
    destruct (nth_error (md_limbs dX) (Z.to_nat i)) as [xi|] eqn:nthXi; [| exfalso; apply nth_error_None in nthXi; lia].
    pose proof (u32arr_read usegs mq (md_p dX) (md_limbs dX) i xi (Z_to_bv 64 (md_p dX + 4 * i)) arrX nthXi
                  ltac:(lia) ltac:(reflexivity)) as rdXi.
    zstep. clear rdXi.
    destruct (nth_error (md_limbs dY) (Z.to_nat t)) as [yt|] eqn:nthYt; [| exfalso; apply nth_error_None in nthYt; lia].
    pose proof (u32arr_read usegs mq (md_p dY) (md_limbs dY) t yt (Z_to_bv 64 (md_p dY + 4 * t)) arrY nthYt
                  ltac:(lia) ltac:(reflexivity)) as rdYt.
    zstep. clear rdYt.
    do 3 zstep.
    replace (i + 1 + (18446744073709551616 - (t + 2))) with (18446744073709551616 + (i - t - 1)) by ring.
    rewrite zbv_add_modulus.
    (* X.p[i] >= Y.p[t]: the digit is 0xffffffff; otherwise the capped quotient. All three paths end at the
       store into Z.p[i-t-1]. *)
    if_cases xgey; clear xgey.
    1: (do 4 zstep; gkill trI;
        zstep; rewrite ?Z.shiftl_mul_pow2 by lia; replace ((i - t - 1) * 2 ^ 2) with (4 * (i - t - 1)) by ring;
        zstep; gkill trJ;
        do 2 zstep).
    2: (do 2 zstep; rewrite ?Z.shiftl_mul_pow2 by lia;
        do 3 zstep; gkill trK;
        do 4 zstep; gkill trL;
        zstep; gkill trM;
        zstep; gkill trN;
        do 2 zstep; gkill trO;
        do 4 zstep; gkill trP;
        zstep; rewrite ?Z.shiftl_mul_pow2 by lia; replace ((i - t - 1) * 2 ^ 2) with (4 * (i - t - 1)) by ring;
        zstep; gkill trQ;
        destruct (nth_error (md_limbs dX) (Z.to_nat (i - 1))) as [xi1|] eqn:nthXi1;
          [| exfalso; apply nth_error_None in nthXi1; lia];
        pose proof (u32arr_read usegs mq (md_p dX) (md_limbs dX) (i - 1) xi1 (Z_to_bv 64 (md_p dX + (i + -1) * 4)) arrX nthXi1
                      ltac:(lia) ltac:(unfold wa; f_equal; lia)) as rdXi1;
        zstep; clear rdXi1;
        do 7 zstep;
        if_cases cap; clear cap; [zstep | do 2 zstep]).
    all: pose proof (u32arr_store_ok usegs mq zp (md_limbs dZ) (i - t - 1) (Z_to_bv 64 (zp + 4 * (i - t - 1))) arrZ
                       ltac:(lia) ltac:(reflexivity)) as okZ.
    all: clear sX sY arrX arrY.
    all: pose proof (munch_refl [(zp + 4 * (i - t - 1), zp + 4 * (i - t - 1) + 4)] mq) as mu1.
    all: pose proof (wmono_refl usegs mq) as wm1.
    all: zstep.
    all: lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
           pose proof (u32arr_write usegs mq zp (md_limbs dZ) (i - t - 1) v arrZ ltac:(lia)) as arrZ1;
           clear arrZ; store_done;
           set (zs := upd (md_limbs dZ) (Z.to_nat (i - t - 1)) v) in arrZ1;
           assert (nthZ : nth_error zs (Z.to_nat (i - t - 1)) = Some v) by (unfold zs; apply nth_error_upd_same; lia)
         end.
    all: try (lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x212dc) _ _ _ _) => zstep end).
    all: assert (cs1 : CST m0 moq hq LBq [dX; dY; set_limbs dZ zs; dT] dR []
                         (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) [])
           by (apply (mc_munch mq moq hq LBq _ dR [] _ [] (Some 2%nat) false false _ m0 _ dR [] cst mu1 wm1 miq stkq);
               [ constructor; [| constructor]; right; left; exists 2%nat, dZ; cbn [fst snd];
                 split; [reflexivity|]; split; [reflexivity|]; split; [exact ownZ|]; rewrite pZ; lia
               | reflexivity
               | intros j d d' Ej Ej';
                 destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'; try (destruct j; discriminate Ej);
                 injection Ej as Ej; injection Ej' as Ej'; subst d d'; repeat (split; [reflexivity|]);
                 [ intros c; discriminate c
                 | intros c; discriminate c
                 | split; [intros c; exfalso; apply c; split; [reflexivity| exact ownZ]
                          | intros _ _; cbn [set_limbs md_limbs md_p]; rewrite pZ; split;
                            [exact arrZ1| unfold zs; rewrite upd_length; exact lenZ]]
                 | intros c; discriminate c ]
               | repeat (split; [reflexivity|]); intros c; discriminate c
               | intros _; reflexivity
               | intros c; discriminate c ]).
    all: exact (L_bodyA2 n t zp k ib j0 j64 kont tnn nmax krng m0 moq hq LBq dX dY (set_limbs dZ zs) dT u0 u1 u2 j68
                  t160 t164 t168 t176 t180 i _ xra t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 x4 x7 cs1 locs
                  (loop_loc_Z dX dY dZ dT n t zp zs lloc) iwin iub nthZ).
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
    intros n t zp k j0 j64 tnn nmax krng D.
    induction D as [|D more]; intros mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i
      xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 x9 x10 fuel cst locs lloc iwin.
    { exfalso. cbn [Z.of_nat] in fuel. lia. }
    assert (later : KONT n t zp k (i - 1) j0 j64).
    { intros mq' moq' hq' LBq' dX' dY' dZ' dT' u0' u1' u2' j68' t160' t164' t168' t176' t180' i'
        xra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x4' x7' x9' x10' cst' locs' lloc' iwin' inmax'.
      exact (more mq' moq' hq' LBq' dX' dY' dZ' dT' u0' u1' u2' j68' t160' t164' t168' t176' t180' i'
               xra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x4' x7' x9' x10'
               ltac:(lia) cst' locs' lloc' ltac:(lia)). }
    exact (L_bodyA n t zp k (i - 1) j0 j64 later tnn nmax krng mq moq hq LBq dX dY dZ dT u0 u1 u2 j68 t160 t164 t168 t176 t180 i
             xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x7 x9 x10 cst locs lloc iwin ltac:(lia)).
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
    intros n t zp k mq moq hq LBq dX dY dZ dT j0 w8 w16 w24 w40 w48 j64 u0 u1 u2 j68 t160 t164 t168 t176 t180
      xra x4 x9 x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 STq LOCS LLq TN NMAX KRNG.
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (HPq & TOPq & FRMq & SOKq & MIq & STKq & _ & MOKq).
    pose proof LOCS as ADDRS. unfold locals_at in ADDRS. cbn in ADDRS. injection ADDRS as AX AY AZ AT.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ STq (eq_refl : nth_error [dX; dY; dZ; dT] 1 = Some dY))
      as (YAT & YNS & _ & _ & _ & _ & YHEAP & _).
    pose proof LLq as (XOWN & XN & YOWN & YN & ZOWN & ZP & ZN & TOWN & TNn & BABS).
    destruct (YHEAP YOWN) as (YP0 & YCEIL & _).
    do 3 zstep.
    pose proof HSHR as SHR. unfold mpi_shift_r_stmt, U_MPI_SHIFT_R in SHR.
    eapply aevtM_cut_evt; [exact MOKq | eapply SHR with (LB := LBq) (dX := dY) (count := 32 * (n - t)) (lo := lo);
      rewrite ?AY, ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity; try lia |].
    intros ms' PO. unfold mpi_shift_r_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & ys & -> & MU2 & WM2 & MI2 & ST2 & YAT2 & YLEN & YVAL).
    rewrite ?(unsigned_lit (SP + -288)) in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 135588)) with (Z_to_bv 64 135588) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CS2 : CST m2 moq hq LBq [dX; set_limbs dY ys; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { assert (YARR : u32arr usegs m2 (md_p dY) ys /\ Z.of_nat (length ys) = md_n dY).
      { destruct YAT2 as ((_ & _ & _ & YLEN2 & _ & YOWNF) & _). cbn [md_own md_limbs md_p md_n] in YLEN2, YOWNF.
        rewrite YOWN in YOWNF. destruct YOWNF as (_ & _ & _ & YARR). split; [exact YARR| exact YLEN2]. }
      apply (mc_munch mq moq hq LBq _ dR [] _ [] (Some 1%nat) false false _ m2 _ dR [] STq MU2 WM2 MI2 ST2).
      - constructor; [left; cbn [fst snd]; lia|].
        constructor; [right; left; exists 1%nat, dY; cbn [fst snd]; repeat split; [exact YOWN| lia| lia]|].
        constructor.
      - reflexivity.
      - intros j d d' Ej Ej'.
        destruct j as [|[|[|[|j]]]]; cbn [nth_error] in Ej, Ej'; [| | | | destruct j; discriminate Ej].
        all: injection Ej as <-; injection Ej' as <-; do 6 (split; [reflexivity|]).
        2: split; [intros NOTH; exfalso; apply NOTH; split; [reflexivity| exact YOWN]| intros _ _; exact YARR].
        all: split; [intros _; reflexivity| intros SOMEj; discriminate SOMEj].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros FLS; discriminate FLS].
      - intros _; reflexivity.
      - intros FLS; discriminate FLS. }
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CS2) as (Fcs0 & Ftpc & Ft2 & Ftc & REGq).
    do 3 zstep.
    rewrite bv_ltu_Z, !unsigned_lit by lia.
    destruct (Z.ltb_spec t n) as [TLT| TGE]; cbn [negb].
    2: { eapply L_fin; [exact CS2| exact LOCS| reflexivity| exact KRNG| exact BABS]. }
    clear MU2 WM2. pose proof (munch_refl [(SPc + 8, SPc + 56)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    do 15 zstep.
    rewrite lxor_allones64 in Fcs0 by lia.
    replace (18446744073709551615 - (t + 1)) with (2^64 - (t + 2)) in Fcs0 by lia.
    assert (W48 : Z_to_bv 64 (((t + -1) mod 18446744073709551616) ≪ 2) = Z_to_bv 64 (4 * (t - 1))).
    { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
      rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_mod_idemp_l by lia. f_equal. lia. }
    rewrite W48 in Fcs0.
    replace (Z_to_bv 64 (t ≪ 2)) with (Z_to_bv 64 (4 * t)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (CS3 : CST m0 moq hq LBq [dX; set_limbs dY ys; dZ; dT] dR []
      (LFR t k j0 j64 u0 u1 u2 j68 (tcells t160 t164 t168 t176 t180)) []).
    { unfold lframe.
      apply (cs_frame_upd m2 moq hq LBq _ dR _ _ j68 _ (SPc + 8) (SPc + 56) m0 _ _ CS2 LOCS MU WM MI2 ST2);
        [lia| lia| exact Fcs0| reflexivity| exact Ftpc| reflexivity| reflexivity]. }
    eapply (L_iloop n t zp k j0 j64 ltac:(lia) NMAX KRNG (Z.to_nat (n - t))); [lia| exact CS3| exact LOCS| apply loop_loc_Ys; exact LLq| lia].
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
    intros n t zp k vy D.
    induction D as [|D IHD]; intros mq moq hq LBq dX dY dZ dT j0 w8 w16 w24 w40 w48 j64 u0 u1 u2 j68 t160 t164 t168 t176 t180
      xra x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 STq LOCS LLq TN NMAX KRNG XVAL YVAL VYPOS.
    { exfalso. cbn [Z.of_nat] in XVAL. lia. }
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (HPq & TOPq & FRMq & SOKq & MIq & STKq & _ & MOKq).
    pose proof LOCS as ADDRS. unfold locals_at in ADDRS. cbn in ADDRS. injection ADDRS as AX AY AZ AT.
    pose proof LLq as (XOWN & XN & YOWN & YN & ZOWN & ZP & ZN & TOWN & TNn & BABS).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ STq (eq_refl : nth_error [dX; dY; dZ; dT] 0 = Some dX))
      as (XAT & XNS & XWR & XLO & XCR & XCRL & XHEAP & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ STq (eq_refl : nth_error [dX; dY; dZ; dT] 1 = Some dY))
      as (YAT & YNS & _ & _ & YCR & YCRL & YHEAP & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ STq (eq_refl : nth_error [dX; dY; dZ; dT] 2 = Some dZ))
      as (ZAT & _ & _ & _ & _ & _ & ZHEAP & _).
    destruct (XHEAP XOWN) as (XP0 & XCEIL & _).
    destruct (YHEAP YOWN) as (YP0 & YCEIL & _).
    destruct (ZHEAP ZOWN) as (ZP0 & ZCEIL & _).
    do 3 zstep.
    pose proof HCMP as CMP. unfold mpi_cmp_mpi_stmt, U_MPI_CMP_MPI in CMP.
    eapply aevtM_cut_evt; [exact MOKq | eapply CMP with (LB := LBq) (dX := dX) (dY := dY);
      rewrite ?AX, ?AY; try eassumption; try reflexivity; intros _; assumption |].
    intros ms' PO. unfold mpi_cmp_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & _).
    replace (ret_pc (Z_to_bv 64 0x20fac)) with (Z_to_bv 64 0x20fac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep.
    destruct (Z.ltb_spec (mpd_val dX) (mpd_val dY)) as [XLTY| YLEX].
    { rewrite (Z.sgn_neg (mpd_val dX - mpd_val dY)) by lia.
      replace (bv_lts (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity). cbv iota.
      eapply L_setup; [exact STq| exact LOCS| exact LLq| lia| lia| exact KRNG]. }
    assert (SGN : 0 <= Z.sgn (mpd_val dX - mpd_val dY) <= 1).
    { destruct (Z.eq_dec (mpd_val dX) (mpd_val dY)) as [EQV| NEV].
      - rewrite EQV, Z.sub_diag. cbn. lia.
      - rewrite Z.sgn_pos by lia. lia. }
    rewrite bv_lts_zero_r, unsigned_lit by lia.
    replace (2^63 <=? Z.sgn (mpd_val dX - mpd_val dY)) with false by (symmetry; apply Z.leb_gt; lia). cbv iota.
    zstep.
    rewrite bv_ltu_Z, !unsigned_lit by lia.
    replace (18446744073709551615 - zp <? 4 * (n - t)) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    pose proof ZAT as ((_ & _ & _ & ZLEN & _ & ZOWNF) & _). rewrite ZOWN in ZOWNF. destruct ZOWNF as (_ & _ & _ & ZARR).
    destruct (nth_error (md_limbs dZ) (Z.to_nat (n - t))) as [wz|] eqn:NTHZ;
      [| apply nth_error_None in NTHZ; lia].
    pose proof (LxPMpiTac.u32rw_cell_at mq (md_p dZ) (md_limbs dZ) (n - t) (zp + 4 * (n - t)) wz ZARR NTHZ ltac:(lia) ltac:(lia)) as ZC.
    clear ZARR.
    pose proof (munch_refl [(zp + 4 * (n - t), zp + 4 * (n - t) + 4)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    clear HPq SOKq. remember (zp + 4 * (n - t)) as ea eqn:EA.
    do 3 zstep.
    pose proof ZAT as ((_ & _ & _ & _ & _ & ZOWNF) & _). rewrite ZOWN in ZOWNF. destruct ZOWNF as (_ & _ & _ & ZARR).
    pose proof (LxPMpiTac.u32arr_upd_of_cell mq m0 (md_p dZ) (md_limbs dZ) (n - t) ea wz _ ZARR NTHZ ltac:(lia) ltac:(lia) MU WM ZC) as ZARR2.
    clear ZARR.
    set (zs := upd (md_limbs dZ) (Z.to_nat (n - t)) (Z_to_bv 64 (bv_unsigned (sx32 wz) + 1))) in ZARR2.
    assert (CS3 : CST m0 moq hq LBq [dX; dY; set_limbs dZ zs; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { assert (ZLEN2 : Z.of_nat (length zs) = md_n dZ) by (subst zs; rewrite upd_length; exact ZLEN).
      apply (mc_munch mq moq hq LBq _ dR [] _ [] (Some 2%nat) false false _ m0 _ dR [] STq MU WM MIq STKq).
      - constructor; [right; left; exists 2%nat, dZ; cbn [fst snd]; repeat split; [exact ZOWN| lia| lia]| constructor].
      - reflexivity.
      - intros j d d' Ej Ej'.
        destruct j as [|[|[|[|j]]]]; cbn [nth_error] in Ej, Ej'; [| | | | destruct j; discriminate Ej].
        all: injection Ej as <-; injection Ej' as <-; do 6 (split; [reflexivity|]).
        3: split; [intros NOTH; exfalso; apply NOTH; split; [reflexivity| exact ZOWN]| intros _ _; split; [exact ZARR2| exact ZLEN2]].
        all: split; [intros _; reflexivity| intros SOMEj; discriminate SOMEj].
      - do 6 (split; [reflexivity|]). split; [intros _; reflexivity| intros FLS; discriminate FLS].
      - intros _; reflexivity.
      - intros FLS; discriminate FLS. }
    clear ZC MU WM ZARR2 TOPq FRMq MIq STKq MOKq XAT YAT ZAT.
    pose proof (cs_parts _ _ _ _ _ _ _ CS3) as (HP3 & TOP3 & FRM3 & SOK3 & MI3 & STK3 & _ & MOK3).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS3 (eq_refl : nth_error [dX; dY; set_limbs dZ zs; dT] 0 = Some dX))
      as (XAT3 & _ & XWR3 & XLO3 & XCR3 & XCRL3 & _ & _).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ _ _ CS3 (eq_refl : nth_error [dX; dY; set_limbs dZ zs; dT] 1 = Some dY))
      as (YAT3 & _ & _ & _ & YCR3 & YCRL3 & _ & _).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0%nat 0%nat _ _ CS3 eq_refl eq_refl) as (_ & OXX).
    pose proof (mc_opnd_sep_ll _ _ _ _ _ _ _ _ _ 0%nat 1%nat _ _ CS3 eq_refl eq_refl) as (SXY & OXY).
    do 5 zstep.
    pose proof HAS as ASUB. unfold add_sub_mpi_stmt, U_ADD_SUB_MPI in ASUB.
    specialize (ASUB (-1) (or_intror eq_refl)).
    eapply aevtM_cut; [eapply ASUB with (h := hq) (LB := LBq) (dX := dX) (dA := dX) (dB := dY) (lo := lo) (m := m0) (mo := moq);
      rewrite ?AX, ?AY, ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity; try lia;
      try (left; reflexivity); try (rewrite <- AX; assumption); rewrite <- AY; assumption |].
    intros ms' mo' PO.
    binop_post PO m4 mo4 h4 LB4 dX4 r E MI4 ST4 MF4 HT4 HH4 MA4 OUT4 PX4 SOK4 RR.
    replace (ret_pc (Z_to_bv 64 135124)) with (Z_to_bv 64 135124) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR as (RVAL & KEEP4).
    pose proof KEEP4 as (KADDR & KPAD & KBLK & KN).
    assert (CS4 : CST m4 mo4 h4 LB4 [dX4; dY; set_limbs dZ zs; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { exact (mc_binop_l m0 moq hq LBq _ dR [] _ [] 0%nat dX m4 mo4 h4 LB4 dX4 CS3 eq_refl HH4 HT4 MF4 MA4 OUT4 PX4 SOK4 MI4 ST4 KBLK). }
    pose proof (cs_parts _ _ _ _ _ _ _ CS4) as (_ & _ & _ & _ & _ & _ & _ & MOK4).
    zstep. zstep.
    assert (LOCS4 : locals_at [dX4; dY; set_limbs dZ zs; dT]).
    { unfold locals_at in *. cbn [map] in *. rewrite KADDR. exact LOCS. }
    destruct RVAL as [(R0 & VAL4)| RFAIL].
    2: { subst r. replace (bv_eqb (Z_to_bv 64 MBEDTLS_ERR_MPI_ALLOC_FAILED) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
         cbv iota. zstep.
         eapply L_c0; [exact CS4| exact LOCS4| reflexivity| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia| exact BABS]. }
    subst r. replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity). cbv iota.
    subst ea.
    pose proof OUT4 as (_ & NS4 & _).
    assert (OWN4 : md_own dX4 = LHeap) by (apply (out_heap m4 LB4 dX4 MA4 NS4); lia).
    assert (LL4 : loop_loc dX4 dY (set_limbs dZ zs) dT n t zp).
    { apply (loop_loc_X dX dY _ dT n t zp dX4); [apply loop_loc_Z; exact LLq| exact OWN4| exact KN]. }
    rewrite Nat2Z.inj_succ, Z.mul_succ_l in XVAL.
    remember (Z.of_nat D * vy) as DV eqn:DVE.
    eapply IHD; [exact CS4| exact LOCS4| exact LL4| lia| lia| exact KRNG| | exact YVAL| exact VYPOS].
    rewrite DVE in *. lia.
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
    intros k zp mq moq hq LBq dX dY dZ dT j0 w8 w16 w24 w32 w40 w48 w56 j64 u0 u1 u2 j68 t160 t164 t168 t176 t180
      xra x5 x6 x7 x8 x9 x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      STq LOCS OWX OWY OWZ PZ OWT NT2 NYX NXZ VX VY KR BPOS.
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (HPq & TOPq & FRMq & SOKq & MIq & STKq & _ & MOKq).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    assert (ADDR4 : md_addr dX = SP + -144 /\ md_addr dY = SP + -160 /\ md_addr dZ = SP + -176 /\ md_addr dT = SP + -192).
    { unfold locals_at in LOCS. cbn in LOCS. injection LOCS as E1 E2 E3 E4. tauto. }
    destruct ADDR4 as (AX & AY & AZ & AT).
    pose proof (struct_cells _ _ _ _ _ _ _ 0%nat dX STq eq_refl) as (CX & SGX & NXr & _ & HPX).
    pose proof (struct_cells _ _ _ _ _ _ _ 1%nat dY STq eq_refl) as (CY & SGY & NYr & _ & HPY).
    pose proof (struct_cells _ _ _ _ _ _ _ 2%nat dZ STq eq_refl) as (_ & _ & NZr & _ & _).
    destruct (HPY OWY) as (YP0 & NY1). destruct (HPX OWX) as (XP0 & NX1).
    rewrite AX in CX. rewrite AY in CY. unfold mpi_cells in CX, CY.
    pose (n := md_n dX - 1). assert (En : md_n dX = n + 1) by (unfold n; lia). clearbody n.
    pose (t := md_n dY - 1). assert (Et : md_n dY = t + 1) by (unfold t; lia). clearbody t.
    zstep. zstep. rewrite !zx16_small by (unfold MPI_MAX_LIMBS in *; lia). rewrite En, Et.
    do 5 zstep.
    assert (E9 : Z_to_bv 64 ((n + 1) mod 18446744073709551616 - (t + 1) mod 18446744073709551616) = Z_to_bv 64 (n - t)).
    { f_equal. rewrite !Z.mod_small by (unfold MPI_MAX_LIMBS in *; lia). lia. }
    assert (E6 : Z_to_bv 64 ((((n + 1) mod 18446744073709551616 - (t + 1) mod 18446744073709551616) mod 18446744073709551616) ≪ 5) = Z_to_bv 64 (32 * (n - t))).
    { f_equal. rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by (unfold MPI_MAX_LIMBS in *; lia). lia. }
    rewrite E9, E6. clear E9 E6.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 1%nat dY STq eq_refl) as (MAY & NSY & WRY & PLY & CRY & CRLY & HFY & LAY1 & LAY2 & LAY3).
    pose proof HSHL as SHL. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SHL.
    eapply aevtM_cut; [eapply SHL with (dX := dY) (count := 32 * (n - t)) (lo := lo) (LB := LBq) (h := hq) (m := mq) (mo := moq);
      rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity | ].
    all: try (rewrite AY; reflexivity).
    1: unfold MPI_MAX_LIMBS in *; lia.
    1: lia.
    1: rewrite TOPq; lia.
    1: lia.
    intros ms' mo' PO.
    binop_post PO m2 mo2 h2 LB2 dY2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
    replace (ret_pc (Z_to_bv 64 135044)) with (Z_to_bv 64 135044) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR as (RES & KEEP2). pose proof KEEP2 as (KA2 & KP2 & KB2 & KN2).
    pose proof (mc_binop_l mq moq hq LBq [dX; dY; dZ; dT] dR [] _ [] 1%nat dY m2 mo2 h2 LB2 dY2 STq eq_refl HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2 KB2) as CS2.
    cbn [set_nth] in CS2.
    assert (LOC2 : locals_at [dX; dY2; dZ; dT]).
    { unfold locals_at in *. cbn in *. rewrite KA2. exact LOCS. }
    pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (_ & _ & _ & _ & _ & _ & _ & MOK2).
    destruct RES as [(R0 & VAL2 & SG2 & N2) | RERR].
    2: { subst r. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
         match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
         eapply L_err with (r := -16); [exact CS2 | exact LOC2 | reflexivity | reflexivity | lia | exact BPOS]. }
    subst r.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CS2) as (Fcs0 & Ftpc & Ft2 & Ftc & REGq).
    pose proof (munch_refl [(SP + -288, SP + -220)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
    zstep. zstep. zstep. do 3 zstep.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 2%nat dZ STq eq_refl) as (_ & _ & _ & _ & _ & _ & HFZ & _).
    destruct (HFZ OWZ) as (ZP0 & ZP1 & _).
    pose proof (@alloc_ceiling_hi L) as ACH.
    assert (E9 : Z_to_bv 64 (((n - t) mod 18446744073709551616) ≪ 2) = Z_to_bv 64 (4 * (n - t))).
    { f_equal. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (unfold MPI_MAX_LIMBS in *; lia). lia. }
    assert (E4 : Z_to_bv 64 (zp + ((n - t) mod 18446744073709551616) ≪ 2) = Z_to_bv 64 (zp + 4 * (n - t))).
    { f_equal. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (unfold MPI_MAX_LIMBS in *; lia). lia. }
    assert (E8 : Z_to_bv 64 (Z.lxor (zp mod 18446744073709551616) 18446744073709551615) = Z_to_bv 64 (18446744073709551615 - zp)).
    { f_equal. rewrite Z.mod_small by lia. apply lxor_allones64. lia. }
    rewrite E9, E4, E8. clear E9 E4 E8.
    assert (CS3 : CST m1 mo2 h2 LB2 [dX; dY2; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 (Z_to_bv 64 k); C8 w40; C8 w48; C8 (Z_to_bv 64 t); CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { eapply cs_frame_upd; [exact CS2 | exact LOC2 | exact MU | exact WM | eassumption | eassumption | lia | lia
        | exact Fcs0 | reflexivity | exact Ftpc | reflexivity | reflexivity]. }
    assert (VY2 : 0 < mpd_val dY2).
    { rewrite VAL2. apply Z.mul_pos_pos; [exact VY | apply Z.pow_pos_nonneg; lia]. }
    assert (OWY2 : md_own dY2 = LHeap).
    { apply (out_heap m2 LB2 dY2 MA2); [exact (proj1 (proj2 OUT2)) | lia]. }
    eapply (L_loop1 n t zp k (mpd_val dY2) (Z.to_nat (mpd_val dX / mpd_val dY2 + 1))).
    - exact CS3.
    - exact LOC2.
    - unfold loop_loc. repeat split; try assumption; lia.
    - lia.
    - unfold MPI_MAX_LIMBS in *; lia.
    - exact KR.
    - split; [exact VX|].
      assert (QN : 0 <= mpd_val dX / mpd_val dY2) by (apply Z.div_pos; lia).
      rewrite Z2Nat.id by lia.
      pose proof (Z.div_mod (mpd_val dX) (mpd_val dY2) ltac:(lia)) as DM.
      pose proof (Z.mod_pos_bound (mpd_val dX) (mpd_val dY2) VY2) as MB.
      nia.
    - reflexivity.
    - exact VY2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma val_lval : forall mq LBq d, mpd_at usegs mq LBq d -> md_sg d = 1 -> mpd_val d = lval (md_limbs d) (md_n d).
  Proof using.
    intros mq LBq d ((_ & _ & _ & LEN & _) & _) SG1.
    unfold mpd_val, lval. rewrite SG1, Z.mul_1_l, <- LEN, Nat2Z.id, firstn_all. reflexivity.
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
    intros zp mq moq hq LBq dX dY dZ dT j0 w8 w16 w24 w32 w40 w48 w56 j64 u0 u1 u2 j68 t160 t164 t168 t176 t180
      xra x4 x5 x6 x7 x8 x9 x10 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      STq LOCS OWX OWY OWZ PZ OWT NT2 NYX NXZ SG1X SG1Y VYX BPOS.
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (HPq & TOPq & FRMq & SOKq & MIq & STKq & _ & MOKq).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    assert (ADDR4 : md_addr dX = SP + -144 /\ md_addr dY = SP + -160 /\ md_addr dZ = SP + -176 /\ md_addr dT = SP + -192).
    { unfold locals_at in LOCS. cbn in LOCS. injection LOCS as E1 E2 E3 E4. tauto. }
    destruct ADDR4 as (AX & AY & AZ & AT).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 1%nat dY STq eq_refl) as (MAY & NSY & WRY & PLY & CRY & CRLY & HFY & LAY1 & LAY2 & LAY3).
    pose proof MAY as ((CY & _ & _ & LENY & NYr & OWNY) & _).
    rewrite OWY in OWNY. destruct OWNY as (NY1 & INY & ALY & ARRY).
    destruct (HFY OWY) as (YP0 & YPC & _).
    rewrite AY in CY. unfold mpi_cells in CY.
    zstep. zstep. rewrite zx16_small by (unfold MPI_MAX_LIMBS in *; lia).
    zstep.
    pose proof HCBL as CBL. unfold mpi_core_bitlen_stmt, U_MPI_CORE_BITLEN in CBL.
    eapply aevtM_cut_evt; [exact MOKq | eapply CBL with (A := md_p dY) (n := md_n dY) (xs := md_limbs dY);
      [exact (u32arr_ro _ _ _ _ ARRY) | unfold MPI_MAX_LIMBS in *; lia | lia | | lia | exact MIq | reflexivity | reflexivity] | ].
    { apply Z.mod_divide in ALY; [| lia]. destruct ALY as (q16 & Q16). apply Z.mod_divide; [lia |]. exists (4 * q16). lia. }
    intros ms' PO. unfold mpi_core_bitlen_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & -> & _ & _ & _ & ->).
    replace (ret_pc (Z_to_bv 64 135000)) with (Z_to_bv 64 135000) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep.
    pose proof (core_bitlen_range (md_limbs dY) (md_n dY) ltac:(lia)) as BLR.
    set (bl := core_bitlen (md_limbs dY) (md_n dY)) in *.
    rewrite (Z.mod_small bl) by (unfold MPI_MAX_LIMBS in *; lia). rewrite land_31 by lia.
    pose proof (Z.mod_pos_bound bl 32 ltac:(lia)) as BLM.
    destruct (Z.eq_dec (bl mod 32) 31) as [B31 | B31].
    - rewrite B31. zstep.
      match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
      zstep.
      eapply (L_m3 0 zp); [exact STq | exact LOCS | exact OWX | exact OWY | exact OWZ | exact PZ | exact OWT | exact NT2
        | exact NYX | lia | lia | lia | lia | exact BPOS].
    - zstep. rewrite (bv_eqb_neq (Z_to_bv 64 (bl mod 32)) (Z_to_bv 64 31)).
      2: { intros EQ. apply (f_equal bv_unsigned) in EQ. rewrite !unsigned_lit in EQ by lia. exact (B31 EQ). }
      cbn [negb].
      zstep. rewrite lxor_ones5 by lia.
      remember (31 - bl mod 32) as kk eqn:EK.
      assert (KR : 0 <= kk <= 31) by lia.
      do 3 zstep.
      pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dX STq eq_refl) as (MAX & NSX & WRX & PLX & CRX & CRLX & HFX & LAX1 & LAX2 & LAX3).
      pose proof HSHL as SHL. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SHL.
      eapply aevtM_cut; [eapply SHL with (dX := dX) (count := kk) (lo := lo) (LB := LBq) (h := hq) (m := mq) (mo := moq);
        rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity | ].
      all: try (rewrite AX; reflexivity).
      1: lia.
      1: lia.
      1: rewrite TOPq; lia.
      1: lia.
      intros ms1 mo1' PO1.
      binop_post PO1 m2 mo2 h2 LB2 dX2 r2 E2 MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
      replace (ret_pc (Z_to_bv 64 135552)) with (Z_to_bv 64 135552) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RR2 as (RES2 & KEEP2). pose proof KEEP2 as (KA2 & KP2 & KB2 & KN2).
      pose proof (mc_binop_l mq moq hq LBq [dX; dY; dZ; dT] dR [] _ [] 0%nat dX m2 mo2 h2 LB2 dX2 STq eq_refl HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2 KB2) as CS2.
      cbn [set_nth] in CS2.
      assert (LOC2 : locals_at [dX2; dY; dZ; dT]).
      { unfold locals_at in *. cbn in *. rewrite KA2. exact LOCS. }
      pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (HP2 & TOP2 & _ & SOK2' & MI2' & STK2 & _ & MOK2).
      destruct RES2 as [(R20 & VAL2 & SG2 & N2) | RERR2].
      2: { subst r2. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
           match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
           eapply L_err with (r := -16); [exact CS2 | exact LOC2 | reflexivity | reflexivity | lia | exact BPOS]. }
      subst r2.
      zstep. match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
      do 3 zstep.
      pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 1%nat dY CS2 eq_refl) as (MAY2 & NSY2 & WRY2 & PLY2 & _ & _ & _ & _ & _ & _).
      eapply aevtM_cut; [eapply SHL with (dX := dY) (count := kk) (lo := lo) (LB := LB2) (h := h2) (m := m2) (mo := mo2);
        rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity | ].
      all: try (rewrite AY; reflexivity).
      1: lia.
      1: lia.
      1: rewrite TOP2; lia.
      1: lia.
      intros ms3 mo3' PO3.
      binop_post PO3 m3 mo3 h3 LB3 dY3 r3 E3 MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR3.
      replace (ret_pc (Z_to_bv 64 135568)) with (Z_to_bv 64 135568) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RR3 as (RES3 & KEEP3). pose proof KEEP3 as (KA3 & KP3 & KB3 & KN3).
      pose proof (mc_binop_l m2 mo2 h2 LB2 [dX2; dY; dZ; dT] dR [] _ [] 1%nat dY m3 mo3 h3 LB3 dY3 CS2 eq_refl HH3 HT3 MF3 MA3 OUT3 PX3 SOK3 MI3 ST3 KB3) as CS3.
      cbn [set_nth] in CS3.
      assert (LOC3 : locals_at [dX2; dY3; dZ; dT]).
      { unfold locals_at in *. cbn in *. rewrite KA3. exact LOC2. }
      pose proof (cs_parts _ _ _ _ _ _ _ CS3) as (_ & _ & _ & _ & _ & _ & _ & MOK3).
      destruct RES3 as [(R30 & VAL3 & SG3 & N3) | RERR3].
      2: { subst r3. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
           match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
           eapply L_err with (r := -16); [exact CS3 | exact LOC3 | reflexivity | reflexivity | lia | exact BPOS]. }
      subst r3.
      zstep. match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
      zstep.
      destruct (HFX OWX) as (XP0 & _ & _ & NX1 & _).
      assert (OWX2 : md_own dX2 = LHeap).
      { apply (out_heap m2 LB2 dX2 MA2); [exact (proj1 (proj2 OUT2)) | lia]. }
      assert (OWY3 : md_own dY3 = LHeap).
      { apply (out_heap m3 LB3 dY3 MA3); [exact (proj1 (proj2 OUT3)) | lia]. }
      assert (BLE : core_bitlen (md_limbs dY) (md_n dY) <= core_bitlen (md_limbs dX) (md_n dX)).
      { apply core_bitlen_mono_val; [lia | lia |].
        rewrite <- (val_lval mq LBq dY MAY SG1Y), <- (val_lval mq LBq dX MAX SG1X). lia. }
      assert (NMONO : md_n dY3 <= md_n dX2).
      { rewrite N2, N3. apply shift_l_n_mono; [lia | lia | exact BLE]. }
      assert (NSUCC : md_n dX2 + 1 <= md_n dZ).
      { rewrite N2. pose proof (shift_l_n_le_succ kk dX KR ltac:(lia)) as SUCC. lia. }
      assert (PW : 0 < 2 ^ kk) by (apply Z.pow_pos_nonneg; lia).
      eapply (L_m3 kk zp); [exact CS3 | exact LOC3 | exact OWX2 | exact OWY3 | exact OWZ | exact PZ | exact OWT | exact NT2
        | exact NMONO | exact NSUCC | | | lia | exact BPOS].
      + rewrite VAL2. apply Z.mul_nonneg_nonneg; lia.
      + rewrite VAL3. apply Z.mul_pos_pos; lia.
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
    intros mq moq hq LBq dX dY dZ dT j0 w8 w16 w24 w32 w40 w48 w56 j64 u0 u1 u2 j68 t160 t164 t168 t176 t180
      xra x4 x5 x6 x7 x8 x9 x10 x11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      STq LOCS OWX OWY OWZ OWT NYX NXA AXA AYB ABR.
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (HPq & TOPq & FRMq & SOKq & MIq & STKq & _ & MOKq).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    assert (ADDR4 : md_addr dX = SP + -144 /\ md_addr dY = SP + -160 /\ md_addr dZ = SP + -176 /\ md_addr dT = SP + -192).
    { unfold locals_at in LOCS. cbn in LOCS. injection LOCS as E1 E2 E3 E4. tauto. }
    destruct ADDR4 as (AX & AY & AZ & AT).
    pose proof (struct_cells _ _ _ _ _ _ _ 0%nat dX STq eq_refl) as (CX & SGX & NXr & _ & HPX).
    pose proof (struct_cells _ _ _ _ _ _ _ 1%nat dY STq eq_refl) as (CY & SGY & NYr & _ & HPY).
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ STq) as (Fcs0 & Ftpc & Ft2 & Ftc & REGq).
    rewrite AX in CX. rewrite AY in CY. unfold mpi_cells in CX, CY.
    unfold t2cells in Ft2.
    pose proof (munch_refl [(SP + -160, SP + -128)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    zstep. zstep. zstep.
    assert (CS1 : CST m1 moq hq LBq [set_sg dX 1; set_sg dY 1; dZ; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_hi_write mq moq hq LBq [dX; dY; dZ; dT] dR [] _ [] (SP + -160) (SP + -128) [] m1
               [set_sg dX 1; set_sg dY 1; dZ; dT] _ STq MU WM); [eassumption | eassumption | lia | lia | constructor | reflexivity | | | ].
      - intros j d d' Ej Ej'.
        destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
        + injection Ej as <-. injection Ej' as <-.
          right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. rewrite AX. exact CX.
        + injection Ej as <-. injection Ej' as <-.
          right. exists 1. split; [reflexivity|]. split; [left; reflexivity|]. rewrite AY. exact CY.
        + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
        + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
        + destruct j; discriminate.
      - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd]; assumption.
      - apply frame_chs; [| reflexivity | reflexivity | reflexivity].
        unfold locals_at in *. cbn in *. exact LOCS. }
    assert (LOC1 : locals_at [set_sg dX 1; set_sg dY 1; dZ; dT]) by (unfold locals_at in *; cbn in *; exact LOCS).
    pose proof (a_cells _ _ _ _ _ _ CS1) as (CA1 & SGA).
    pose proof (rw_cells_bound _ _ _ _ CA1) as BA. cbn in BA.
    pose proof (opnd_facts _ _ _ _ _ _ dA CS1 opndA) as (MAA & _ & _ & _ & _ & _).
    pose proof MAA as ((_ & ALA & PA & LENA & NAr & _) & _).
    unfold mpi_cells in CA1.
    zstep.
    rewrite (bv_eqb_neq (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 0)).
    2: { intros EQ. apply (f_equal bv_unsigned) in EQ. rewrite !unsigned_lit in EQ by lia. lia. }
    cbv beta iota.
    zstep. zstep.
    assert (L7 : Z.land (md_addr dA) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact ALA).
    rewrite L7.
    match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
    zstep. rewrite zx16_small by (unfold MPI_MAX_LIMBS in *; lia).
    zstep. zstep. zstep. zstep.
    unfold bv_ltu. rewrite !unsigned_lit by (unfold MPI_MAX_LIMBS in *; lia).
    destruct (Z.ltb_spec 9998 (md_n dA)) as [BIG | SMALL]; cbv beta iota.
    { eapply L_c0 with (r := -16); [exact CS1 | exact LOC1 | reflexivity | reflexivity | lia | lia]. }
    do 4 zstep.
    pose proof (cs_parts _ _ _ _ _ _ _ CS1) as (HP1 & TOP1 & FRM1 & SOK1 & MI1 & STK1 & _ & MOK1).
    eapply aevtM_cut.
    { pose proof (heap_calloc usegs L HI) as HC. rewrite HCALLOC in HC. unfold U_CALLOC in HC.
      eapply HC with (cnt := md_n dA + 2) (sz := 4) (lo := lo) (h := hq) (LB := LBq) (m := m1) (mo := moq);
        rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity.
      all: rewrite ?TOP1; lia. }
    intros ms2 mo2' PO2. unfold call_post in PO2.
    destruct PO2 as (z0 & z1 & z2 & ret2 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m2 & mo2 & E2 & MI2 & ST2 & MF2 & HPR2 & h2 & HT2 & RES2).
    injection E2 as E2a E2b. subst ms2 mo2'.
    replace (ret_pc (Z_to_bv 64 134920)) with (Z_to_bv 64 134920) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ?(unsigned_lit (SP + -288)) in ST2, HPR2 by lia.
    destruct RES2 as [(RV0 & HP2) | (A & RVA & BRA & HP2 & ZB2)].
    { subst ret2. pose proof (heap_mok _ _ _ _ _ _ _ HP2) as MOK2.
      zstep.
      match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
      assert (CS2 : CST m2 mo2 h2 LBq [set_sg dX 1; set_sg dY 1; dZ; dT] dR []
        (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64]
           [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
      { exact (mc_heap_nop m1 moq hq LBq _ dR [] _ [] 0%nat (set_sg dX 1) m2 mo2 h2 CS1 eq_refl HP2 HT2 MF2 HPR2 MI2 ST2). }
      eapply L_c0 with (r := -16); [exact CS2 | exact LOC1 | reflexivity | reflexivity | lia | lia]. }
    subst ret2. pose proof (heap_mok _ _ _ _ _ _ _ HP2) as MOK2.
    replace ((md_n dA + 2) * 4) with (4 * (md_n dA + 2)) in BRA, HP2, ZB2 by lia.
    pose proof BRA as (AP0 & A16 & _ & AHI & _).
    pose proof (@alloc_ceiling_hi L) as ACH.
    zstep.
    rewrite (bv_eqb_neq (Z_to_bv 64 A) (Z_to_bv 64 0)).
    2: { intros EQ. apply (f_equal bv_unsigned) in EQ. rewrite !unsigned_lit in EQ by lia. lia. }
    cbv beta iota.
    pose proof (struct_cells _ _ _ _ _ _ _ 2%nat dZ CS1 eq_refl) as (CZ1 & SGZ & NZr & NULZ & _).
    destruct (NULZ OWZ) as (PZ0 & NZ0).
    assert (CZ2 : rw_cells usegs m2 (SP + -176) (mpi_cells (md_p dZ) (Z_to_bv 64 (md_sg dZ)) (md_n dZ) (md_pad dZ))).
    { apply (heap_pres_rw_cells _ _ _ _ _ _ _ _ HPR2); [rewrite <- AZ; exact CZ1 |].
      intros a Ra. left. cbn in Ra. lia. }
    unfold mpi_cells in CZ2. rewrite PZ0, NZ0 in CZ2.
    assert (NRANGE : 1 <= md_n dA + 2 <= MPI_MAX_LIMBS) by (unfold MPI_MAX_LIMBS in *; lia).
    pose proof (fun m3x => mc_calloc_attach m1 moq hq LBq _ dR [] _ [] 2%nat dZ m2 mo2 h2 A (md_n dA + 2) m3x (md_sg dZ) (md_pad dZ)
                  CS1 eq_refl OWZ HP2 HT2 MF2 HPR2 MI2 ST2 BRA ZB2 NRANGE) as ATT.
    pose proof (munch_refl [(SP + -176, SP + -160)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    zstep. zstep. zstep.
    assert (MU2' : munch [(md_addr dZ, md_addr dZ + 16)] m2 m3) by (rewrite AZ; replace (SP + -176 + 16) with (SP + -160) by lia; exact MU2).
    assert (CZ3 : rw_cells usegs m3 (md_addr dZ) (mpi_cells A (Z_to_bv 64 (md_sg dZ)) (md_n dA + 2) (md_pad dZ))) by (rewrite AZ; exact CZ2).
    pose proof (ATT m3 MU2' WM2 MI2 CZ3 SGZ) as CS3. cbn [set_nth] in CS3. clear ATT.
    do 3 zstep.
    assert (E2 : Z_to_bv 64 ((md_n dA + 2) ≪ 2) = Z_to_bv 64 (4 * (md_n dA + 2))) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite E2. clear E2.
    pose proof U_memset_spec as MS0. unfold memset_stmt in MS0.
    eapply aevtM_cut_evt; [exact MOK2 | eapply MS0; [rewrite !unsigned_lit by lia; exact ZB2 | exact MI2] | ].
    intros ms4 PO4. unfold memset_post in PO4.
    destruct PO4 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m4 & -> & MU4 & WM4 & MI4 & ZB4).
    rewrite !unsigned_lit in MU4, ZB4 by lia. rewrite Zmod_0_l in ZB4.
    replace (ret_pc (Z_to_bv 64 134948)) with (Z_to_bv 64 134948) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep.
    assert (L3 : Z.land A 3 = 0).
    { change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
      apply Z.mod_divide in A16; [| lia]. destruct A16 as (q16 & Q16). apply Z.mod_divide; [lia |]. exists (4 * q16). lia. }
    zstep. rewrite L3.
    match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
    assert (NN : Z.to_nat (md_n dA + 2) = S (S (Z.to_nat (md_n dA)))) by lia.
    assert (ZC4 : rw_cells usegs m4 A (map C4 (repeat (Z_to_bv 64 0) (Z.to_nat (md_n dA + 2))))).
    { apply (rw_cells_zeros _ _ _ _ _ ZB4).
      - generalize (Z.to_nat (md_n dA + 2)). intros k. induction k as [|k IHk]; cbn; [exact I | split; [reflexivity | exact IHk]].
      - assert (SZK : forall k, cells_size (map C4 (repeat (Z_to_bv 64 0) k)) = (4 * k)%nat).
        { intros k. induction k as [|k IHk]; cbn; [reflexivity | rewrite IHk; lia]. }
        rewrite SZK. lia. }
    clear ZB4. rewrite NN in ZC4. cbn [repeat map] in ZC4.
    pose proof (munch_refl [(A, A + 4 * (md_n dA + 2))] m4) as MU5. pose proof (wmono_refl usegs m4) as WM5.
    zstep. rename m0 into m5.
    assert (ZU5 : u32arr usegs m5 A (repeat (Z_to_bv 64 0) (Z.to_nat (md_n dA + 2)))).
    { rewrite NN. apply LxPMpiTac.u32arr_of_rw_cells. exact ZC4. }
    assert (STK5 : stk usegs m5 lo SPc).
    { apply (stk_transport_disjoint _ _ _ _ _ _ ST2 MU4 WM4). cbn. split; [| exact I]. lia. }
    match type of CS3 with CST _ ?mo ?h ?lb ?ls ?dw ?ex ?cs ?cx => assert (CS5 : CST m5 mo h lb ls dw ex cs cx) end.
    { eapply mc_munch with (li := Some 2%nat) (wl := false) (ex := false); [exact CS3 | exact MU4 | exact WM4 | exact MI4 | exact STK5 | | reflexivity | | | |].
      - constructor; [| constructor]. right. left. exists 2%nat. eexists. split; [reflexivity|]. split; [reflexivity|].
        cbn. split; [reflexivity|]. lia.
      - intros j d d' Ej Ej'. rewrite Ej in Ej'. injection Ej' as <-.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [intros _; reflexivity|].
        intros Ej2 _. injection Ej2 as <-. cbn in Ej. injection Ej as <-. cbn [md_p md_limbs md_n].
        split; [exact ZU5 | rewrite repeat_length; lia].
      - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [intros _; reflexivity|]. intros FL; discriminate FL.
      - intros _; reflexivity.
      - intros FL; discriminate FL. }
    match type of CS5 with CST _ _ _ _ [_; _; ?z; _] _ _ _ _ => set (dZ5 := z) in CS5 end.
    pose proof (a_cells _ _ _ _ _ _ CS5) as (CA5 & _). unfold mpi_cells in CA5.
    zstep. rewrite zx16_small by (unfold MPI_MAX_LIMBS in *; lia).
    zstep.
    pose proof (struct_cells _ _ _ _ _ _ _ 2%nat dZ5 CS5 eq_refl) as (CZ5 & _ & _ & _ & _).
    assert (AZ5 : md_addr dZ5 = SP + -176) by (cbn; exact AZ).
    rewrite AZ5 in CZ5. unfold mpi_cells in CZ5.
    clear MU4 MU5 WM4 WM5 MU2 MU2' WM2 MU WM CA5 ZC4.
    pose proof (munch_refl [(SP + -176, SP + -160)] m5) as MU6. pose proof (wmono_refl usegs m5) as WM6.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ CS5) as (Fcs5 & Ftpc5 & Ft25 & Ftc5 & REG5).
    unfold t2cells in Ft25.
    pose proof (cs_parts _ _ _ _ _ _ _ CS5) as (_ & _ & _ & _ & MI5 & ST5 & _ & _).
    zstep. rename m0 into m6.
    assert (CS6 : CST m6 mo2 h2 ((A, 4 * (md_n dA + 2)) :: LBq) [set_sg dX 1; set_sg dY 1; set_sg dZ5 1; dT] dR []
      (frame [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 j64]
         [C4 u0; C4 u1; C4 u2] j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_hi_write m5 mo2 h2 _ [set_sg dX 1; set_sg dY 1; dZ5; dT] dR [] _ [] (SP + -176) (SP + -160) [] m6
               [set_sg dX 1; set_sg dY 1; set_sg dZ5 1; dT] _ CS5 MU6 WM6); [exact MI5 | exact ST5 | lia | lia | constructor | reflexivity | | | ].
      - intros j d d' Ej Ej'.
        destruct j as [|[|[|[|j]]]]; cbn in Ej, Ej'.
        + injection Ej as <-. injection Ej' as <-. left. split; [cbn; lia | reflexivity].
        + injection Ej as <-. injection Ej' as <-. left. split; [cbn; lia | reflexivity].
        + injection Ej as <-. injection Ej' as <-. right. exists 1. split; [reflexivity|]. split; [left; reflexivity|].
          rewrite AZ5. exact CZ5.
        + injection Ej as <-. injection Ej' as <-. left. split; [lia | reflexivity].
        + destruct j; discriminate.
      - unfold frame. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; cbn [fst snd]; assumption.
      - apply frame_chs; [| reflexivity | reflexivity | reflexivity]. unfold locals_at in *. cbn in *. exact LOCS. }
    do 3 zstep.
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 3%nat dT CS6 eq_refl) as (MAT & NST & WRT & PLT & _).
    pose proof (cs_parts _ _ _ _ _ _ _ CS6) as (HP6 & TOP6 & _ & SOK6 & MI6 & ST6 & _ & MOK6).
    pose proof HGROW as GRW. unfold mpi_grow_stmt, U_MPI_GROW in GRW.
    eapply aevtM_cut; [eapply GRW with (dX := dT) (nb := md_n dA + 2) (lo := lo) (LB := (A, 4 * (md_n dA + 2)) :: LBq) (h := h2) (m := m6) (mo := mo2);
      rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity | ].
    all: try (rewrite AT; reflexivity).
    1: lia.
    1: lia.
    1: rewrite TOP6; lia.
    1: lia.
    intros ms7 mo7' PO7.
    binop_post PO7 m7 mo7 h7 LB7 dT7 r7 E7 MI7 ST7 MF7 HT7 HH7 MA7 OUT7 PX7 SOK7 RR7.
    replace (ret_pc (Z_to_bv 64 134984)) with (Z_to_bv 64 134984) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RR7 as (RES7 & KB7).
    pose proof (mc_binop_l m6 mo2 h2 _ [set_sg dX 1; set_sg dY 1; set_sg dZ5 1; dT] dR [] _ [] 3%nat dT m7 mo7 h7 LB7 dT7
                  CS6 eq_refl HH7 HT7 MF7 MA7 OUT7 PX7 SOK7 MI7 ST7 KB7) as CS7.
    cbn [set_nth] in CS7.
    assert (LOC7 : locals_at [set_sg dX 1; set_sg dY 1; set_sg dZ5 1; dT7]).
    { unfold locals_at in *. cbn in *. rewrite (proj1 OUT7). exact LOCS. }
    pose proof (cs_parts _ _ _ _ _ _ _ CS7) as (_ & _ & _ & _ & _ & _ & _ & MOK7).
    destruct RES7 as [(R70 & SG7 & N7 & _ & _ & _) | (R7E & ET7)].
    2: { subst r7. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
         match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
         eapply L_err with (r := -16); [exact CS7 | exact LOC7 | reflexivity | reflexivity | lia | lia]. }
    subst r7. zstep.
    match goal with |- context [if ?c then _ else _] => let v := eval vm_compute in c in change c with v; cbv beta iota end.
    pose proof (struct_cells _ _ _ _ _ _ _ 3%nat dT CS1 eq_refl) as (_ & _ & _ & NULT & _).
    destruct (NULT OWT) as (_ & NT0).
    assert (OWT7 : md_own dT7 = LHeap).
    { apply (out_heap m7 LB7 dT7 MA7); [exact (proj1 (proj2 OUT7)) | lia]. }
    eapply (L_m2 A); [exact CS7 | exact LOC7 | exact OWX | exact OWY | reflexivity | reflexivity | exact OWT7 | lia
      | exact NYX | cbn; lia | reflexivity | reflexivity | | lia].
    unfold mpd_val, mpd_abs in *. cbn [set_sg md_sg md_limbs]. lia.
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
    intros mq moq hq LBq ls dW cs0 tpc j68 t160 t164 t168 t176 t180 r xra x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 STq ALLNUL LOCS SZcs SZtp RRANGE BPOS.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ STq) as (Fcs0 & Ftpc & Ft2 & Ftc & REGq).
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    assert (FRlo : 0 <= SP + -288) by lia.
    pose proof (cs_parts _ _ _ _ _ _ _ STq) as (HPq & TOPq & FRMq & SOKq & MIq & STKq & _ & MOKq).
    pose proof (mc_final _ _ _ _ _ _ _ _ STq ALLNUL) as (_ & _ & _ & MWq & OUTq & KEEPq & PXq & _).
    assert (STKfull : stk usegs mq lo SP).
    { destruct STq as (_ & _ & _ & LOKq & _).
      unfold locals_at in LOCS.
      destruct ls as [|dX [|dY [|dZ [|dT [|dE rest]]]]]; try discriminate LOCS.
      cbn in LOCS. injection LOCS as AX AY AZ AT.
      pose proof (Forall_inv LOKq) as LX. pose proof (Forall_inv_tail LOKq) as LOK1.
      pose proof (Forall_inv LOK1) as LY. pose proof (Forall_inv_tail LOK1) as LOK2.
      pose proof (Forall_inv LOK2) as LZ. pose proof (Forall_inv (Forall_inv_tail LOK2)) as LT.
      destruct LX as (((CX & _) & _) & _). destruct LY as (((CY & _) & _) & _).
      destruct LZ as (((CZ & _) & _) & _). destruct LT as (((CT & _) & _) & _).
      rewrite AX in CX. rewrite AY in CY. rewrite AZ in CZ. rewrite AT in CT.
      apply (stk_release _ _ _ _ _ STKq) in Fcs0; [| lia]. rewrite SZcs in Fcs0.
      replace (SP + -288 + Z.of_nat 68) with (SP + -220) in Fcs0 by lia.
      apply (stk_release _ _ _ _ _ Fcs0) in Ftpc; [| lia]. rewrite SZtp in Ftpc.
      replace (SP + -220 + Z.of_nat 12) with (SP + -208) in Ftpc by lia.
      apply (stk_release _ _ _ _ _ Ftpc) in Ft2; [| lia]. cbn [cells_size csize t2cells Nat.add] in Ft2.
      replace (SP + -208 + Z.of_nat 16) with (SP + -192) in Ft2 by lia.
      apply (stk_release _ _ _ _ _ Ft2) in CT; [| lia]. cbn [cells_size csize mpi_cells Nat.add] in CT.
      replace (SP + -192 + Z.of_nat 16) with (SP + -176) in CT by lia.
      apply (stk_release _ _ _ _ _ CT) in CZ; [| lia]. cbn [cells_size csize mpi_cells Nat.add] in CZ.
      replace (SP + -176 + Z.of_nat 16) with (SP + -160) in CZ by lia.
      apply (stk_release _ _ _ _ _ CZ) in CY; [| lia]. cbn [cells_size csize mpi_cells Nat.add] in CY.
      replace (SP + -160 + Z.of_nat 16) with (SP + -144) in CY by lia.
      apply (stk_release _ _ _ _ _ CY) in CX; [| lia]. cbn [cells_size csize mpi_cells Nat.add] in CX.
      replace (SP + -144 + Z.of_nat 16) with (SP + -128) in CX by lia.
      apply (stk_release _ _ _ _ _ CX) in Ftc; [| lia]. cbn [cells_size csize tcells Nat.add] in Ftc.
      replace (SP + -128 + Z.of_nat 24) with (SP + -104) in Ftc by lia.
      apply (stk_release _ _ _ _ _ Ftc) in REGq; [| lia]. cbn [cells_size csize Nat.add] in REGq.
      replace (SP + -104 + Z.of_nat 104) with SP in REGq by lia. exact REGq. }
    do 15 zstep.
    apply aevtM_done. unfold mpi_binop_post.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, mq, moq, hq, LBq, dW, r.
    split; [reflexivity|]. split; [exact MIq|]. split; [exact STKfull|]. split; [exact FRMq|].
    split; [exact TOPq|]. split; [exact HPq|]. split; [exact MWq|]. split; [exact OUTq|].
    split; [exact PXq|]. split; [exact SOKq|].
    split; [split; [exact RRANGE| intros _; exact BPOS]| exact KEEPq].
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
    intros mq moq hq LBq dX dY dZ dT cs0 tpc j68 t160 t164 t168 t176 t180 xra x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
      t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CSin LOCS NULLS SIZE0 SIZE1 BNZ.
    pose proof (bv_unsigned_in_range 64 sp) as SPbnd. change (bv_modulus 64) with (2^64) in SPbnd.
    pose proof alloc_ceiling_pos as CEILpos.
    pose proof (cs_parts _ _ _ _ _ _ _ CSin) as (HEAPq & TOPeq & MOFR & STATq & MINVq & STKq & _ & MOKq).
    destruct facts0 as (RADDRpos & RADDRal & RADDRside & _ & _ & _ & SPtop & _).
    destruct (w_cells _ _ _ _ _ _ _ CSin) as (RCELLS & RSIGN).
    pose proof (rw_cells_bound _ _ _ _ RCELLS) as RBND. cbn [cells_size csize mpi_cells Nat.add] in RBND.
    zstep.
    rewrite (bv_eqb_neq (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 0)) by
      (intros E0; apply (f_equal bv_unsigned) in E0; rewrite !unsigned_lit in E0 by lia; lia).
    do 3 zstep.
    destruct (mc_w_facts _ _ _ _ _ _ _ _ _ CSin) as (MATR & _ & _ & WRq & _).
    destruct (opnd_facts _ _ _ _ _ _ dA CSin opndA) as (MATA & CRAq & CRALq & _).
    destruct (opnd_sep_w _ _ _ _ _ _ dA CSin opndA) as (_ & OSRA).
    assert (CPSEP : copy_sep dR dA lo SPc).
    { apply copy_sep_of_opnd; [exact OSRA|]. destruct MATA as ((_ & _ & APOS & _) & _). lia. }
    pose proof HCOPY as COPYSPEC. unfold mpi_copy_stmt_x, U_MPI_COPY in COPYSPEC.
    eapply aevtM_cut; [eapply COPYSPEC with (dX := dR) (dY := dA) (lo := lo) (LB := LBq) (h := hq);
      rewrite ?(unsigned_lit (SP + -288)) by lia; try eassumption; try reflexivity; try lia | ].
    intros ms' mo' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & mo2 & h2 & LB2 & dR2 & rc &
                    CFG & MINV2 & STK2 & MOFR2 & TOP2 & HEAP2 & MAT2 & OUT2 & PRES2 & STAT2 & RES2).
    injection CFG as -> ->.
    rewrite (unsigned_lit (SP + -288)) in STK2, PRES2 by lia.
    destruct RES2 as ((OUTCOME & ADDR2 & PAD2 & BLK2) & _).
    assert (CS2 : CST m2 mo2 h2 LB2 [dX; dY; dZ; dT] dR2 [] (frame cs0 tpc j68 (tcells t160 t164 t168 t176 t180)) []).
    { apply (mc_binop_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ CSin HEAP2 TOP2 MOFR2 MAT2 OUT2 PRES2 STAT2 MINV2 STK2 BLK2 PAD2).
      destruct OUTCOME as [(_ & _ & NGROW & _) | (_ & NSAME & _)]; lia. }
    replace (ret_pc (Z_to_bv 64 135316)) with (Z_to_bv 64 135316) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (_ & _ & _ & _ & _ & _ & _ & MOK2).
    destruct OUTCOME as [(-> & _) | (-> & _)].
    - zstep. rewrite bv_eqb_refl.
      eapply L_ret0; [exact CS2 | exact NULLS | exact LOCS | exact SIZE0 | exact SIZE1 | lia | exact BNZ].
    - unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
      replace (bv_eqb (Z_to_bv 64 (-16)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
      eapply L_err; [exact CS2 | exact LOCS | exact SIZE0 | exact SIZE1 | lia | exact BNZ].
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
    intros mq j0 j148 t160 t164 t180 xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CS0 MU0 WM0.
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    pose proof (cs_parts _ _ _ _ _ _ _ CS0) as (_ & _ & _ & _ & MIq & STq & CELLS & MOKq).
    pose proof (Forall_inv CELLS) as FA. pose proof (Forall_inv (Forall_inv_tail CELLS)) as FT.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CELLS))) as FG. clear CELLS.
    cbn [fst snd] in FA, FT, FG.
    assert (SGB : Z.sgn (mpd_val dB) = 0 \/ Z.sgn (mpd_val dB) = 1 \/ Z.sgn (mpd_val dB) = -1)
      by (destruct (mpd_val dB); cbn; auto).
    destruct SGB as [SG0 | SGnz].
    - (* B = 0: return MBEDTLS_ERR_MPI_DIVISION_BY_ZERO through the epilogue *)
      rewrite SG0.
      pose proof (mc_final _ _ _ _ _ _ _ _ CS0 (Forall_nil _)) as (HPq & TOPq & FRMq & MWq & OUTq & KEEPq & PXq & SOKq & _).
      assert (STfull : stk usegs mq lo SP).
      { apply (stk_release _ _ _ _ _ STq) in FA; [| lia]. cbn [cells_size csize Nat.add] in FA.
        replace (SP + -288 + Z.of_nat 160) with (SP + -128) in FA by lia.
        apply (stk_release _ _ _ _ _ FA) in FT; [| lia]. cbn [cells_size csize tcells Nat.add] in FT.
        replace (SP + -128 + Z.of_nat 24) with (SP + -104) in FT by lia.
        apply (stk_release _ _ _ _ _ FT) in FG; [| lia]. cbn [cells_size csize Nat.add] in FG.
        replace (SP + -104 + Z.of_nat 104) with SP in FG by lia. exact FG. }
      zstep. if_true. do 17 zstep.
      apply aevtM_done. unfold mpi_binop_post.
      exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, mq, mo, h, LB, dR, (-12).
      split; [reflexivity|]. split; [exact MIq|]. split; [exact STfull|]. split; [exact FRMq|].
      split; [exact TOPq|]. split; [exact HPq|]. split; [exact MWq|]. split; [exact OUTq|].
      split; [exact PXq|]. split; [exact SOKq|].
      split; [split; [lia| intros E12; discriminate E12]| exact KEEPq].
    - assert (BPOS : 0 < mpd_abs dB).
      { rewrite <- (mpd_val_abs dB (proj2 MB0)).
        destruct SGnz as [S1|S1]; destruct (mpd_val dB); cbn in S1 |- *; lia. }
      assert (CONT : forall v : word,
        aevtM usegs mo POST (MS (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA))
          v a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dB)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20e64) fc None mq (seg_rom usegs))).
      2: { destruct SGnz as [S1|S1]; rewrite S1; zstep; if_false; apply CONT. }
      intros v. clear SGnz.
      (* one byte region over the four struct slots and T2, so that the init stores can split it *)
      apply (rw_cells_merge usegs mq SPc [] [CB 144 j0; C4 (Z_to_bv 64 0); CB 12 j148] []) in FA.
      cbn [app cells_size csize Nat.add] in FA.
      set (jall := cells_bytes [CB 144 j0; C4 (Z_to_bv 64 0); CB 12 j148]) in FA. clearbody jall.
      do 16 zstep.
      lazymatch goal with Mx : mem_inv usegs ?mm |- aevtM _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      (* cut the stored region into cs0, TP2, T2 and the four local structs *)
      take FA 1%nat FLO. take FA 3%nat FT2. take FA 3%nat FTT. take FA 3%nat FZZ. take FA 3%nat FYY.
      apply (rw_cells_split_CB usegs m1 SPc [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 4; 4; 4; 4]%nat) in FLO; [| reflexivity].
      cbn [app mk_CB_cells] in FLO.
      take FLO 9%nat FC0.
      do 7 (lazymatch type of FC0 with rw_cells ?sg ?mm ?A (?c0 :: ?rest) =>
        let rec upto cs := lazymatch cs with CB 8%nat _ :: _ => constr:(@nil cell) | ?c :: ?r => let p := upto r in constr:(c :: p) end in
        let p := upto rest in apply (rw_cells_CB8_C8' sg mm A (c0 :: p)) in FC0; cbn [app] in FC0 end).
      do 3 (lazymatch type of FLO with rw_cells ?sg ?mm ?A ?cs =>
        let rec upto cs := lazymatch cs with CB 4%nat _ :: _ => constr:(@nil cell) | ?c :: ?r => let p := upto r in constr:(c :: p) end in
        let p := upto cs in apply (rw_cells_CB4_C4 sg mm A p) in FLO; cbn [app] in FLO end).
      apply (rw_cells_split_C4 usegs m1 (SP + -208) [C8 _]) in FT2. cbn [app] in FT2.
      apply (rw_cells_C2_congr usegs m1 (SP + -208) [C8 _] 196609 1) in FT2; [| reflexivity].
      apply (rw_cells_C2_congr usegs m1 (SP + -208) [C8 _; C2 _] _ 3) in FT2; [| vm_compute; reflexivity].
      apply (rw_cells_CB4_C4 usegs m1 (SP + -208) [C8 _; C2 _; C2 _]) in FT2. cbn [app] in FT2.
      let fresh_struct HS :=
        lazymatch type of HS with rw_cells ?sg ?mm ?A _ =>
          apply (rw_cells_split_C4 sg mm A [C8 _]) in HS; cbn [app] in HS;
          apply (rw_cells_C2_congr sg mm A [C8 _; C2 _] _ 0) in HS; [| vm_compute; reflexivity];
          apply (rw_cells_CB4_C4 sg mm A [C8 _; C2 _; C2 _]) in HS; cbn [app] in HS end in
      fresh_struct FTT; fresh_struct FZZ; fresh_struct FYY; fresh_struct FA.
      (* name the junk words *)
      lazymatch type of FC0 with rw_cells _ _ _ [CB 8 ?b0; C8 ?b1; C8 ?b2; C8 ?b3; C8 ?b4; C8 ?b5; C8 ?b6; C8 ?b7; CB 4 ?b8] =>
        set (k0 := b0) in FC0; set (w8 := b1) in FC0; set (w16 := b2) in FC0; set (w24 := b3) in FC0; set (w32 := b4) in FC0;
        set (w40 := b5) in FC0; set (w48 := b6) in FC0; set (w56 := b7) in FC0; set (k64 := b8) in FC0 end.
      lazymatch type of FLO with rw_cells _ _ _ [C4 ?b0; C4 ?b1; C4 ?b2] =>
        set (u0 := b0) in FLO; set (u1 := b1) in FLO; set (u2 := b2) in FLO end.
      lazymatch type of FT2 with rw_cells _ _ _ [_; _; _; C4 ?b0] => set (j68 := b0) in FT2 end.
      lazymatch type of FA with rw_cells _ _ _ [_; _; _; C4 ?b0] => set (padX := b0) in FA end.
      lazymatch type of FYY with rw_cells _ _ _ [_; _; _; C4 ?b0] => set (padY := b0) in FYY end.
      lazymatch type of FZZ with rw_cells _ _ _ [_; _; _; C4 ?b0] => set (padZ := b0) in FZZ end.
      lazymatch type of FTT with rw_cells _ _ _ [_; _; _; C4 ?b0] => set (padT := b0) in FTT end.
      clearbody k0 w8 w16 w24 w32 w40 w48 w56 k64 u0 u1 u2 j68 padX padY padZ padT. clear jall.
      assert (LOCS : locals_at [mkMPD (SP + -144) 1 0 0 [] padX LNull; mkMPD (SP + -160) 1 0 0 [] padY LNull;
                                mkMPD (SP + -176) 1 0 0 [] padZ LNull; mkMPD (SP + -192) 1 0 0 [] padT LNull]) by reflexivity.
      assert (CS1 : CST m1 mo h LB
        [mkMPD (SP + -144) 1 0 0 [] padX LNull; mkMPD (SP + -160) 1 0 0 [] padY LNull;
         mkMPD (SP + -176) 1 0 0 [] padZ LNull; mkMPD (SP + -192) 1 0 0 [] padT LNull] dR []
        (frame [CB 8 k0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; CB 4 k64] [C4 u0; C4 u1; C4 u2] j68
           (tcells t160 t164 (Z_to_bv 64 (SP + -144)) (Z_to_bv 64 65537) t180)) []).
      { assert (ESm : Forall (fun e : mpd => mpd_at usegs m LB e) es)
          by (unfold es; destruct ALIAS; repeat apply Forall_cons; try apply Forall_nil; assumption).
        apply (mc_init m1 _ _ HH0 SOK0 MI0 MR0 ESm MU0 WM0 MIq STq).
        - repeat apply Forall_cons; try apply Forall_nil; cbn [md_addr md_pad md_own md_p md_n md_limbs md_sg];
            (split; [assumption| repeat split; try reflexivity; lia]).
        - intros i j di dj Ei Ej NE.
          destruct i as [|[|[|[|i]]]]; cbn in Ei; [..| destruct i; discriminate Ei]; injection Ei as <-;
          (destruct j as [|[|[|[|j]]]]; cbn in Ej; [..| destruct j; discriminate Ej]; injection Ej as <-);
          cbn [md_addr]; first [lia | exfalso; exact (NE eq_refl)].
        - unfold frame. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; assumption.
        - apply (frame_chs _ _ _ _ _ LOCS); reflexivity. }
      clear FT FG FT2 FTT FZZ FYY FA FC0 FLO CS0 MU0 WM0 MIq STq.
      (* cmp_abs(A, B) *)
      zstep.
      pose proof (opnd_facts _ _ _ _ _ _ dA CS1 opndA) as (MA1 & _ & _ & _ & PA1 & _).
      pose proof (opnd_facts _ _ _ _ _ _ dB CS1 (or_introl opndB)) as (MB1 & _ & _ & _ & PB1 & _).
      pose proof (cs_parts _ _ _ _ _ _ _ CS1) as (_ & _ & _ & _ & MI1 & _ & _ & _).
      pose proof HCABS as CABS. unfold mpi_cmp_abs_stmt, U_MPI_CMP_ABS in CABS.
      eapply aevtM_cut_evt; [exact MOKq | eapply CABS with (LB := LB) (dX := dA) (dY := dB) |].
      1: exact MA1.
      1: exact MB1.
      1: intros O; exact (proj1 (PA1 O)).
      1: intros O; exact (proj1 (PB1 O)).
      1: exact MI1.
      1: reflexivity.
      1: reflexivity.
      intros ms' PO. unfold mpi_cmp_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & _ & _ & _).
      replace (ret_pc (Z_to_bv 64 134824)) with (Z_to_bv 64 134824) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear MA1 MB1 PA1 PB1 MI1 CABS.
      remember (Z.sgn (mpd_abs dA - mpd_abs dB)) as sgv eqn:Esg.
      assert (SGV : sgv = -1 \/ (sgv = 0 \/ sgv = 1) /\ mpd_abs dB <= mpd_abs dA).
      { subst sgv. destruct (Z.ltb_spec (mpd_abs dA) (mpd_abs dB)) as [LT|GE].
        - left. apply Z.sgn_neg. lia.
        - right. split; [| exact GE]. destruct (Z.eq_dec (mpd_abs dA) (mpd_abs dB)) as [E|NE].
          + left. rewrite E, Z.sub_diag. reflexivity.
          + right. apply Z.sgn_pos. lia. }
      clear Esg. destruct SGV as [-> | [SGGE ABle]].
      { (* |A| < |B|: Q is NULL, so straight to the copy of A into R *)
        zstep. if_true. zstep. if_true.
        eapply L_early; [exact CS1| exact LOCS| repeat constructor| reflexivity| reflexivity| exact BPOS]. }
      assert (NLT : bv_lts (Z_to_bv 64 sgv) (Z_to_bv 64 0) = false) by (destruct SGGE as [-> | ->]; reflexivity).
      zstep. rewrite NLT. cbv_concl_iota. clear NLT SGGE.
      (* copy(X, A) *)
      do 3 zstep.
      pose proof (cs_parts _ _ _ _ _ _ _ CS1) as (HP1 & _ & _ & SOK1 & MI1 & ST1 & _ & _).
      pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat _ CS1 eq_refl) as (MX1 & NSX1 & WX1 & _).
      pose proof (opnd_facts _ _ _ _ _ _ dA CS1 opndA) as (MA1 & CRA1 & CRAL1 & _).
      pose proof (opnd_sep_l _ _ _ _ _ _ 0%nat _ dA CS1 eq_refl opndA) as (SXA1 & OXA1).
      pose proof HCOPY as COPY. unfold mpi_copy_stmt_x, U_MPI_COPY in COPY.
      eapply aevtM_cut; [eapply COPY with (h := h) (LB := LB) (lo := lo) (dX := mkMPD (SP + -144) 1 0 0 [] padX LNull) (dY := dA) |].
      1: exact HP1.
      1: exact MX1.
      1: exact NSX1.
      1: exact MA1.
      1: exact SXA1.
      1: rewrite unsigned_lit by lia; apply copy_sep_of_opnd; [exact OXA1| exact (Z.lt_le_incl _ _ (proj1 (proj2 (proj2 (proj1 MA1)))))].
      1: exact CRA1.
      1: exact CRAL1.
      1: rewrite unsigned_lit by lia; exact WX1.
      1: rewrite unsigned_lit by lia; exact ST1.
      1: rewrite unsigned_lit by lia; lia.
      1: exact ACL.
      1: rewrite unsigned_lit by lia; lia.
      1: rewrite unsigned_lit by lia; lia.
      1: exact DHI.
      1: exact TP.
      1: exact MI1.
      1: exact SOK1.
      1: exact CA.
      1: reflexivity.
      1: reflexivity.
      clear HP1 MX1 NSX1 WX1 MA1 CRA1 CRAL1 SXA1 OXA1 SOK1 MI1 ST1.
      intros ms' mo' PO.
      binop_post PO m2 mo2 h2 LB2 d2 r2 E2 MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
      replace (ret_pc (Z_to_bv 64 134840)) with (Z_to_bv 64 134840) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MOK2.
      pose proof RR2 as (CR2 & _).
      pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 0%nat _ m2 mo2 h2 LB2 d2 CS1 eq_refl HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2
                    (proj2 (proj2 (proj2 CR2)))) as CS2.
      cbn [set_nth] in CS2.
      pose proof (proj1 (proj2 CR2)) as AD2. cbn [md_addr] in AD2.
      assert (LOCS2 : locals_at [d2; mkMPD (SP + -160) 1 0 0 [] padY LNull; mkMPD (SP + -176) 1 0 0 [] padZ LNull;
                                 mkMPD (SP + -192) 1 0 0 [] padT LNull])
        by (unfold locals_at; cbn [map md_addr]; rewrite AD2; reflexivity).
      destruct CR2 as [[(-> & _ & _) | (-> & _)] _].
      2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep. if_true.
           eapply L_err; [exact CS2| exact LOCS2| reflexivity| reflexivity| lia| exact BPOS]. }
      pose proof (copy_local_facts m2 LB LB2 (mkMPD (SP + -144) 1 0 0 [] padX LNull) dA d2 MA2 (proj2 MA0)
                    (proj1 (proj2 OUT2)) eq_refl eq_refl (proj1 RR2) (proj2 RR2 eq_refl) ltac:(lia))
        as (AB2 & N2 & OWN2 & LOW2 & HIB2).
      clear CS1 LOCS RR2 HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2 MOKq.
      zstep. if_false.
      (* copy(Y, B) *)
      do 3 zstep.
      pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (HP2 & _ & _ & SOK2 & MI2 & ST2 & _ & _).
      pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 1%nat _ CS2 eq_refl) as (MY2 & NSY2 & WY2 & _).
      pose proof (opnd_facts _ _ _ _ _ _ dB CS2 (or_introl opndB)) as (MB2 & CRB2 & CRBL2 & _).
      pose proof (opnd_sep_l _ _ _ _ _ _ 1%nat _ dB CS2 eq_refl (or_introl opndB)) as (SYB2 & OYB2).
      eapply aevtM_cut; [eapply COPY with (h := h2) (LB := LB2) (lo := lo) (dX := mkMPD (SP + -160) 1 0 0 [] padY LNull) (dY := dB) |].
      1: exact HP2.
      1: exact MY2.
      1: exact NSY2.
      1: exact MB2.
      1: exact SYB2.
      1: rewrite unsigned_lit by lia; apply copy_sep_of_opnd; [exact OYB2| exact (Z.lt_le_incl _ _ (proj1 (proj2 (proj2 (proj1 MB2)))))].
      1: exact CRB2.
      1: exact CRBL2.
      1: rewrite unsigned_lit by lia; exact WY2.
      1: rewrite unsigned_lit by lia; exact ST2.
      1: rewrite unsigned_lit by lia; lia.
      1: exact ACL.
      1: rewrite unsigned_lit by lia; pose proof (cs_parts _ _ _ _ _ _ _ CS2) as (_ & HTq & _); lia.
      1: rewrite unsigned_lit by lia; lia.
      1: exact DHI.
      1: exact TP.
      1: exact MI2.
      1: exact SOK2.
      1: exact CA.
      1: reflexivity.
      1: reflexivity.
      clear HP2 MY2 NSY2 WY2 MB2 CRB2 CRBL2 SYB2 OYB2 SOK2 MI2 ST2 COPY.
      intros ms' mo' PO.
      binop_post PO m3 mo3 h3 LB3 d3 r3 E3 MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR3.
      replace (ret_pc (Z_to_bv 64 134856)) with (Z_to_bv 64 134856) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MOK3.
      pose proof RR3 as (CR3 & _).
      pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 1%nat _ m3 mo3 h3 LB3 d3 CS2 eq_refl HH3 HT3 MF3 MA3 OUT3 PX3 SOK3 MI3 ST3
                    (proj2 (proj2 (proj2 CR3)))) as CS3.
      cbn [set_nth] in CS3.
      pose proof (proj1 (proj2 CR3)) as AD3. cbn [md_addr] in AD3.
      assert (LOCS3 : locals_at [d2; d3; mkMPD (SP + -176) 1 0 0 [] padZ LNull; mkMPD (SP + -192) 1 0 0 [] padT LNull])
        by (unfold locals_at; cbn [map md_addr]; rewrite AD2, AD3; reflexivity).
      destruct CR3 as [[(-> & _ & _) | (-> & _)] _].
      2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep. if_true.
           eapply L_err; [exact CS3| exact LOCS3| reflexivity| reflexivity| lia| exact BPOS]. }
      pose proof (copy_local_facts m3 LB2 LB3 (mkMPD (SP + -160) 1 0 0 [] padY LNull) dB d3 MA3 (proj2 MB0)
                    (proj1 (proj2 OUT3)) eq_refl eq_refl (proj1 RR3) (proj2 RR3 eq_refl) BPOS)
        as (AB3 & N3 & OWN3 & LOW3 & HIB3).
      assert (NYX : md_n d3 <= md_n d2).
      { destruct LOW3 as [ONE3 | POW3]; [lia|].
        assert (LTP : 2 ^ (32 * (md_n d3 - 1)) < 2 ^ (32 * md_n d2)) by lia.
        apply (proj2 (Z.pow_lt_mono_r_iff 2 (32 * (md_n d3 - 1)) (32 * md_n d2) ltac:(lia) ltac:(lia))) in LTP. lia. }
      zstep. if_false.
      eapply L_m1; [exact CS3| exact LOCS3| exact OWN2| exact OWN3| reflexivity| reflexivity| exact NYX| lia
                   | exact AB2| exact AB3| lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma es_at : Forall (fun e => mpd_at usegs m LB e) es.
  Proof using MA0 MB0.
    unfold es. destruct ALIAS.
    - apply Forall_cons; [exact MB0| apply Forall_nil].
    - apply Forall_cons; [exact MA0| apply Forall_cons; [exact MB0| apply Forall_nil]].
  Qed.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "".
  Lemma div_val_T0 : forall a p pd own, mpd_val (mkMPD a 1 1 p [Z_to_bv 64 0] pd own) = 0.
  Proof. intros. unfold mpd_val. cbn [md_sg md_limbs]. vm_compute. reflexivity. Qed.

  Lemma div_T_opnd : forall (mm : mem) (P Q SPx : Z) (w : word),
    rw_cells usegs mm P [C4 (Z_to_bv 64 0)] ->
    rw_cells usegs mm Q [C8 (Z_to_bv 64 P); C4 (Z_to_bv 64 65537); C4 w] ->
    0 < Q -> Q mod 8 = 0 -> 0 < P -> P mod 4 = 0 -> SPx <= P -> P + 4 < 2^64 ->
    stack_opnd usegs mm SPx (mkMPD Q 1 1 P [Z_to_bv 64 0] w LStatic).
  Proof using DIMG sp.
    intros mm P Q SPx w LIMB HDR Qpos Qal Ppos Pal LOWP HIGHP.
    apply (rw_cells_split_C4 usegs mm Q [C8 (Z_to_bv 64 P)] _ [C4 w]) in HDR.
    rewrite (unsigned_lit 65537) in HDR by lia. cbn [app] in HDR.
    apply (rw_cells_C2_congr usegs mm Q [C8 (Z_to_bv 64 P)] 65537 1 _) in HDR; [| reflexivity].
    apply (rw_cells_C2_congr usegs mm Q [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 1)] (65537 / 2 ^ 16) 1 _) in HDR; [| reflexivity].
    pose proof (proj1 (LxPMpiTac.u32arr_of_rw_cells mm P [Z_to_bv 64 0] LIMB)) as BYTES.
    unfold stack_opnd; cbn [md_own md_addr md_p md_sg md_n md_pad md_limbs].
    split; [reflexivity|]. split; [exact HDR|]. split; [exact Qal|]. split; [exact Qpos|].
    split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; [lia|]. split; [exact Pal|].
    split; [exact Ppos|]. split; [exact BYTES|]. split; [exact LOWP|]. split; [lia|]. left; reflexivity.
  Qed.

  Local Ltac div_cb4_first FRc :=
    let rec upto cs :=
      lazymatch cs with
      | CB 4%nat _ :: _ => constr:(@nil cell)
      | ?c :: ?rest => let p := upto rest in constr:(c :: p)
      end in
    lazymatch type of FRc with
    | rw_cells ?sg ?mm ?A ?cs =>
        let p := upto cs in
        apply (rw_cells_CB4_C4 sg mm A p) in FRc; cbn [app] in FRc
    end.

  Lemma L_div : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    aevtM usegs mo POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dR)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dB)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20df4) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
    pose proof (bv_unsigned_in_range 64 sp) as SPrng. change (bv_modulus 64) with (2^64) in SPrng.
    pose proof alloc_ceiling_pos as ACpos.
    pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MOKm.
    (* Walk on a name m0 for the entry memory: the frame stores then rewrite only hypotheses over m0, and the
       section hypotheses over m (HH0, SOK0, MI0, ...) that mc_init and the later walk lemmas depend on stay intact. *)
    lazymatch goal with |- aevtM ?sg ?mo' ?P (MS ?R ?F' ?pc ?fc' ?rv m ?ro) =>
      cut (forall m0 : mem, m0 = m -> stk usegs m0 lo SP -> mem_inv usegs m0 -> aevtM sg mo' P (MS R F' pc fc' rv m0 ro));
      [intros GEN; exact (GEN m eq_refl ST0 MI0)|] end.
    intros m0 Em0 STw MIw.
    carve_frame 288%nat STw.
    pose proof (munch_refl [(lo, SP)] m0) as MUw. pose proof (wmono_refl usegs m0) as WMw.
    do 27 zstep.
    subst m0.
    lazymatch goal with FRx : rw_cells _ ?mm _ (CB 144 ?ja :: C4 _ :: CB 20 ?jb :: _ :: _ :: CB 4 ?jc :: _) |- _ =>
      rename mm into m2; set (j0 := ja) in FRx; set (jm := jb) in FRx; set (jt := jc) in FRx end.
    apply (rw_cells_split_CB usegs m2 SPc [CB 144 j0; C4 (Z_to_bv 64 0)] 20 jm _ [12; 4; 4]%nat) in FR; [| reflexivity].
    cbn [app mk_CB_cells] in FR.
    do 3 div_cb4_first FR.
    take FR 3%nat FRA. take FR 5%nat FRT.
    pose proof FRA as LIMB. take LIMB 1%nat J0c. take LIMB 1%nat LIMB0.
    pose proof FRT as HDR. take HDR 2%nat T160c.
    assert (CS1 : CST m2 mo h LB [] dR []
                    [(SPc, [CB 144 j0; C4 (Z_to_bv 64 0); CB 12 (firstn 12 jm)]);
                     (SP + -128, tcells (wof (firstn 4 (skipn 12 jm))) (wof (firstn 4 (skipn 4 (skipn 12 jm))))
                                   (Z_to_bv 64 (SP + -144)) (Z_to_bv 64 65537) (wof jt));
                     (SP + -104, REGS)] []).
    { apply (mc_init m2 [] _ HH0 SOK0 MI0 MR0 es_at MUw WMw MIw STw).
      - apply Forall_nil.
      - intros i j di dj Ei. destruct i; discriminate Ei.
      - apply Forall_cons; [exact FRA|]. apply Forall_cons; [exact FRT|]. apply Forall_cons; [exact FR| apply Forall_nil].
      - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd cells_size csize tcells Nat.add];
          (split; [lia| split; [lia| intros d []]]). }
    pose proof (opnd_facts _ _ _ _ _ _ dB CS1 (or_introl opndB)) as (MB2 & _ & _ & _ & PB2 & _).
    pose proof HCMPO as CMPO. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in CMPO.
    eapply aevtM_cut_evt; [exact MOKm | eapply CMPO with (LB := LB) (dX := dB)
        (dY := mkMPD (SP + -120) 1 1 (SP + -144) [Z_to_bv 64 0] (wof jt) LStatic) |].
    1: left; exact MB2.
    1: right; rewrite unsigned_lit by lia; apply div_T_opnd; [exact LIMB0| exact HDR| lia ..].
    1: intros O; exact (proj1 (PB2 O)).
    1: intros O; discriminate O.
    1: exact MIw.
    1: reflexivity.
    1: reflexivity.
    intros ms' PO. unfold mpi_cmp_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & -> & _ & _ & _).
    replace (ret_pc (Z_to_bv 64 134752)) with (Z_to_bv 64 134752) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite div_val_T0, Z.sub_0_r.
    eapply L_main; [exact CS1| exact MUw| exact WMw].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Walk.

  Theorem U_mpi_div_mpi_ok : mpi_div_mpi_stmt usegs L HI U_MPI_DIV_MPI MSF.
  Proof using HCALLOC HLS SW DIMG HND ROIMG IMGC HCOPY HGROW HSHL HCMP HAS HLSET HMULI HCBL HCMPO HSHR HCABS HZF HPZ.
    unfold mpi_div_mpi_stmt, U_MPI_DIV_MPI.
    intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB dX dA dB lo
      HPm MDX MDA MDB SPXA SPXB SPAB NSTX NEXB OSXA OSXB CRDA CRLA CRDB CRLB WRX RLOX STKm LOW CEIL TOPm ALN DHIm TPm MIm SOKm CMSF
      A1E A2E A3E.
    subst a1 a2 a3.
    eapply L_div; eassumption.
  Qed.
End DivP.
