(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P030280b797b19d8e 0 2 0 1 12 4294967296P038fa1ec46d1c06c 0 2 0 1 11 1P0484898f58cdc6cb 0 2 0 1 11 1P07444bad33cd7598 0 2 0 1 12 1P08e55d6ab914c55e 0 2 0 1 1 1P09744c55888b13d7 0 2 0 1 10 1P0c628761c6f9e956 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P0dd46cc75ad72bdd 1 1 8 2 20 1 36 1 3 0 1 35 1 37 8P0de992cc9593cb85 0 2 0 1 11 1P0e57870d7d8e94e5 0 2 1 1 18 1P0f7bf8b16f40b8ae 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P10dc21699850af8d 1 1 8 2 0 1 36 1 3 17 1 35 1 37 8P1172d83055fb9b23 1 1 4294967296 1 0 1 2 1 1 36 1P11d3a2f7a1ff583c 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P158f22506ec66330 0 5 0 1 23 1 24 1 31 1 32 1P168b777818599d5f 1 1 8 2 0 1 36 1 3 16 1 35 1 37 8P17362e68d0740a87 0 2 0 1 1 1P18ea6435dfaec502 0 2 0 1 10 1P19893271af0ac1f5 0 2 0 1 10 1P1a15649091b6e21d 1 1 8 2 23 1 36 1 3 0 1 35 1 37 8P1a1b679569bed3d8 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P1b890f2ea2b38419 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P1c5047335cb34d88 0 2 0 1 12 1P1cb5479dca3ab4fe 0 2 0 1 1 1P1d4ab2444b39c773 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P1f37603f6fbccae4 0 2 0 1 11 1P20013746daf0bb91 2 13 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P2243de637785e5d4 0 2 0 1 11 1P23972668c3e724a7 0 2 0 1 12 1P23df5c772a2c91a4 2 19 1 1 8 3 1 1 40 1 41 1 6 0 1 31 1 32 1 39 1 42 1 43 8 1 1 8 3 2 1 39 1 42 1 4 0 2 40 2 41 2 43 16P24f2208f080b989d 0 2 0 1 12 1P26ad53499cecbf08 0 2 0 1 11 1P26c4b325ebf42700 2 13 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P270c245af61d642d 2 13 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P2805ea3b70413c60 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P29b87fb3298c4dbf 0 4 0 8 16 8 35 8 36 8P2cb335668a67b47a 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P2e11e911b6b0758f 0 5 0 1 29 1 30 1 37 1 38 1P2e820e9e7beeab99 0 2 0 1 2 1P30cc6cd240391d58 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P33e29cfe936d7f85 2 14 1 1 8 3 2 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 2 38 2 39 2 41 16P33e839edada0ab91 0 4 0 8 17 8 35 8 36 8P36a815c8ae1e8741 2 13 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P3784a826a235eaf2 0 2 0 1 12 1P3a2adfb5f9165f8c 0 5 0 1 31 1 32 1 39 1 40 1P3a39d3dd44caca26 1 1 8 2 0 1 35 1 3 1 1 36 1 37 8P3bdce4bcb214580c 2 13 1 1 8 3 2 1 34 1 35 1 6 0 1 25 1 26 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 2 34 2 35 2 37 16P3d176aec9b2df3b8 1 1 8 2 0 1 35 1 3 1 1 36 1 37 8P3f2dffb59925765a 1 1 8 2 0 1 35 1 3 2 1 36 1 37 8N0031ecb69d412f8fN00f500344235844bN0175eda9addecf39N025d5b4e5d586d81N02ef7a2961dc4ad4N035f388f8fcabfbaN03eff9637bb97210N056f9cfa000820c3N06308818aefce182N073003f776926c3eN07ae4d484a205fabN07c0b9df7612bd0eN07c7d1affd8f7c7bN08bc76ebbee55ab1N08df2dd90c0e189fN0a10826e865fe305N0b0b95465221ae95N0b579fcbb9c9dce3N0d62820dba32ca71N0d81537b073387fcN0dc79de87c5d67a9N0e1bd8a3c4c20244N0e360dac985e437cN0f3fd88255eef2f7N10866edd8daeb884N10fcb51c920c63e8N114012103b325611N11f2ef1170df5361N121f8e052e7fafaaN12af46cf1a48dadeN137c1b8dfa19f444N13c31ed02194e751N13c82c72e3ef7bcfN1569e0f92c703601N1744658cdaef4931N1a3c4876d034a282N1abe802de0962c01N1bd38b9e4eb50195N1cd7bdebd149cb3eN1d98c82e301248d6N1d9da3db6334ae2cN1ed35614f186d7f8N1fb98a5796975566N20a2d8115b4e2dd7N2270e55037318db7N249c20246b08aaa7N2569310c03596307N2907ad24683a1df6N29cf9d3986afa675N2df5fa5aa1f6ae69N2f77fe1dfea1a51aN2fb3915c58c927daN302fa1fca5968d43N3124a559f4ad0e92N33aed3ef0cf8c3b8N3443b03e74e39798N3486f667faed07c7N349f07e526ff7d88N3687a5a8877eb678N374ac5e801fc5b6bN37c40c75b2ed33e8N37d641f8a325c166N37f07180ca46d047N3804da571af739e3N387a4fd21fd02c23N39b7fb195624e07bN3b48998cd1f51fd7N3c016dfff1eaab90N3c1564a0850e0e0dN3cf5511cc412a2a3N3e0660ea10517cc5N3f30e0d3665c285eN3f7297af316cc7d2N3fc6c374b789569d"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_copy () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "copy_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "copy_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "copy_Rx"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "trim_i"; "zeros_above"; "Corelib.Init.Peano.le"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.zx16"; "Stdlib.ZArith.BinInt.Z.ge"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"].


Definition U_MPI_COPY : Z := 0x1f638.
Definition U_MEMSET : Z := 0x46e44.
Notation MPI_COPY_STACK := 80 (only parsing).

(* [comment removed for export] *)
Definition copy_R (dY dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "(0.(1.(0.(2.$3.O2.=)(0.(2.$3.(4.O1.)(4.O5.))(0.(5.(6.O4.)(6.O1.))(5.(6.O1.)(7.(6.O4.)(6.O5.))))))(0.(2.$3.O2.$8.)(0.(2.$3.(6.O1.)(6.O4.))(0.(2.$3.(9.O1.)(9.O4.))(0.(2.(:.(;.&40.))(<.O1.)(<.O4.))(2.$=.(>.O1.)(>.O4.)))))))(0.(2.$3.(?.O1.)(?.O4.))(0.(2.(;.&40.)(10.O1.)(10.O4.))Pb,$11.P,(12.$11.R1.(13.O1.))(1.(12.$11.R2.(13.O4.))(14.(12.$11.R2.O3.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition copy_sep (dX dY : mpd) (lo SP : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "(0.P,(14.(2.$=.(>.O3.)$15.))(1.(5.(16.(?.O4.)+10.)(9.O3.))(5.(16.(9.O3.)(17.+4.(6.O3.)))(?.O4.)))(0.P,(2.$=.(>.O4.)$18.)(1.(5.(16.(?.O3.)+10.)(9.O4.))(5.(16.(9.O4.)(17.+4.(6.O4.)))(?.O3.)))(0.(1.(2.$19.O4.O3.)(1.(14.(2.$=.(>.O4.)$18.))(1.(2.$=.(>.O3.)$15.)(1.(5.(16.(9.O4.)(17.+4.(6.O4.)))(9.O3.))(5.(16.(9.O3.)(17.+4.(6.O3.)))(9.O4.))))))(0.(1.(5.(16.(?.O3.)+10.)O2.)(5.O1.(?.O3.)))(0.P,(14.(2.$=.(>.O3.)$15.))(1.(5.(16.(9.O3.)(17.+4.(6.O3.)))O2.)(5.O1.(9.O3.)))Pa,$3.P,(0.(5.(?.O3.)R1.)(1:.R1.(16.(?.O3.)+10.)))(5.=R2.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition copy_trim (dY dX dX' : mpd) : Prop :=
  md_n dX' = md_n dX \/ md_n dX' = 1 \/ 2 ^ (32 * (md_n dX' - 1)) <= mpd_abs dY.
Definition copy_Rx (dY dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop :=
  copy_R dY dX LB r dX' /\ (r = 0 -> copy_trim dY dX dX').
Definition trim_i (ys : list word) (i : Z) : Prop :=
  i = 1 \/ exists w, nth_error ys (Z.to_nat (i - 1)) = Some w /\ bv_unsigned w mod 2^32 <> 0.

Definition mpi_copy_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "Pra,(;.&40.)Psp,(;.&40.)Pgp,(;.&40.)Ptp,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Ps0,(;.&40.)Ps1,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Ps2,(;.&40.)Ps3,(;.&40.)Ps4,(;.&40.)Ps5,(;.&40.)Ps6,(;.&40.)Ps7,(;.&40.)Ps8,(;.&40.)Ps9,(;.&40.)Ps10,(;.&40.)Ps11,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)PF,(1;.&5.(;.&40.))Pfc,(;.&20.)Pm,P,(;.&40.)(1<.(;.&8.))Pmo,$1=.Ph,(1>.O5.O4.O3.)PLB,(:.$11.)PdX,$19.PdY,$19.Plo,$3.P,(1?.O5.O4.O3.R5.R4.R7.R6.)P,(20.O5.R8.R5.R4.)P,(14.(2.$=.(>.R5.)$21.))P,(20.O5.R:.R7.R5.)P,(22.R7.R6.)P,(23.R8.R7.R6.(24.&40.R2<.))P,(25.O4.R:.R7.(?.R8.)+10.)P,P,(2.$=.(>.R9.)$18.)(25.O4.R<.R9.(9.R:.)(17.+4.(6.R:.)))P,(26.O4.R<.(24.&40.R2?.)(27.O5.O4.O3.R=.)R;.)P,(28.O5.R10.R:.(24.&40.R30.))P,(5.R;.(29.(29.(24.&40.R31.)+50.)(2:.O4.)))P,(5.(2;.O4.)R<.)P,(5.(24.&40.R33.)(27.O5.O4.O3.R11.))P,(2.$3.(2<.(24.&40.R34.)+10.)=)P,(5.(2=.O4.)(2;.O4.))P,(2.(;.&40.)R34.(2>.&40.(2?.O4.)))P,(30.O5.R17.)P,(31.O5.O4.R18.)P,(32.O4.O1.+8.)P,(2.(;.&40.)R32.(2>.&40.(?.R16.)))P,(2.(;.&40.)R32.(2>.&40.(?.R16.)))(33.O5.R1;.(34.O5.O4.O3.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1>.R1=.R1:.R19.R18.(35.R17.R18.R19.)R16.R1<.R1;.)(36.(37.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(2>.&40.O2.)R1=.(38.(;.&40.))R1<.(39.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_copy_stmt_x (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "Pra,(;.&40.)Psp,(;.&40.)Pgp,(;.&40.)Ptp,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Ps0,(;.&40.)Ps1,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Ps2,(;.&40.)Ps3,(;.&40.)Ps4,(;.&40.)Ps5,(;.&40.)Ps6,(;.&40.)Ps7,(;.&40.)Ps8,(;.&40.)Ps9,(;.&40.)Ps10,(;.&40.)Ps11,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)PF,(1;.&5.(;.&40.))Pfc,(;.&20.)Pm,P,(;.&40.)(1<.(;.&8.))Pmo,$1=.Ph,(1>.O5.O4.O3.)PLB,(:.$11.)PdX,$19.PdY,$19.Plo,$3.P,(1?.O5.O4.O3.R5.R4.R7.R6.)P,(20.O5.R8.R5.R4.)P,(14.(2.$=.(>.R5.)$21.))P,(20.O5.R:.R7.R5.)P,(22.R7.R6.)P,(23.R8.R7.R6.(24.&40.R2<.))P,(25.O4.R:.R7.(?.R8.)+10.)P,P,(2.$=.(>.R9.)$18.)(25.O4.R<.R9.(9.R:.)(17.+4.(6.R:.)))P,(26.O4.R<.(24.&40.R2?.)(27.O5.O4.O3.R=.)R;.)P,(28.O5.R10.R:.(24.&40.R30.))P,(5.R;.(29.(29.(24.&40.R31.)+50.)(2:.O4.)))P,(5.(2;.O4.)R<.)P,(5.(24.&40.R33.)(27.O5.O4.O3.R11.))P,(2.$3.(2<.(24.&40.R34.)+10.)=)P,(5.(2=.O4.)(2;.O4.))P,(2.(;.&40.)R34.(2>.&40.(2?.O4.)))P,(30.O5.R17.)P,(31.O5.O4.R18.)P,(32.O4.O1.+8.)P,(2.(;.&40.)R32.(2>.&40.(?.R16.)))P,(2.(;.&40.)R32.(2>.&40.(?.R16.)))(33.O5.R1;.(34.O5.O4.O3.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1>.R1=.R1:.R19.R18.(3:.R17.R18.R19.)R16.R1<.R1;.)(36.(37.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(2>.&40.O2.)R1=.(38.(;.&40.))R1<.(39.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050>D44021889276.4D47490711301.4D49029298798.4D50827930528.1D7686832576.4 00000100400700:00ASS1aS1aS1bS1w1a1b". (* [comment removed for export] *)
Lemma limbs_val_app : forall a b, limbs_val (a ++ b) = limbs_val a + 2 ^ (32 * Z.of_nat (length a)) * limbs_val b.
Proof.
  induction a as [|w a IH]; intros b; cbn [app length].
  - rewrite Z.mul_0_r, Z.pow_0_r. cbn [limbs_val]. dlia.
  - cbn [limbs_val]. rewrite IH. replace (32 * Z.of_nat (S (length a))) with (32 + 32 * Z.of_nat (length a)) by dlia.
    rewrite Z.pow_add_r by dlia. dlia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>D61024089806.4000001S". (* [comment removed for export] *)
Lemma limbs_val_zeros : forall ws, (forall k w, nth_error ws k = Some w -> bv_unsigned w mod 2^32 = 0) -> limbs_val ws = 0.
Proof.
  induction ws as [|w ws IH]; intros H; cbn [limbs_val]; [reflexivity|].
  rewrite (H 0%nat w eq_refl). rewrite IH; [dlia|]. intros k w' Hk. exact (H (S k) w' Hk).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma limbs_val_repeat0 : forall k, limbs_val (repeat (Z_to_bv 64 0) k) = 0.
Proof. intros k. apply limbs_val_zeros. intros j w Hj. apply nth_error_In in Hj. apply repeat_spec in Hj. subst w. reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L42464375761.5L42464375761.8L43868116880.9L44015161774.9L44700446647.6L49026503484.900000100400900>00L00QSS1kS1y1kS1y1kS2ys1w2NZ1H2H0S1y1k". (* [comment removed for export] *)
Lemma limbs_val_nth_lower : ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "Pys,(:.(;.&40.))Pk,$3;.Pw,(;.&40.)P,(2.(1<.(;.&40.))(3<.(;.&40.)R3.R2.)(3=.(;.&40.)R1.))P,(14.(2.$3.(2<.(24.&40.R2.)(3>.+2.+20.))=))(5.(3>.+2.(17.+20.(3?.R4.)))(40.R5.))")
(* [comment removed for export] *).
Proof.
  induction ys as [|y ys IH]; intros k w Hk NZ; [destruct k; discriminate|].
  destruct k as [|k]; cbn [nth_error] in Hk; cbn [limbs_val].
  - injection Hk as ->. pose proof (limbs_val_nonneg ys). pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)). lia.
  - pose proof (IH k w Hk NZ). pose proof (Z.mod_pos_bound (bv_unsigned y) (2^32) ltac:(lia)).
    replace (32 * Z.of_nat (S k)) with (32 + 32 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition zeros_above (ys : list word) (i : Z) : Prop :=
  forall k w, (Z.to_nat i <= k)%nat -> nth_error ys k = Some w -> bv_unsigned w mod 2^32 = 0.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>D39475314974.4D8077075840.7 00000600;S2ys1iS1i1k". (* [comment removed for export] *)
Lemma limbs_val_firstn : forall ys i, 0 <= i -> zeros_above ys i -> limbs_val (firstn (Z.to_nat i) ys) = limbs_val ys.
Proof.
  intros ys i Hi HZ. rewrite <- (firstn_skipn (Z.to_nat i) ys) at 2. rewrite limbs_val_app.
  rewrite (limbs_val_zeros (skipn (Z.to_nat i) ys)); [dlia|].
  intros k w Hk. rewrite nth_error_skipn in Hk. eapply HZ; [| exact Hk]. dlia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma sx16_sign : forall s, s = 1 \/ s = -1 -> sx16 (Z_to_bv 64 s) = Z_to_bv 64 s.
Proof. intros s [->| ->]; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma lor_land3_0 : forall a b, a mod 4 = 0 -> b mod 4 = 0 -> Z.land (Z.lor a b) 3 = 0.
Proof.
  intros a b Ha Hb. rewrite Z.land_lor_distr_l. change 3 with (Z.ones 2).
  rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Ha, Hb. reflexivity.
Qed.

Local Ltac cond_decide :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  repeat match goal with
    | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
    | |- context [Z.ltb ?x ?y] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
    | |- context [Z.eqb ?x ?y] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
    | |- context [Z.b2z ?b] => progress cbn [Z.b2z]
    | |- context [negb ?b] => progress cbn [negb]
    | |- context [Z.lxor ?x ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
  end; reflexivity.
Local Ltac if_false_x :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      let E := fresh "E" in assert (E : c = false) by cond_decide; rewrite E; cbv_concl_iota; clear E
  end.
Local Ltac land_zero_any :=
  repeat match goal with
  | |- context [Z.land (Z.lor ?a ?b) 3] => rewrite (lor_land3_0 a b) by lia
  | |- context [Z.land ?p 7] => let E := fresh "E" in
      assert (E : Z.land p 7 = 0) by (change (Z.land p 7) with (Z.land p (Z.ones 3)); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia);
      rewrite E; clear E
  | |- context [Z.land ?p 3] => let E := fresh "E" in
      assert (E : Z.land p 3 = 0) by (change (Z.land p 3) with (Z.land p (Z.ones 2)); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia);
      rewrite E; clear E
  end.

Section CopyP.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr usegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.

  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.13L18926747689.13L18926759668.1300000:00;00@S1a1b1k2HkSS1a1b". (* [comment removed for export] *)
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L18932482474.10L27106854092.10L44022087408.10000001004005SS1nS". (* [comment removed for export] *)
  Lemma sh32m1 : forall n, Z.shiftr (4294967296 * n + -4294967296) 32 = n - 1.
  Proof.
    intros n. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
    replace (4294967296 * n + -4294967296) with ((n - 1) * 4294967296) by lia. rewrite Z.div_mul by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Ltac fix_regs :=
    repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
      let z := constr:(Zpos p) in
      lazymatch eval compute in (Z.leb (2^63) z) with
      | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
      end end.


  Lemma frame_junk8 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "Pmq,P,(;.&40.)(1<.(;.&8.))PA,$3.Pbs,(:.(;.&8.))Prest,(:.$41.)P,(42.$43.R4.R3.(44.$41.(45.#8.R2.)R1.))(42.$43.R5.R4.(44.$41.(46.(47.R3.))R2.))")
(* [comment removed for export] *).
  Proof.
    intros mq A bs rest H. flat constr:(H) 2%nat. intros ((LEN & WF) & _) _. cbn [cell_wf] in LEN.
    eapply rw_cells_reshape; [exact H| split; [exact I| exact WF]|].
    cbn [cells_bytes cbytes]. rewrite le8_le_bytes_to_word by exact LEN. reflexivity.
  Qed.

  Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (lo : Z)
            (X sgX nX pX : Z) (xs : list word) (padX : word) (ownX : limb_own)
            (Y sgY nY pY : Z) (ys : list word) (padY : word) (ownY : limb_own).
  Let dX := mkMPD X sgX nX pX xs padX ownX.
  Let dY := mkMPD Y sgY nY pY ys padY ownY.
  Hypothesis HH0 : HEAP usegs L HI h LB m mo.
  Hypothesis MAX : mpd_at usegs m LB dX.
  Hypothesis NST : ownX <> LStatic.
  Hypothesis MAY : mpd_at usegs m LB dY.
  Hypothesis NEQ : X <> Y.
  Hypothesis SEP : mpd_sep dX dY.
  Hypothesis CSEP : copy_sep dX dY lo (bv_unsigned sp).
  Hypothesis YCR : client_range L LB lo Y 16.
  Hypothesis YLCR : ownY = LHeap -> client_range L LB lo pY (4 * nY).
  Hypothesis XW : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dX.
  Hypothesis SLO : lo <= bv_unsigned sp - MPI_COPY_STACK - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv usegs m.
  Hypothesis SOK0 : statics_ok usegs L m.
  Hypothesis CA : const_at L U_MEMSET_FUNC 8.

  Notation POST := (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (copy_Rx dY dX LB) lo m mo).
  (* [comment removed for export] *)
Notation FRAME8 x := ([C8 x; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?D30309475896.85D45370438041.85D60453088131.85D63312638695.85D65500065799.83D774846548.83  D819727256.85  D9364571742.85 00000K00_01:01U01i02P02d03?S2sp1X2xs1Y2nY2ys3NRY2XB2YBS2sp1X2xs1Y2ys2XB2YBS2sp1X2nX2xs1Y2ys3NRX2XB2YBS2sp1X2nX2xs1Y2ys3NRX2XB2YBS2sp1X2xs1Y2ys2XB2YBS1L3HLS2sp2lo1X2xs1Y2ys3SLO2X02Y02XB2YBS2sp1X2xs1Y2ys2XB2YBS2sp1X2xs1Y2nY2ys3NRY2XB2YB". (* [comment removed for export] *)
  Lemma facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "(0.(2.$3.(2<.VX,+8.)=)(0.(1:.=VX,)(0.(2.$3.(3?.(48.(;.&40.)Vxs,))VnX,)(0.(0.(5.=VnX,)(5.VnX,+2710.))(0.(1.(2.$3.VsgX,+1.)(2.$3.VsgX,-1.))(0.(2.$3.(2<.VY,+8.)=)(0.(1:.=VY,)(0.(2.$3.(3?.(48.(;.&40.)Vys,))VnY,)(0.(0.(5.=VnY,)(5.VnY,+2710.))(0.(1.(2.$3.VsgY,+1.)(2.$3.VsgY,-1.))(0.(5.(16.VX,+10.)(3>.+2.+40.))(0.(5.(16.VY,+10.)(3>.+2.+40.))(0.(1.(5.(16.VX,+10.)VY,)(5.(16.VY,+10.)VX,))(1.(5.(16.VX,+10.)Vlo,)(5.(24.&40.Vsp,)VX,)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(MAX) 2%nat. intros FLt1 SGX. flat constr:(FLt1) 2%nat. flclear FLt1. intros CHX FLt2. flat constr:(FLt2) 5%nat. flclear FLt2. intros XAL X0 LENX NRX _. flat constr:(MAY) 2%nat. intros FLt3 SGY. flat constr:(FLt3) 2%nat. flclear FLt3. intros CHY FLt4. flat constr:(FLt4) 5%nat. flclear FLt4. intros YAL Y0 LENY NRY _.
    cbn [dX dY md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold MPI_MAX_LIMBS in NRX, NRY.
    pose proof (rw_cells_bound _ _ _ _ CHX) as XB. pose proof (rw_cells_bound _ _ _ _ CHY) as YB.
    unfold mpi_cells in XB, YB. cbn [cells_size csize Nat.add] in XB, YB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros HBR _. flat constr:(XW) 3%nat. intros XCW _ _. cbn [dX md_addr] in XCW.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(dlia) HBR DHI ACL ltac:(dlia)) as XS.
    destruct SEP as [E|SEP']; [exfalso; apply NEQ; injection E; auto|]. cbn [dX dY md_addr] in SEP'.
    (flsplit; repeat split); try assumption; dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00`0@D10366616433.168D19026868104.172D20040761447.168D20662043991.154D2487047200.155 D2487062599.157 D29425296123.157D29425313436.155D3238745851.157 D3251329070.168 D33818513991.157D3556193230.173 D35944776366.168D41413713102.154D41523223527.155D4260097829.173 D52101704109.175D52101733636.171D52101802538.181D52103794831.173D54391985784.173D54398282304.172D57751203752.174D66345858476.155D66345873867.157D7839374885.157 D8077075840.171 L10927556835.169L1120085281.145 L11741095640.160L17636578342.169L22700267513.168L26274826249.169L26924648792.160L27911231108.169L32879090465.0  L38720243939.169L40263536192.167L40263536192.169L41250020593.3  L43654564952.160L51709126249.168L59499841752.160L61251806371.169L66267994430.144L7510805464.160 L982998592.4    R22706564033.17600000X01Z02D02i03n05306@07M08R09W0:M0;:0<?0<b0=g0>R0?\0@g0B70B^0D10EO0FO0G\0Hi0Ii0JP0LF0Li0ML0OB0Q00R=0R`0S^0S_0S`0TV0Ue0Un0VQ0W40WW0WX0XW0Y:0YE0YFS2sp1X2nX2xs1Y2nY2pY2ys1i3pX'3xs02Hi3PYBS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3SLO3ACL3pX'3xs03P0'2X02Y03SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys2n'3pX'3xs03NR03PYBS2sp1X2nX2xs1Y2nY2pY2ys1i3pX'3xs03PYBS2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin3P0'2X03NRX2Y03NR03SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin3P0'2X03NRX2Y03NR03SPB3PYBS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3SLO3ACL2n'3pX'3xs03P0'3PAC2X02Y03N1'3SPB3PYBS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3SLO3ACL2n'3pX'3xs03P0'3PAC2X02Y03N1'3SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin2NB3P0'2X02Y04LENY3SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin2NB3P0'2X02Y04LENY3SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys1i3pX'3xs02Hi3P0'2X02Y03SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys2n'3pX'3xs03PYB1a1H2H0S2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin2NB3P0'2X02Y04LEN03SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYBS2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin2NB3P0'2X02Y04LEN03SPB3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys3pX'3xs03PYB1a2HoS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3SLO3ACL3DHI3pX'3xs03P0'2X02Y03SPB3PYB1a1CS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3SLO3ACL3DHI3pX'3xs03P0'2X02Y03SPB3PYB1a2HaS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3SLO3ACL3pX'3xs03P0'2X02Y03SPB3PYB1a1B1k1R2B02B4S2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYB1a1CS1L2HI3HLS2sp1h2lo1X2nX2xs1Y2nY2pY2ys3SLO4HTOP2n'3pX'3xs03P0'2X02Y03SPB3PYB1a2NO2H0S1L2HI3HLS2sp1h2lo1X2nX2xs1Y2nY2pY2ys3SLO3ACL4HTOP2n'3pX'3xs03P0'3PAC2X02Y03N1'3SPB3PYB1a2NO1HS1L2sp1X2nX2xs1Y2nY2pY2ys2n'3pX'3xs03P0'2X02Y03SPB3PYB1a2Ha1H2H0S2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin2NB3P0'2X02Y04LENY3N1'3SPB3PY03PYBS2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin2NB3P0'2X02Y04LENY3N1'3SPB3PY03PYBS2sp1X2nX2xs1Y2nY2pY2ys1i2n'3pX'3xs02Hi3Hin2NB3P0'2X02Y03SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys1i3pX'3xs03PYB1kS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2n'3pX'3xs02Hi3Hin2TR3SY12SX3P0'3PAC2X03YAL2Y03SXY4LEN03N1'4PAL'3SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYBS2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYBS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2n'3pX'3xs02Hi3Hin2TR3SY12SX3P0'3PAC3XAL2X02Y03SXY4LEN03N1'4PAL'3SPB3PYBS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2n'3pX'3xs02Hi3Hin2TR3SY12SX3P0'3PAC3XAL2X03YAL2Y03SPB3PYB3x141HS1L2sp2lo1X2nX2xs1Y2nY2pY2ys3ACL1i2n'3pX'3xs02Hi3Hin2NB3P0'3PAC2X02Y03SPB3PYBS2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYBS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3SLO3pX'3xs03P0'2X02Y03SPB3PYBSFS2sp1X2nX2xs1Y2nY2pY2ys1i3pX'3xs02Hi3P0'2X02Y03SPB3PYBS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3SLO3ACL1i2n'3pX'3xs03Hin3P0'3PAC2X02Y03SPB3PYBS2nY1i2HiS2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYBS2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYBS2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYBFS2sp1X2nX2xs1Y2nY2pY2ys1i3pX'3xs02Hi3P0'2X02Y04LENY3SPB3PY03PYBS2sp1X2nX2xs1Y2nY2pY2ys3pX'3xs03PYBS1i2n'1E2I1F". (* [comment removed for export] *)
  Lemma final_walk : forall (i n' pX' : Z) (xs0 : list word) (mc : mem) (moc : Model) (hc : HST usegs L HI) (LBc : list blk)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs1 xs2 xs3 xs4 : word),
    let dXc : mpd := mkMPD X sgY n' pX' xs0 padX LHeap in
    1 <= i <= nY -> i <= n' -> nX <= n' <= Z.max nX nY ->
    n' = nX \/ (n' = i /\ trim_i ys i) -> zeros_above ys i ->
    (forall (k : nat) (w : word), (Z.to_nat i <= k)%nat -> nth_error xs0 k = Some w -> w = Z_to_bv 64 0) ->
    HEAP usegs L HI hc LBc mc moc -> heap_top usegs L HI hc = heap_top usegs L HI h -> mo_frame mo moc ->
    mpd_at usegs mc LBc dXc -> mpd_out LB dX LBc dXc ->
    (forall b : blk, In b (mpd_blk dXc) -> In b (mpd_blk dX) \/ ~ In b LB) ->
    rw_cells usegs mc Y (mpi_cells pY (Z_to_bv 64 sgY) nY padY) -> bytes_at usegs mc pY (u32s ys) ->
    Y + 16 <= pX' \/ pX' + 4 * n' <= Y -> pY + 4 * nY <= pX' \/ pX' + 4 * n' <= pY ->
    X + 16 <= pX' \/ pX' + 4 * n' <= X -> 0 < pX' -> pX' + 4 * n' <= @alloc_ceiling L ->
    heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m mc -> statics_ok usegs L mc -> mem_inv usegs mc ->
    stk usegs mc lo (bv_unsigned sp + -48) -> rw_cells usegs mc (bv_unsigned sp + -48) (FRAME8 s4) ->
    a0 = Z_to_bv 64 pX' ->
    aevtM usegs moc POST (MS (mkR xs1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (4 * i)) xs2 a0 a1 a2 a3 a4 a5 a6 a7
      xs3 (Z_to_bv 64 Y) xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1f7c4) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xs4. intros dXc Hi Hin NB TR ZY ZX HHc HTc MFc MAc OUTc FRc CHY PBY SY1 SY2 SX P0' PAC PXc SOKc MIc STc FRM ->.
    flat constr:(facts) 14%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY XS.
    flat constr:(CSEP) 6%nat. intros C1 C2 C3 C4 C5 _. cbn [dX dY md_addr md_own md_p md_n] in C1, C2, C3, C4, C5.
    pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MKc. flat constr:((heap_blocks _ _ HI _ _ _ _ HHc)) 2%nat. intros HBRc HAPc.
    flat constr:(MAc) 2%nat. intros FLt5 _. flat constr:(FLt5) 2%nat. flclear FLt5. intros CHX FLt6. flat constr:(FLt6) 5%nat. flclear FLt6. intros _ _ LEN0 NR0 OWN0. cbn [dXc md_addr md_sg md_n md_p md_limbs md_pad md_own] in CHX, LEN0, NR0, OWN0.
    flat constr:(OWN0) 4%nat. flclear OWN0. intros N1' PIN' PAL' PX0. unfold mpi_cells in CHX, CHY. unfold MPI_MAX_LIMBS in NR0.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(PBY) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (pX', pX' + 4 * n')] mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    pose proof (conj HHc I) as HHc0. pose proof (conj SOKc I) as SOKc0.
    assert (PY4 : pY mod 4 = 0).
    { flat constr:(MAY) 2%nat. intros FLtA _. flat constr:(FLtA) 2%nat. flclear FLtA. intros _ FLtB. flat constr:(FLtB) 5%nat. flclear FLtB. intros _ _ LY _ OY.
      cbn [dY md_own md_n md_p md_limbs] in OY, LY.
      destruct ownY; [destruct OY as [_ N0]; exfalso; dlia| destruct OY as (_ & _ & PALY & _); dlia| destruct OY as (_ & PALY & _); exact PALY]. }
    zstep. zstep. zstep. land_zero_any. zstep. if_false. zstep. zstep.
    (* [comment removed for export] *)
    rewrite <- (firstn_skipn (Z.to_nat i) xs0) in PX0. apply u32arr_app in PX0. flat constr:(PX0) 2%nat. flclear PX0. intros PXA PXB.
    rewrite firstn_length_le in PXB by dlia. apply u32arr_cells in PXA. rewrite firstn_length_le in PXA by dlia.
    pose proof PBY as PBY'. rewrite <- (firstn_skipn (Z.to_nat i) ys) in PBY'. rewrite u32s_app in PBY'. apply bytes_at_app in PBY'. flat constr:(PBY') 2%nat. flclear PBY'. intros PBA _.
    pose proof U_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    eapply aevtM_cut_evt; [ exact MKc | eapply SPc with (src := u32s (firstn (Z.to_nat i) ys)); rewrite ?unsigned_lit by dlia;
      [ exact PBA | rewrite u32s_length, firstn_length_le by dlia; dlia | replace (Z.to_nat (4 * i)) with (4 * Z.to_nat i)%nat by dlia; exact PXA | generalize SY2; dlia | exact MIc ] | ].
    clear SPc PBA. unfold memcpy_post. rewrite !unsigned_lit by dlia. post_call usegs mc.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : rw_cells usegs m3 pX' _ |- _ => rename H into PXA3 end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => match goal with H : stk usegs mx _ _ |- _ => release_frame FRM H (bv_unsigned sp) end end.
    zstep.
    flat constr:(HHc0) 2%nat. flclear HHc0. intros HHc0 _. flat constr:(SOKc0) 2%nat. flclear SOKc0. intros SOKc0 _.
    match goal with H : u32arr usegs m3 _ (skipn _ xs0) |- _ => rename H into PXB3 end.
    apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists hc, LBc.
    exists (mkMPD X sgY n' pX' (firstn (Z.to_nat i) ys ++ skipn (Z.to_nat i) xs0) padX LHeap), 0.
    split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MFc|]. split; [exact HTc|].
    split. { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HHc0| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. rewrite HTc.
      destruct (Z.le_gt_cases pX' a); [destruct (Z.lt_ge_cases a (pX' + 4 * n')); [right; right; exists (pX', 4 * n'); split; [exact PIN'| cbn; dlia] |]|]; left; dlia. }
    split. { split; [| cbn; exact SGY]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CHX|]. split; [exact XAL|]. split; [exact X0|].
      split; [rewrite length_app, firstn_length_le, length_skipn by dlia; dlia|]. split; [unfold MPI_MAX_LIMBS; dlia|].
      split; [exact N1'|]. split; [exact PIN'|]. split; [exact PAL'|].
      apply u32arr_app. split; [eapply u32arr_of_cells; [exact PXA3| reflexivity]|].
      rewrite firstn_length_le by dlia. exact PXB3. }
    split; [eapply mpd_out_ext; [exact OUTc| reflexivity| cbn; discriminate| reflexivity]|].
    split. { eapply heap_presx_trans; [exact PXc|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn. split; [| split; [| exact I]].
      - flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros HBR _.
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia].
      - refine (new_limbs_apart usegs L HI hc LB LBc mc mc moc (bv_unsigned sp) dX dXc a HHc MAc OUTc FRc ltac:(dlia) (proj1 DIMG) (proj2 DIMG) Hc _ eq_refl).
        intros HOX. unfold mpd_ivs in Ho. cbn [dX md_own md_addr md_p md_n] in Ho, HOX |- *. rewrite HOX in Ho. cbn in Ho. dlia. }
    split. { eapply statics_ok_munch; [exact SOKc0| exact MU|]. intros a Ha NW. cbn. split; [dlia|]. split; [| exact I].
      flat constr:((proj1 (Forall_forall _ _) HBRc _ PIN')) 5%nat. intros _ _ _ _ B5. cbn in B5. destruct DIMG; generalize B5; dlia. }
    unfold copy_Rx, copy_R. cbn [dX dY md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk mpd_val].
    split.
    { split. { left. split; [reflexivity|]. split; [| cbn [md_n dX dY]; exact NB]. unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_app.
        rewrite (limbs_val_zeros (skipn (Z.to_nat i) xs0)).
        2: { intros k w Hk. rewrite nth_error_skipn in Hk. rewrite (ZX (Z.to_nat i + k)%nat w ltac:(dlia) Hk). reflexivity. }
        rewrite limbs_val_firstn; [rewrite Z.mul_0_r, Z.add_0_r; reflexivity| dlia| exact ZY]. }
      split; [reflexivity|]. split; [reflexivity|]. exact FRc. }
    intros _. unfold copy_trim, mpd_abs. cbn [md_n md_limbs dX dY].
    destruct TR as [E|[E TI]]; [left; exact E|]. right. destruct TI as [I1|(w & Hw & NZ)]; [left; clear - E I1; lia| right].
    pose proof (limbs_val_nth_lower ys (Z.to_nat (i - 1)) w Hw NZ) as LO. rewrite Z2Nat.id in LO by (clear - Hi; lia). rewrite E. exact LO.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@D12996442114.160D1651773129.155 D17796584092.135D17798748044.155D17798814096.159D17991835629.155D17995963162.153D18420161661.155D18454081967.155D19615678210.155D20664094210.134D20903534416.155D2111289696.155 D22012528888.153D2549732723.155 D26153483537.159D28226776187.140D28226791445.138D41411663771.134D41856321569.155D42207609664.140D44396825856.128D47955312128.128D52101704109.162D52101720239.160D52101802538.168D53516927417.138D54288481622.134D54391985784.160D54398282304.159D58835970830.155D59308567928.140D59982979476.140D60901887829.138D60901935931.140D631512231.155  D64027496726.155D66253982974.135D67481704124.155D7005244449.155 D8927508880.128 L11801586693.152L14278493136.152L21313358653.126L22700267513.151L23100341967.127L23100341967.143L34381262068.152L40601571469.152L44484923210.152L45210610932.151L64707994401.0  L66265911915.126L67052556429.149R22706564033.15900000T01501n02g03e04E05705d05e05f06@06A06B07>07k08J09R0:Z0;20;f0<S0=20=Q0>Q0>o0@50@O0@l0B50CG0CH0D80E00Eh0F`0Fa0Fb0GO0H?0H@0Hh0If0Ig0K20L<0LT0Ln0Lo0NT0OJ0Pj0Pk0Qa0RN0SaS2sp1X2nX2pX2xs1Y2pY2ys1i3PYB1a1H2H0S2sp1X2nX2pX2xs1Y2pY2ys1i3NRX3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X04LENX2Y02P03SPB3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X04LENX2Y02P03SPB3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X04LENX2Y02P03SPB3PYB1k2HkS2sp1X2nX2pX2xs1Y2nY2pY2ys1i3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2X02Y04LENY2P03SPB3PYBS2sp1X2pX2xs1Y2nY2pY2ys1i2Hi2X02Y02P03SPB3PYBFFS2sp1X2pX2xs1Y2pY2ys1i3PYBFFS1L3HLS2sp2lo1X2pX2xs1Y2nY2pY2ys3SLO1i2X02Y04LENY2P03SPB3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2X02Y02P03SPB3PYBS2sp1X2pX2xs1Y2pY2ys1i3PYB1k2HkS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3SLO3ACL1i2Hi3Hin2X02Y02P02P43SPB3PYBS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3SLO3ACL1i2Hi3Hin2X02Y02P02P43SPB3PYBS2sp1X2pX2xs1Y2pY2ys3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X02Y02P03SPB3PYBS2sp1X2pX2xs1Y2nY2pY2ys1i2Hi2X02Y02P03SPB3PYBS2sp1X2nX2pX2xs1Y2pY2ys3NRX3PYBS2sp1X2nX2pX2xs1Y2pY2ys3NRX3PYBS1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL3DHI1i2X02Y02P03SPB3PYB1a1CS2sp1X2pX2xs1Y2pY2ys1i3PYB1a1CS1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL1i2X02Y02P03SPB3PYB1a1B1k1R2B02B4S2sp1X2pX2xs1Y2pY2ys1i3PYBS2sp1X2nX2pX2xs1Y2pY2ys1i3PYBS1L2HI3HLS2sp1h2lo1X2nX2pX2xs1Y2pY2ys3SLO4HTOP1i2X02Y02P03SPB3PYB1a2NO2H0S1L2HI3HLS2sp1h2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL4HTOP1i2X02Y02N12P02P43SPB3PYB1a2NO1HFS2sp1X2pX2xs1Y2nY2pY2ys1i2Hi2X02Y02P03SPB3PYB2OYS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi2X04LENX2Y02P03SPB3PYB2NNS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X03NRX2Y02P03SPB3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X03NRX2Y02P03SPB3PYBFFS2sp1X2pX2xs1Y2nY2pY2ys1i2Hi2X02Y02P03SPB3PYBS2sp1X2nX2pX2xs1Y2pY2ys1i2X02Y02P03SPB3PYB2NN2LFFS2sp1X2nX2pX2xs1Y2pY2ys2X02Y02P03SPB3PYBS1L3HLS2sp2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL1i2X02Y02P02P43SPB3PYBFS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3SLO3ACL1i2Hi3Hin2X02Y02P02P43SPB3PYB2NNS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3SLO3ACL1i2Hi2X02Y02P02P43SPB3PYB3x141HS2sp1X2pX2xs1Y2pY2ys3PYBS2sp1X2pX2xs1Y2pY2ys1i3PYBFS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3XAL2X02Y04LENY3SXY2C22N13PAL2P02P43SPB3PYB2LF2XPS1L2sp2lo1X2nX2pX2xs1Y2pY2ys3ACL1i2X02Y02P02P43SPB3PYBS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi2X03YAL2Y03SXY2C22N13PAL2P02P43SPB3PYB2LF2XPSS2sp1X2pX2xs1Y2nY2pY2ys1i2Hi2X02Y04LENY2P03SPB3PY03PYBS2sp1X2nX2pX2xs1Y2pY2ys1i2X02Y02P03SPB3PYB2LFS1L4DIMG2sp1X2nX2pX2xs1Y2nY2pY2ys3NEQ1i2Hi3XAL2X03YAL2Y02C22N12P02P53SPB3PYB2XP1a1H". (* [comment removed for export] *)
  Lemma memset_path : forall (i : Z) (mc : mem) (t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 xs1 : word),
    1 <= i <= nY -> i <= nX -> ownX = LHeap -> zeros_above ys i ->
    rw_cells usegs mc X (mpi_cells pX (Z_to_bv 64 sgY) nX padX) -> u32arr usegs mc pX xs ->
    rw_cells usegs mc Y (mpi_cells pY (Z_to_bv 64 sgY) nY padY) -> bytes_at usegs mc pY (u32s ys) ->
    HEAP usegs L HI h LB mc mo -> heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m mc ->
    statics_ok usegs L mc -> mem_inv usegs mc ->
    stk usegs mc lo (bv_unsigned sp + -48) -> rw_cells usegs mc (bv_unsigned sp + -48) (FRAME8 s4) ->
    aevtM usegs mo POST (MS (mkR xs1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (4 * i)) (Z_to_bv 64 i)
      (Z_to_bv 64 X) (Z_to_bv 64 Y) a2 a3 (zx16 (Z_to_bv 64 nX)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x1f6e8) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xs1. intros Hi Hin EO ZY CHX PX CHY PBY HHc PXc SOKc MIc STc FRM.
    flat constr:(facts) 14%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY XS.
    flat constr:(CSEP) 6%nat. intros C1 C2 C3 C4 C5 _. cbn [dX dY md_addr md_own md_p md_n] in C1, C2, C3, C4, C5.
    pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MKc. flat constr:((heap_blocks _ _ HI _ _ _ _ HHc)) 2%nat. intros HBR HAP.
    flat constr:(MAX) 2%nat. intros FLt7 _. flat constr:(FLt7) 2%nat. flclear FLt7. intros _ FLt8. flat constr:(FLt8) 5%nat. flclear FLt8. intros _ _ _ _ OWN0. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OWN0. rewrite EO in OWN0.
    flat constr:(OWN0) 4%nat. flclear OWN0. intros N1 PIN PAL _. specialize (C2 EO).
    flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(PBY) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB.
    assert (NN : bv_unsigned (zx16 (Z_to_bv 64 nX)) = nX) by (unfold zx16; rewrite !unsigned_lit by dlia; apply Z.mod_small; dlia).
    unfold mpi_cells in CHX, CHY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (pX, pX + 4 * nX)] mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    pose proof (conj HHc I) as HHc0. pose proof (conj SOKc I) as SOKc0. pose proof (conj PBY I) as PBYc.
    zstep. zstep. try replace (4 * i + pX) with (pX + 4 * i) by dlia.
    zstep; if_false_x. zstep; if_false_x. zstep; if_false_x.
    zstep. zstep. rewrite ?NN. zstep. zstep. zstep. zstep.
    replace ((nX - i) ≪ 2) with (4 * (nX - i)) by (rewrite Z.shiftl_mul_pow2 by dlia; dlia).
    (* [comment removed for export] *)
    rewrite <- (firstn_skipn (Z.to_nat i) xs) in PX. apply u32arr_app in PX. flat constr:(PX) 2%nat. flclear PX. intros PXA PXB.
    rewrite firstn_length_le in PXB by dlia. apply u32arr_cells in PXB. rewrite length_skipn in PXB.
    assert (LF : Z.of_nat (length (firstn (Z.to_nat i) xs)) = i) by (rewrite firstn_length_le; dlia).
    flat constr:(XW) 3%nat. intros _ _ XP. cbn [dX md_addr md_own md_p md_n] in XP. specialize (XP EO).
    assert (OYN : ownY <> LNull).
    { intros C. flat constr:(MAY) 2%nat. intros FLt9 _. flat constr:(FLt9) 2%nat. flclear FLt9. intros _ FLt10. flat constr:(FLt10) 5%nat. flclear FLt10. intros _ _ LY _ OY. cbn [dY md_own md_n md_p md_limbs] in OY, LY. rewrite C in OY. dlia. }
    specialize (C1 OYN). specialize (C5 OYN).
    assert (PXY : pX + 4 * nX <= pY \/ pY + 4 * nY <= pX).
    { destruct C3 as [E|[C|[C|C]]]; [exfalso; apply NEQ; injection E; auto| exfalso; exact (C EO)| exfalso; exact (OYN C) | exact C]. }
    zstep.
    pose proof U_memset_spec as SPs. unfold memset_stmt in SPs.
    eapply aevtM_cut_evt; [ exact MKc | eapply SPs; rewrite ?unsigned_lit by dlia;
      [ replace (Z.to_nat (4 * (nX - i))) with (4 * (length xs - Z.to_nat i))%nat by dlia; replace (pX + 4 * i) with (pX + 4 * Z.of_nat (Z.to_nat i)) by dlia; exact PXB | assumption ] | ].
    clear SPs PXB. unfold memset_post. rewrite !unsigned_lit by dlia. post_call usegs mc.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : rw_cells usegs m3 (pX + 4 * i) _ |- _ => rename H into PZ end.
    flat constr:(PBYc) 2%nat. flclear PBYc. intros PBYc _. try clear PBY.
    assert (PBY3 : bytes_at usegs m3 pY (u32s ys)).
    { eapply bytes_at_transport; [exact PBYc| exact MU|]. rewrite u32s_length. cbn. split; [generalize C5; dlia|]. split; [generalize PXY; dlia| exact I]. }
    zstep. zstep.
    flat constr:(HHc0) 2%nat. flclear HHc0. intros HHc0 _. flat constr:(SOKc0) 2%nat. flclear SOKc0. intros SOKc0 _.
    assert (TR : nX = nX \/ (nX = i /\ trim_i ys i)) by (left; reflexivity).
    eapply (final_walk i nX pX (firstn (Z.to_nat i) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nX - i))) m3 mo h LB);
      try eassumption; try reflexivity; try dlia.
    - intros k w Hk HN. rewrite nth_error_app2 in HN by (rewrite firstn_length_le by dlia; dlia).
      apply nth_error_In in HN. apply repeat_spec in HN. exact HN.
    - eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HHc0| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO.
      destruct (Z.le_gt_cases pX a); [destruct (Z.lt_ge_cases a (pX + 4 * nX)); [right; right; exists (pX, 4 * nX); split; [exact PIN| cbn; dlia] |]|]; left; dlia.
    - apply mo_frame_refl.
    - split; [| cbn; exact SGY]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CHX|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite length_app, firstn_length_le, repeat_length by dlia; dlia|].
      split; [unfold MPI_MAX_LIMBS; dlia|]. split; [exact N1|]. split; [exact PIN|]. split; [exact PAL|].
      apply u32arr_app. split; [exact PXA|]. rewrite firstn_length_le by dlia. replace (pX + 4 * Z.of_nat (Z.to_nat i)) with (pX + 4 * i) by dlia.
      eapply u32arr_of_cells; [exact PZ|]. rewrite u32s_repeat0. cbn [Z.modulo]. f_equal. dlia.
    - apply mpd_out_same_blocks; [reflexivity| cbn; discriminate| unfold dX; cbn [mpd_blk md_own md_p md_n]; rewrite EO; reflexivity].
    - unfold dX. cbn [mpd_blk md_own md_p md_n]. rewrite EO. intros b Hb; left; exact Hb.
    - generalize PXY; dlia.
    - eapply heap_presx_trans; [exact PXc|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. unfold mpd_ivs in Ho. cbn [dX md_addr md_own md_p md_n] in Ho. rewrite EO in Ho. cbn in Ho |- *.
      flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _. split; [| split; [exact O2| exact I]].
      destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?D10142048111.82D11998961097.81D12457787866.79D19628598561.82D30459643022.82D32604240303.81D5106302096.79 D5108351020.83 D66345859244.8100000A00O00g01`02S03F03W04L05ES2sp2nY2pY2ys3PBBS2sp2pY2ys3PBBS2sp2nY2pY2ys1A1k3HnY2N0S1L3HLS2sp2lo2nY2pY2ys3SLO3ACL1A1k3HnY2Hk2A02A42LY2PP3PBBS1L3HLS2sp2lo2nY2pY2ys3SLO3ACL1A1k3HnY2Hk2A02A43PBBS1L3HLS2sp2lo2nY2pY2ys3SLO3ACL1A1k3HnY2Hk2A02A43PBBS2sp2nY2pY2ys1A1kS1L3HLS2sp2lo2nY2pY2ys3SLO3ACL1A1k2Hk2A02A43PBB2R12R2S1L3HLS2sp2lo2nY2pY2ys3SLO3ACL1A1k3HnY2Hk2A02A42LY2PP3PBB". (* [comment removed for export] *)
  Lemma ylimbs_apart_fresh : ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "PA,$3.Pk,$3.P,(58.VnY,+1.)P,(1:.=R2.)P,(59.VL,R4.R3.)P,PB,$3.Pj,$3.P,(12.(5:.$3.$3.)(5;.$3.$3.R2.R1.)VLB,)(1.(5.(16.R8.R7.)R3.)(5.(16.R3.R2.)R8.))(1.(5.(16.VpY,(17.+4.VnY,))R6.)(5.(16.R6.R5.)VpY,))")
(* [comment removed for export] *).
  Proof.
    intros A k HnY Hk (A0 & _ & Ak & A4 & A5) HAPA.
    flat constr:(MAY) 2%nat. intros FLt11 _. flat constr:(FLt11) 2%nat. flclear FLt11. intros _ FLt12. flat constr:(FLt12) 5%nat. flclear FLt12. intros _ _ LY NY OY. cbn [dY md_addr md_sg md_n md_p md_limbs md_pad md_own] in LY, NY, OY.
    destruct ownY.
    - flat constr:(OY) 2%nat. flclear OY. intros _ N0. dlia.
    - flat constr:(OY) 4%nat. flclear OY. intros _ PIN _ _. generalize (HAPA _ _ PIN); dlia.
    - flat constr:(OY) 5%nat. flclear OY. intros _ _ PP PB RO. flat constr:(PB) 3%nat. flclear PB. intros _ PBB _. rewrite u32s_length in PBB.
      pose proof (ROIMG pY ltac:(dlia) ltac:(replace pY with (pY + 0) by dlia; apply RO; dlia)) as R1.
      pose proof (ROIMG (pY + 4 * nY - 1) ltac:(dlia) ltac:(replace (pY + 4 * nY - 1) with (pY + (4 * nY - 1)) by dlia; apply RO; dlia)) as R2. generalize A5; dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02j0@D10364569636.134D10375653139.156D10917811501.173D11566266720.222D12996432337.160D13796136073.163D13798216867.162D13798233251.163D14125161660.225D14788764387.134D14791076275.196D14792959895.152D14792959895.215D15226509510.222D16251155753.160D16251155753.226D1651690435.152 D1663011337.175 D16753695927.161D16753695927.229D17315745945.196D17989670858.224D18728330852.163D19613119012.173D19646181967.225D19652550953.224D19652659704.208D21026673542.196D21028674851.175D22012527110.223D22027029894.226D22027206803.158D22719078771.154D23931266085.164D24010168020.208D25188048531.154D25514719242.222D25620244961.224D2780666493.154 D28812073579.181D28818382827.180D29227127268.223D29242154596.226D35202291097.173D35740685127.176D36052405171.154D36249316244.196D36249740612.181D36457795155.173D36472342481.208D38221178462.196D39409830041.224D39409836362.177D39409836362.182D39409836362.211D40829866043.134D41415938670.175D41418005707.196D43646919618.208D44187047108.134D44399052946.130D46288017929.183D46288018056.184D46288024153.224D4632852750.222 D47957277586.130D49643072906.154D51024030278.212D5112593925.223 D51273449520.134D52101704109.179D52101704109.227D52101704109.232D52101720110.177D52101720239.225D52101720239.230D52101733636.176D52101733636.211D52101802538.185D52101802538.238D52101802921.229D52463926887.180D52478557159.181D54391985784.177D54391985784.182D54391985784.211D54391986042.184D54391986171.183D54398102733.178D54398102733.183D54398102733.208D54398282304.176D54398282304.210D57751154346.228D57751203752.227D58315410958.196D58734142043.173D59308562897.5  D59308567928.129D59308632307.169D59308632307.175D59308633593.165D59315317366.165D59315317366.166D60395741555.154D60634946379.222D60668600941.174D60675325052.168D60675325052.169D60675325052.226D60679058686.227D60681178462.168D60681178462.169D60681227356.228D629346689.173  D63525934856.134D64831911713.173D64838598307.208D65220328362.173D65500066615.162D65500082999.163D6624980440.209 D66254111944.173D66952896442.181D6739948970.225 D67494220312.208D67919376067.173D68341485675.180D68343600619.181D68344027963.196D68418654899.222D807982321.196  D8838691126.221 D8895070966.211 D8929475586.130 D9072270588.154 D9213743235.208 D9223837953.173 L11741095640.144L1227220751.192 L12292857614.190L12292857614.193L13972576688.168L13972576688.169L22700267513.192L23100341967.153L23100341967.159L23100341967.180L23100341967.205L23900635781.192L26924648792.144L27907150090.152L28767740167.167L28767740167.168L28767740167.214L28767740167.215L28814040852.152L38541400496.167L38541400496.168L38541400496.214L38541400496.215L40238812268.193L43654564952.144L44046804688.169L44046804688.170L44046804688.220L44046804688.221L44154063980.190L44154063980.192L49578233423.159L49578233423.205L51709126206.151L52476066706.156L52476066706.158L58165767448.220L58165767448.221L5848377239.193 L59269710469.193L59314955108.1  L59499841752.144L61263218231.193L62454858145.0  L7510805464.144 R2113957450.154 R22706564033.200R31957511749.15400000M00b00c01Y02H03403`04L05@06407307g08f09g0:Q0;H0;d0<h0=R0>I0>J0??0@70@80@`0A?0A]0B:0BW0CV0DU0EG0EH0Ea0FS0Fh0GE0Gd0H90IC0JM0K?0L10L20Ld0MT0NL0OD0P40Pj0QM0Ql0RJ0Rk0SL0Sa0T;0TU0UM0V80VT0W80W\0XW0YX0Z40ZI0[L0\@0\^0]^0^g0`00`K0`i0aG0bE0cI0dL0eU0f[0g_0hc0ii0kS0lb0n60o]10W11W12W13\14j15^16[17X17Y17g18]19M19m1:J1;O1<G1<H1<e1=Q1>A1?11?e1@a1AT1BG1CG1CH1Ci1DH1Dj1EV1Em1FD1GD1H01Hc1Ig1J]1J^1K^1L^1M^1NQ1OT1On1Pa1QC1QD1R=1S31SH1SI1Sh1To1Vf1XN1ZP1Zg1[>1[X1\21^31^H1_41`a1bN1dQ1fT1gT1h>1hj1iW1jF1lO1ld1n_20S22k25C27627727N27h28=28g29k2<G2>_2>`2>a2>d2?92@82@92@N2@c2Bd2CGS2sp1X2xs1Y2nY2pY2ys1i2Hi3PYBS2sp1X2xs1Y2pY2ys3PYBFS2sp1X2nX2pX2xs1Y2pY2ys1i3Hin2X02Y03SPB3PYB1A2A02N12P0S2sp1X2nX2pX2xs1Y2pY2ys2X04LENX2Y03SPB3PYB1a2HaS2sp1X2xs1Y2nY2pY2ys1i2Hi2X02Y03SPB3PYB1A2A0S2sp1X2xs1Y2nY2pY2ys1i2Hi2X02Y03SPB3PYB1A2A0S2sp1X2xs1Y2nY2pY2ys1i2Hi2X02Y03SPB3PYB1A2A0S2sp2lo1X2pX2xs1Y2pY2ys2X02Y03SPB3PYB1A2A02P01a2Ha1CS1L3HLS2sp2lo1X2xs1Y2pY2ys3SLO3ACL2X02Y03ACP3SPB3PYBS1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL2X02Y03ACP3SPB3PYB1A2A02P0S1L3HLS2sp2lo1X2xs1Y2pY2ys3SLO3ACL2X02Y03ACP3SPB3PYBS1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL2X02Y03ACP3SPB3PYB1A2A02P0S1L3HLS2sp2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL2X02Y03SPB3PYB1A2A02P02P4S2sp1X2xs1Y2nY2pY2ys2X02Y03SPB3PYB2LY1a2HaS2sp1X2pX2xs1Y2nY2pY2ys2X02Y04LENY3SPB3PYB1A2A02P01a2HaS2sp1X2nX2xs1Y2pY2ys3NRX3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X04LENX2Y03SPB3PYB2NN1A2A02N12P0S2sp1X2xs1Y2nY2pY2ys2X02Y03SPB3PYB2LY1j2HjS2sp1X2pX2xs1Y2nY2pY2ys1A2X02Y04LENY3SPB3PYB2A02P01j2HjFS2sp1X2nX2pX2xs1Y2nY2pY2ys2X02Y04LENY3SPB3PYB1A2A02P0S2sp1X2nX2xs1Y2nY2pY2ys1i2Hi3Hin2X04LENX2Y03SPB3PYB1A2A0FS1L2HI2sp1h1X2pX2xs1Y2pY2ys3PYB1A1a2Ha1CS2sp1X2pX2xs1Y2pY2ys3PYB1A1a2HaS2sp1X2pX2xs1Y2pY2ys3PYB1A1a1CS2sp1X2nX2pX2xs1Y2pY2ys3PYB1AS2sp1X2nX2pX2xs1Y2pY2ys3PYB1AS1L3HLS2sp2lo1X2pX2xs1Y2nY2pY2ys3SLO2X02Y04LENY3SPB3PYB1A2A02P0S1L3HLS2sp2lo1X2pX2xs1Y2nY2pY2ys3SLO1A2X02Y04LENY3SPB3PYB2A02P0S1L3HLS2sp2lo1X2xs1Y2nY2pY2ys3SLO2X02Y03SPB3PYB2LYFS2sp1X2xs1Y2pY2ys1i3PYB1AS2sp1X2nX2pX2xs1Y2pY2ys1A2X04LENX2Y03SPB3PYB2A02P0S2sp1X2xs1Y2pY2ys3PYBS2sp1X2nX2pX2xs1Y2pY2ys3PYB1AS2sp1X2pX2xs1Y2pY2ys3PYB1A1a2HaS2sp1X2xs1Y2pY2ys3PYBS1L3HLS2sp2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL1i3Hin2X02Y03SPB3PYB1A2A02A42N12P0S1L3HLS2sp2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL1i3Hin2X02Y03SPB3PYB1A2A02A42N12P0S2sp1X2pX2xs1Y2nY2pY2ys2X02Y04LENY3SPB3PYB1A2A02P0S2sp1X2pX2xs1Y2nY2pY2ys1A2X02Y04LENY3SPB3PYB2A02P0FS2sp1X2nX2pX2xs1Y2pY2ys2X04LENX2Y03SPB3PYB1A2A02P0S1L3HLS2sp2lo1X2xs1Y2pY2ys3SLO3ACL2X02Y03SPB3PYBS2sp1X2nX2pX2xs1Y2pY2ys2X04LENX2Y03SPB3PYB2NN1A2A02N12P0S2sp1X2nX2pX2xs1Y2pY2ys2X04LENX2Y03SPB3PYB2NN1A2A02N12P0S2sp1X2xs1Y2nY2pY2ys1i2Hi1A2X02Y03NRY3SPB3PYB2A0S2sp1X2pX2xs1Y2nY2pY2ys1i2Hi1A2X02Y03NRY3SPB3PYB2A02P0S1L2sp2lo1X2pX2xs1Y2pY2ys3SLO3PYB1AS2sp1X2pX2xs1Y2pY2ys3PYB1A1a2HaS2sp1X2xs1Y2pY2ys1A3PYB1a1H2H0S2sp1X2pX2xs1Y2pY2ys3PYB1A1a1H2H0S2sp1X2pX2xs1Y2pY2ys1A3PYB1a1H2H0S2sp1X2xs1Y2pY2ys3PYBS2sp1X2pX2xs1Y2pY2ys3PYB1AS2sp1X2pX2xs1Y2pY2ys3PYB1AS2sp1X2nX2pX2xs1Y2pY2ys1i3Hin1A2X04LENX2Y03SPB3PYB2A02P0S2sp1X2xs1Y2nY2pY2ys1i2Hi2X02Y03NRY3SPB3PYBS2sp1X2nX2xs1Y2pY2ys3NRX3PYBS2sp1X2pX2xs1Y2pY2ys1i3PYB1A1a2H02H1S2sp1X2pX2xs1Y2pY2ys1i3PYB1A1a2H12H2S2sp1X2nX2pX2xs1Y2pY2ys1i3Hin2X02Y03SPB3PYB1A2A02N12P01a2HaS2sp2LB1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X02Y03SPB3PYB1A2A02N12P01eS2sp1X2nX2xs1Y2pY2ys3NRX3PYBS2sp1X2xs1Y2pY2ys3PYBS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin1A2X04LENX2Y03SPB3PYB2A02P01k2HkS2sp1X2pX2xs1Y2nY2pY2ys1i2X02Y04LENY3SPB3PYB1A2A02P0S1L2sp2lo1X2xs1Y2pY2ys3SLO3PYBS1L3HLS2sp2lo1X2xs1Y2pY2ys3SLO3ACL3DHI1A2X02Y03SPB3PYB2A02KZ1a1CS1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL3DHI2X02Y03SPB3PYB1A2A02KZ2P02KP1a1CS1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL3DHI1A2X02Y03SPB3PYB2A02KZ2P02KP1a1CS2sp1X2xs1Y2pY2ys1A3PYB1a1CS2sp1X2pX2xs1Y2pY2ys3PYB1A1a1CS2sp1X2pX2xs1Y2pY2ys1A3PYB1a1CS1L3HLS2sp2lo1X2xs1Y2pY2ys3SLO3ACL3DHI1A2X02Y03SPB3PYB2A01a2HaS1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL3DHI1A2X02Y03SPB3PYB2A02P01a2HaS1L3HLS2sp2lo1X2xs1Y2pY2ys3SLO3ACL1A2X02Y03SPB3PYB2A01a1B1k1R2B02B4S1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL1A2X02Y03SPB3PYB2A02P01a1B1k1R2B02B4S1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL2X02Y03SPB3PYB1A2A02P01a1B1k1R2B4S1L3HLS2sp2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL2X02Y03SPB3PYB1A2A02N12P02P4S1L3HLS2sp2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL2X02Y03SPB3PYB1A2A02N12P02P4S1L2HI3HLS2sp1h2lo1X2xs1Y2pY2ys3SLO4HTOP1A2X02Y03SPB3PYB2A02KZ1a2NO2H0S1L2HI3HLS2sp1h2lo1X2nX2pX2xs1Y2nY2pY2ys3SLO3ACL4HTOP1i2Hi3Hin2X02Y03SPB3PYB1A2A02A42KZ2N12P02KP1a2NO1H2H0S1L2HI3HLS2sp1h2lo1X2pX2xs1Y2pY2ys3SLO4HTOP1A2X02Y03SPB3PYB2A02KZ2P02KP1a2NO2H0S1L2HI3HLS2sp1h2lo1X2pX2xs1Y2pY2ys3SLO4HTOP1i2X02Y03SPB3PYB1A2A02KZ2P02KP1a2NO2H02H2S1L2HI3HLS2sp1h2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL4HTOP1i3Hin2X02Y03SPB3PYB1A2A02A42KZ2N12P02KP1a2NO2H02H11HS1L2HI3HLS2sp1h2lo1X2xs1Y2pY2ys3SLO1A2X02Y03SPB3PYB2A01a1CS1L2HI3HLS2sp1h2lo1X2pX2xs1Y2pY2ys3SLO2X02Y03SPB3PYB1A2A02P01a1CS1L2HI3HLS2sp1h2lo1X2pX2xs1Y2pY2ys3SLO1A2X02Y03SPB3PYB2A02P01a1CS1L2HI3HLS2sp1h2lo1X2xs1Y2pY2ys3SLO4HTOP1A2X02Y03SPB3PYB2A02KZ1a2NO1HS1L2HI3HLS2sp1h2lo1X2pX2xs1Y2pY2ys3SLO4HTOP1A2X02Y03SPB3PYB2A02KZ2P02KP1a2NO1HS2sp1X2pX2xs1Y2pY2ys1i2X02Y03SPB3PYB1A2A02P01a1B1k1RS1L2sp1X2pX2xs1Y2pY2ys1i2X02Y03SPB3PYB1A2A02KZ2P02KP1a1C1H2H0S1L2HI2sp1h1X2pX2xs1Y2pY2ys4HTOP2X02Y03SPB3PYB2h23HT21A2A02P0FS2nX2pX1a1R2O2S2sp1X2nX2xs1Y2nY2pY2ys1i2Hi3Hin2X04LENX2Y03SPB3PYB2OYS2sp1X2pX2xs1Y2pY2ys2X02Y03SPB3PYB1A2A02KZ2P02KPS2sp1X2pX2xs1Y2pY2ys3PYB1A2P02KPS2sp1X2xs1Y2pY2ys3PYB1A2A02KZS1L2HI3HLS2sp1h2lo1X2xs1Y2pY2ys3SLO3ACL1i2X02Y03SPB3PYB1A2A02A41a1C1SS1L2sp2lo1X2xs1Y2pY2ys3ACL1i2X02Y03SPB3PYB1A2A02A41a1C1SFS2sp1X2nX2pX2xs1Y2pY2ys3PYB1AS2sp1X2xs1Y2nY2pY2ys1i2Hi1A2X02Y03SPB3PYB2A0S2sp1X2xs1Y2pY2ys1i2X02Y03SPB3PYB1A2A01a1C1B1k1RS2sp1X2xs1Y2pY2ys1i2X02Y03SPB3PYB1A2A01a1C1B1k1RS2sp1X2nX2pX2xs1Y2pY2ys2X02Y03SPB3PYB1A2A02P01a2Ha1RS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin1A2X02Y03SPB3PYB2A02N12P0S1L2sp1X2xs1Y2pY2ys1i2X02Y03SPB3PYB1A2A01a1C1D1H2H0S1L2sp1X2xs1Y2pY2ys1i2X02Y03SPB3PYB1A2A01a1C1D1H2H0S2sp1X2nX2pX2xs1Y2nY2pY2ys2X02Y04LENY3SPB3PYB1A2A02P01a2Ha2E12E2FS1L2HI2sp1h1X2xs1Y2pY2ys4HTOP3PYBS2sp1X2xs1Y2nY2pY2ys1i2Hi1A3PYBS2sp1X2pX2xs1Y2nY2pY2ys1i2Hi1A3PYBS2sp1X2xs1Y2nY2pY2ys1i2Hi1A2X02Y03SPB3PYB2A0S2sp1X2xs1Y2pY2ys3PYB1AS2sp1X2xs1Y2pY2ys3PYB1AS2sp1X3sgX2nX2pX2xs4padX1Y3sgY2pY2ys1i3Hin1A2X02Y03SPB3PYB2A02P0S2sp1X2xs1Y2nY2pY2ys1i2Hi1A2X02Y03SPB3PYB2A0S2sp1X2nX2pX2xs1Y2pY2ys1i3Hin2X02Y03SPB3PYB1A2A02P0S1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL1i2X02Y03SPB3PYB1A2A02A42P01a1CS2sp1X2nX2pX2xs1Y2pY2ys1i3Hin1A2X02Y03SPB3PYB2NN2A02P0FS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X02Y03NRY3SPB3PYB1A2A02N12P0S2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X02Y03NRY3SPB3PYB1A2A02N12P0S2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin2X02Y03NRY3SPB3PYB1A2A02N12P0S2sp1X2nX2pX2xs1Y2pY2ys1i3Hin2X02Y03SPB3PYB1A2A02P0S1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL3SPA2X02Y03ACP3SPB3PYB1A2A02P0S2sp1X2pX2xs1Y2pY2ys3PYB1AS2sp1X2nX2pX2xs1Y2pY2ys1i3Hin1A2X02Y03SPB3PYB2A02P0S2sp1X2nX2xs1Y2pY2ys2X02Y03SPB3PYBFS2sp1X2nX2pX2xs1Y2nY2pY2ys1i2Hi3Hin1A2X02Y03SPB3PYB2A02P0S2sp1X2nX2xs1Y2nY2pY2ys1i2Hi3Hin1A2X02Y03SPB3PYB2A02N0S2sp1X2xs1Y2pY2ys3PYBFS2sp1X2nX2pX2xs1Y2pY2ys1i3PYB1AS1L3HLS2sp2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL1i3Hin2X02Y03SPB3PYB1A2A02A42P0S1L3HLS2sp2lo1X2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3XAL2X02Y04LENY3SXY2XS2C12C53SPB3PYB1A2A03A162A42XA3YLA2KZ2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi1A2X02Y04LENY3SXY2XS2C12C53SPB3PYB2A02A42KZ2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin3XAL2X03YAL2Y04LENY3SPB3PYB2XP1A2A02A42XA2YA3YLA2KZ3PXY2P02P43APA2KP3x281HS2sp1X2xs1Y2pY2ys3PYB1AS2sp1X2xs1Y2pY2ys3PYB1AS2sp1X2pX2xs1Y2pY2ys3PYB1AS2sp1X2pX2xs1Y2pY2ys3PYB1AS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin2X03YAL2Y03SXY3SPB3PYB2XP2NN1A2A03A162A42XA2YA3YLA2KZ2N13PXY2P02P43APA2KPS2sp1X2xs1Y2pY2ys3PYBS1L3HLS2sp2lo1X2xs1Y2pY2ys3SLO2X02Y03SPB3PYBS1L3HLS2sp2lo1X2xs1Y2nY2pY2ys3NEQ3SLO3ACL3SPA1i2Hi3XAL2X02Y04LENY3SXY2XS2C43SPB3PYB1A2A02A42KZ2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2xs1Y2nY2pY2ys3NEQ3SLO3ACL3SPA1i2Hi1A3XAL2X02Y04LENY3SXY2XS2C43SPB3PYB2A02A42KZ2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL3SPA1i2Hi3Hin3XAL2X02Y04LENY3SXY2XS2C43SPB3PYB1A2A02A42KZ2N12P02P42KP2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL3SPA1i2Hi3Hin1A3XAL2X02Y04LENY3SXY2XS2C43SPB3PYB2A02A42KZ2N12P02P42KP2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2xs1Y2nY2pY2ys3SLO3ACL1i2Hi2X02Y03SPB3PYB1A2A02A4S2sp1X2xs1Y2pY2ys1A3SXY3PYB2HB5Ha_st5Hl_stS2sp1X2xs1Y2pY2ys1i1A3SXY3PYB2HB5Ha_st5Hl_stS2sp1X2pX2xs1Y2pY2ys1A3SXY3PYB2HB5Ha_st5Hl_stS2sp1X2pX2xs1Y2pY2ys1i1A3SXY3PYB2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin3XAL2X02Y04LENY3SXY2C13SPB3PYB2XP2NN1A2A03A162A42XA2YA3YLA2KZ2N13PXY2P02P43APA2KPS2sp1X2xs1Y2pY2ys3PYBS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin3XAL2X02Y04LENY3SXY2C13SPB3PYB1A2A03A162A42XA2YA3YLA2KZ2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin1A3XAL2X02Y04LENY3SXY3SPB3PYB2A03A162A42XA2YA2KZ2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin3XAL2X02Y04LENY3SXY2C13SPB3PYB2XP2NN1A2A03A162A42XA2YA3YLA2KZ2N13PXY2P02P43APA2KP2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin1A3XAL2X02Y04LENY3SXY2C13SPB3PYB2XP2NN2A03A162A42XA2YA3YLA2KZ2N13PXY2P02P43APA2KP2HB5Ha_st5Hl_stS2sp1X2nX2pX2xs1Y2nY2pY2ys3NEQ1i2Hi3Hin3XAL2X04LENX3YAL2Y03SPB3PYB2XP2NN1A2A03A162XA2YA3YLA2KZ2N13PAL3PXY2P03APA2KPFS2sp1X2xs1Y2pY2ys3PYB1AS2sp1X2pX2xs1Y2pY2ys3PYB1AS2sp1X2xs1Y2pY2ys3PYBS2sp1X2pX2xs1Y2pY2ys2X02Y03SPB3PYB1A2A02P0S1L3HLS2sp2lo1X2nX2pX2xs1Y2pY2ys3SLO3ACL2X02Y03SPB3PYB1A2A02N12P02P4S1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin3XAL2X02Y04LENY3SXY2C13SPB3PYB2XP2NN1A2A03A162A42XA2YA3YLA2KZ2N13PAL3PXY2P02P43APA2KP2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2pX2xs1Y2nY2pY2ys3NEQ3SLO3ACL1i2Hi3Hin1A3XAL2X02Y04LENY3SXY2C13SPB3PYB2XP2NN2A03A162A42XA2YA3YLA2KZ2N13PXY2P02P43APA2KP2HB5Ha_st5Hl_stFFS1ES2sp1X2xs1Y2pY2ys3PYBS1L2sp2lo1X2nX2pX2xs1Y2pY2ys3ACL1i3Hin2X02Y03SPB3PYB1A2A02A42P0SS2sp1X2xs1Y2pY2ys3PYBS2sp1X2xs1Y2pY2ys3PYBS1L4DIMG2sp1X2nX2pX2xs1Y2nY2pY2ys3NEQ1i2Hi3Hin3XAL2X03YAL2Y04LENY3SPB3PYB2XP1A2A03A162A52XA2YA3YLA2KZ2N13PAL3PXY2P02P53APA2KP1a1HS2sp2lo1X2xs1Y2pY2ys3NEQ3SXY2C43PYB". (* [comment removed for export] *)
  Lemma grow_path : forall (i : Z) (mc : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs1 : word),
    1 <= i <= nY -> nX < i -> zeros_above ys i -> trim_i ys i ->
    rw_cells usegs mc X (mpi_cells pX (Z_to_bv 64 sgY) nX padX) -> (ownX = LHeap -> u32arr usegs mc pX xs) ->
    rw_cells usegs mc Y (mpi_cells pY (Z_to_bv 64 sgY) nY padY) -> bytes_at usegs mc pY (u32s ys) ->
    HEAP usegs L HI h LB mc mo -> heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m mc ->
    statics_ok usegs L mc -> mem_inv usegs mc ->
    stk usegs mc lo (bv_unsigned sp + -48) -> rw_cells usegs mc (bv_unsigned sp + -48) (FRAME8 s4) ->
    aevtM usegs mo POST (MS (mkR xs1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (4 * i)) (Z_to_bv 64 i)
      (Z_to_bv 64 X) (Z_to_bv 64 Y) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-16)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x1f764) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xs1. intros Hi Hin ZY TI CHX PXH CHY PBY HHc PXc SOKc MIc STc FRM.
    assert (TR : i = nX \/ (i = i /\ trim_i ys i)) by (right; split; [reflexivity| exact TI]).
    flat constr:(facts) 14%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY XS. pose proof alloc_ceiling_pos as ACP.
    flat constr:(CSEP) 6%nat. intros C1 C2 C3 C4 C5 _. cbn [dX dY md_addr md_own md_p md_n] in C1, C2, C3, C4, C5.
    pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MKc. flat constr:((heap_blocks _ _ HI _ _ _ _ HHc)) 2%nat. intros HBR HAP. pose proof (HND _ _ _ _ HHc) as ND.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(PBY) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB.
    assert (OYN : ownY <> LNull).
    { intros C. flat constr:(MAY) 2%nat. intros FLt13 _. flat constr:(FLt13) 2%nat. flclear FLt13. intros _ FLt14. flat constr:(FLt14) 5%nat. flclear FLt14. intros _ _ LY _ OY. cbn [dY md_own md_n md_p md_limbs] in OY, LY. rewrite C in OY. dlia. }
    specialize (C1 OYN). specialize (C5 OYN).
    flat constr:(XW) 3%nat. intros XCW XD XP. cbn [dX md_addr md_own md_p md_n] in XCW, XD, XP.
    assert (NN : bv_unsigned (zx16 (Z_to_bv 64 nX)) = nX) by (unfold zx16; rewrite !unsigned_lit by dlia; apply Z.mod_small; dlia).
    unfold mpi_cells in CHX, CHY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    pose proof (conj PBY I) as PBYc.
    zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := i) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by dlia; try eassumption; try reflexivity; try dlia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by dlia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ dlia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ mc m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame mo mo2 |- _ => rename H into MF2 end.
    clear STc MIc. heap_transport HPc.
    assert (SOK2 : statics_ok usegs L m2) by (eapply statics_ok_heap_pres; [exact SOKc| exact HPc| exact SW]).
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m2).
    { eapply heap_presx_trans; [exact PXc|]. eapply heap_presx_trans; [eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| dlia]|].
      eapply heap_presx_of_pres_sub; [exact HPc| intros b Hb; exact Hb| dlia| dlia]. }
    assert (PXH2 : ownX = LHeap -> u32arr usegs m2 pX xs).
    { intros EO. pose proof (PXH EO) as U. apply u32arr_cells in U.
      apply (heap_pres_rw_cells usegs L LB _ mc m2 _ _ HPc) in U.
      2: { cbn [cells_size csize Nat.add]. flat constr:(MAX) 2%nat. intros FLt15 _. flat constr:(FLt15) 2%nat. flclear FLt15. intros _ FLt16. flat constr:(FLt16) 5%nat. flclear FLt16. intros _ _ _ _ OX. cbn [dX md_own md_n md_p md_limbs] in OX. rewrite EO in OX.
           flat constr:(OX) 3%nat. flclear OX. intros _ PIN _. intros a Ha. right; right. exists (pX, 4 * nX). split; [exact PIN| cbn; dlia]. }
      eapply u32arr_of_cells; [exact U| reflexivity]. }
    flat constr:(PBYc) 2%nat. flclear PBYc. intros PBYc _.
    assert (PBY2 : bytes_at usegs m2 pY (u32s ys)).
    { flat constr:(MAY) 2%nat. intros FLt17 _. flat constr:(FLt17) 2%nat. flclear FLt17. intros _ FLt18. flat constr:(FLt18) 5%nat. flclear FLt18. intros _ _ LY _ OY. cbn [dY md_own md_n md_p md_limbs] in OY, LY.
      destruct ownY; [exfalso; exact (OYN eq_refl)| |].
      - flat constr:(OY) 3%nat. flclear OY. intros _ PIN _. apply (heap_pres_bytes_at usegs L LB _ mc m2 _ _ HPc); [| rewrite u32s_length; intros a Ha; right; right; exists (pY, 4 * nY); split; [exact PIN| cbn; dlia]].
        eapply bytes_at_transport; [exact PBYc| exact MU|]. rewrite u32s_length. cbn. split; [generalize C5; dlia| exact I].
      - flat constr:(OY) 5%nat. flclear OY. intros _ _ _ PB0 RO. eapply static_limbs_any_mem; [exact MI0| exact MI2| exact PB0|]. rewrite u32s_length. intros j Hj. apply RO. dlia. }
    clear HHc SOKc MU WM HPc PXc PXH PBYc.
    destruct PO as (h2 & HT2 & [[-> HH2] | (A & -> & HBA & HH2 & HNEW)]).
    { (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      zstep; if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FRM ST2 (bv_unsigned sp). zstep.
      apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h2, LB.
      exists (mkMPD X sgY nX pX xs padX ownX), MBEDTLS_ERR_MPI_ALLOC_FAILED.
      split; [reflexivity|]. split; [assumption|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|].
      split; [exact HH2|].
      split. { split; [| cbn; exact SGY]. flat constr:(MAX) 2%nat. intros FLt19 _. flat constr:(FLt19) 2%nat. flclear FLt19. intros _ FLt20. flat constr:(FLt20) 5%nat. flclear FLt20. intros _ _ _ _ OX. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX |- *.
        split; [exact CHX|]. split; [exact XAL|]. split; [exact X0|]. split; [exact LENX|]. split; [unfold MPI_MAX_LIMBS; dlia|].
        destruct ownX; [exact OX| | exfalso; exact (NST eq_refl)]. flat constr:(OX) 4%nat. flclear OX. intros N1 PIN PAL _. split; [exact N1|]. split; [exact PIN|]. split; [exact PAL| exact (PXH2 eq_refl)]. }
      split; [apply mpd_out_same_blocks; cbn; [reflexivity| exact NST| reflexivity]|].
      split; [exact HPX2|]. split; [exact SOK2|].
      unfold copy_Rx, copy_R. cbn [dX dY md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [| intros E; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in E; clear - E; lia].
      split; [right; (flsplit; repeat split); reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros b Hb; left; exact Hb. }
    (* [comment removed for export] *)
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2. pose proof (HND _ _ _ _ HH2) as ND2.
    pose proof HBA as HBA'. flat constr:(HBA') 5%nat. flclear HBA'. intros A0 A16 _ A4 A5. flat constr:(HAP2) 2%nat. flclear HAP2. intros HAPA _.
    assert (XA' : forall a, X <= a < X + 16 -> ~ (A <= a < A + i * 4)).
    { intros a Ha C. destruct (XCW a Ha) as [S|[[D NS]|([B k] & Hb & R)]]; [dlia| generalize A5; destruct DIMG; dlia| generalize (HAPA B k Hb); cbn in R; dlia]. }
    pose proof (pointwise_apart X 16 A (i * 4) ltac:(dlia) ltac:(dlia) XA') as XA. clear XA'.
    assert (YA' : forall a, Y <= a < Y + 16 -> ~ (A <= a < A + i * 4)).
    { intros a Ha C. destruct (YCR a Ha) as [S|[[D NS]|([B k] & Hb & R)]]; [dlia| generalize A5; destruct DIMG; dlia| generalize (HAPA B k Hb); cbn in R; dlia]. }
    pose proof (pointwise_apart Y 16 A (i * 4) ltac:(dlia) ltac:(dlia) YA') as YA. clear YA'.
    pose proof (ylimbs_apart_fresh A (i * 4) ltac:(dlia) ltac:(dlia) HBA HAPA) as YLA.
    replace (i * 4) with (4 * i) in * by dlia.
    zstep; if_cases KZ; zify_cond KZ; [exfalso; dlia|].
    zstep. zstep.
    flat constr:(MAX) 2%nat. intros FLt21 _. flat constr:(FLt21) 2%nat. flclear FLt21. intros _ FLt22. flat constr:(FLt22) 5%nat. flclear FLt22. intros _ _ _ _ OX. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX.
    assert (OC : ownX = LNull \/ ownX = LHeap) by (clear -NST; destruct ownX; [left| right| exfalso; exact (NST eq_refl)]; reflexivity).
    destruct OC as [EO|EO]; rewrite EO in OX.
    - (* [comment removed for export] *)
      flat constr:(OX) 2%nat. flclear OX. intros P0 N0.
      zstep; if_cases KP; zify_cond KP; [| exfalso; rewrite ?Z.mod_small in KP by dlia; dlia].
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (X, X + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj HH2 I) as HH2c. pose proof (conj SOK2 I) as SOK2c. clear HH2 SOK2.
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      flat constr:(HH2c) 2%nat. flclear HH2c. intros HH2c _. flat constr:(SOK2c) 2%nat. flclear SOK2c. intros SOK2c _.
      assert (HH4 : HEAP usegs L HI h2 ((A, 4 * i) :: LB) m4 mo2).
      { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2c| exact ACL| exact MU| exact WM|].
        intros a Ha NO. cbn in NO. rewrite HT2.
        destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(dlia)) as [C|[C|([B k] & Hb & R)]]; [left; dlia| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb| exact R]] |]|]; left; dlia. }
      eapply (final_walk i i A (repeat (Z_to_bv 64 0) (Z.to_nat i)) m4 mo2 h2 ((A, 4 * i) :: LB)); try eassumption; try reflexivity; try dlia.
      + intros k w Hk HN. apply nth_error_In in HN. apply repeat_spec in HN. exact HN.
      + split; [| cbn; exact SGY]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [assumption|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite repeat_length; dlia|]. split; [unfold MPI_MAX_LIMBS; dlia|].
        split; [dlia|]. split; [left; reflexivity|]. split; [exact A16|].
        eapply u32arr_of_cells; [eassumption|]. rewrite u32s_repeat0. f_equal. dlia.
      + unfold dX. rewrite P0, EO. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
        split. { intros b [<-|Hb]; [right; left; reflexivity| left; exact Hb]. }
        split. { intros b Hb Hn. right. exact Hb. }
        intros b [].
      + unfold dX. rewrite EO. cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. intros HinA. generalize (HAPA A (4 * i) HinA). dlia.
      + eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
        intros a Ha Hc Ho. unfold mpd_ivs in Ho. unfold dX in Ho. rewrite EO in Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros O1 _.
        split; [| split; [exact O1| exact I]].
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia].
      + eapply statics_ok_munch; [exact SOK2c| exact MU|]. intros a Ha NW. cbn. split; [dlia|]. split; [| exact I]. intros HX. exact (NW (XD a HX Ha)).
    - (* [comment removed for export] *)
      flat constr:(OX) 4%nat. flclear OX. intros N1 PIN PAL _. specialize (XP EO). pose proof (PXH2 EO) as PX2. clear PXH2.
      assert (PXY : pX + 4 * nX <= pY \/ pY + 4 * nY <= pX).
      { destruct C3 as [E|[C|[C|C]]]; [exfalso; apply NEQ; injection E; auto| exfalso; exact (C EO)| exfalso; exact (OYN C) | exact C]. }
      flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
      pose proof (HAPA pX (4 * nX) PIN) as APA.
      zstep; if_cases KP; zify_cond KP; [exfalso; dlia|].
      zstep. zstep. land_zero_any. zstep. if_false.
      zstep. zstep. rewrite ?NN. replace (nX ≪ 2) with (4 * nX) by (rewrite Z.shiftl_mul_pow2 by dlia; dlia).
      zstep.
      assert (HN2 : rw_cells usegs m2 A ([CB (4 * length xs) (repeat (Z_to_bv 8 0) (4 * length xs))] ++ [CB (Z.to_nat (4 * (i - nX))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (i - nX))))])).
      { eapply rw_cells_reshape; [exact HNEW| |].
        - cbn. rewrite !repeat_length; (flsplit; repeat split); reflexivity.
        - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. dlia. }
      apply rw_cells_app in HN2. flat constr:(HN2) 2%nat. flclear HN2. intros HNA HNB. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
      replace (A + Z.of_nat (4 * length xs + 0)) with (A + 4 * nX) in HNB by dlia.
      pose proof (proj1 PX2) as PBA.
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 4 * i); (X, X + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj PBY2 I) as PBYc.
      zstep.
      pose proof U_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
      eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs); rewrite ?unsigned_lit by dlia; [ exact PBA | rewrite u32s_length; dlia | replace (Z.to_nat (4 * nX)) with (4 * length xs)%nat by dlia; exact HNA | generalize APA; dlia | exact MI2 ] | ].
      clear SPc. unfold memcpy_post. rewrite !unsigned_lit by dlia. post_call usegs m2.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
      match goal with H : rw_cells usegs m3 A _ |- _ => rename H into PA end.
      assert (HH3 : HEAP usegs L HI h2 ((A, 4 * i) :: LB) m3 mo2).
      { clear_disj. eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MU| exact WM|].
        intros a Ha NO. cbn in NO. rewrite HT2.
        destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(dlia)) as [C|[C|([B k] & Hb & R)]]; [left; dlia| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb| exact R]] |] |].
        all: destruct (Z.le_gt_cases A a); [destruct (Z.lt_ge_cases a (A + 4 * i)); [right; right; exists (A, 4 * i); split; [left; reflexivity| cbn; dlia] |] |].
        all: left; dlia. }
      apply u32arr_cells in PX2. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
      zstep. zstep. zstep. rewrite ?NN. replace (nX ≪ 2) with (4 * nX) by (rewrite Z.shiftl_mul_pow2 by dlia; dlia).
      zstep.
      eapply aevtM_cut.
      { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pX) (len := 4 * nX) (lo := lo) (junk := u32s xs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by dlia; try eassumption; try reflexivity; try dlia.
        right. split; [right; exact PIN|]. replace (Z.to_nat (4 * nX)) with (4 * length xs)%nat by dlia. exact PX2. }
      cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m4 mo4 h4 E PO. injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by dlia.
      flat constr:(PO) 7%nat. flclear PO. intros MI4 ST4 MF4 HT4 HH4 PX4 SOK4.
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ dlia | reflexivity ]) end.
      assert (LBR : lb_remove pX ((A, 4 * i) :: LB) = (A, 4 * i) :: lb_remove pX LB) by (cbn; destruct (Z.eqb_spec A pX); [generalize APA; dlia| reflexivity]).
      rewrite LBR in HH4, PX4. clear LBR.
      assert (PBY4 : ownY = LHeap -> bytes_at usegs m4 pY (u32s ys)).
      { intros EOY. flat constr:(PBYc) 2%nat. flclear PBYc. intros PB2 _. flat constr:(MAY) 2%nat. intros FLt23 _. flat constr:(FLt23) 2%nat. flclear FLt23. intros _ FLt24. flat constr:(FLt24) 5%nat. flclear FLt24. intros _ _ _ _ OY. cbn [dY md_addr md_sg md_n md_p md_limbs md_pad md_own] in OY. rewrite EOY in OY.
        flat constr:(OY) 4%nat. flclear OY. intros _ PINY _ _.
        assert (PB3 : bytes_at usegs m3 pY (u32s ys)).
        { eapply bytes_at_transport; [exact PB2| exact MU|]. rewrite u32s_length. cbn. split; [generalize C5; dlia|]. split; [generalize YLA; dlia|]. split; [generalize C1; dlia| exact I]. }
        apply (heap_presx_bytes_at usegs L _ _ _ m3 m4 _ _ PX4); [exact PB3| | rewrite u32s_length; cbn; split; [generalize PXY; dlia| exact I]].
        rewrite u32s_length. intros a Ha. right; right. exists (pY, 4 * nY). split; [| cbn; dlia].
        right. apply (in_lb_remove_other LB pX (4 * nX) pY (4 * nY) ND PIN PINY). intros E; injection E as E1 E2. generalize PXY; dlia. }
      apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in FRM; [| cbn [cells_size csize Nat.add]; intros a Ha; left; dlia | cbn; split; [dlia| exact I] ].
      apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in PA; [| cbn [cells_size csize Nat.add]; intros a Ha; right; right; exists (A, 4 * i); split; [left; reflexivity| cbn; dlia] | cbn; split; [generalize APA; dlia| exact I] ].
      apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in HNB; [| cbn [cells_size csize Nat.add]; intros a Ha; right; right; exists (A, 4 * i); split; [left; reflexivity| cbn; dlia] | cbn; split; [generalize APA; dlia| exact I] ].
      apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in CHX;
        [| cbn [cells_size csize Nat.add]; intros a Ha;
           destruct (XCW a ltac:(dlia)) as [C|[C|([B k] & Hb & R)]]; [left; dlia| right; left; exact C| right; right; exists (B, k); split; [|exact R]];
           right; apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb); intros E; injection E as -> ->; cbn in R; generalize XP; dlia
         | cbn; split; [generalize XP; dlia| exact I] ].
      apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in CHY;
        [| cbn [cells_size csize Nat.add]; intros a Ha;
           destruct (YCR a ltac:(dlia)) as [C|[C|([B k] & Hb & R)]]; [left; generalize C4; dlia| right; left; exact C| right; right; exists (B, k); split; [|exact R]];
           right; apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb); intros E; injection E as -> ->; cbn in R; generalize (C2 EO); dlia
         | cbn; split; [generalize (C2 EO); dlia| exact I] ].
      clear PX2. try clear ST2. try clear MI2.
      assert (HPX4 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m4).
      { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_trans.
        - eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho |- *. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
          split; [| split; [| split; [exact O1| exact I]]].
          + destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _); cbn in R, B4; dlia].
          + destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| generalize A5; destruct DIMG; dlia| generalize (HAPA B k Hb); cbn in R; dlia].
        - intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
          apply PX4; [exact Ha| | cbn; split; [exact O2| exact I]].
          destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; clear_disj; dlia| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
          right. apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb). intros E; injection E as -> ->; cbn in R; clear -R O2; dlia. }
      clear HPX2 PX4 MU WM.
      pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (X, X + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
      pose proof (conj HH4 I) as HH4c. pose proof (conj SOK4 I) as SOK4c. pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
      flat constr:((heap_blocks _ _ HI _ _ _ _ HH4)) 2%nat. intros HBR4 _.
      clear HH4 SOK4.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      flat constr:(HH4c) 2%nat. flclear HH4c. intros HH4c _. flat constr:(SOK4c) 2%nat. flclear SOK4c. intros SOK4c _.
      assert (XCW4 : forall a, X <= a < X + 16 -> client_waddr L ((A, 4 * i) :: lb_remove pX LB) lo (heap_top usegs L HI h) a).
      { intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; clear_disj; dlia| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
        right. apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb). intros E; injection E as -> ->; cbn in R; generalize XP; dlia. }
      assert (HH6 : HEAP usegs L HI h4 ((A, 4 * i) :: lb_remove pX LB) m6 mo4).
      { clear_disj. eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH4c| exact ACL| exact MU| exact WM|].
        intros a Ha NO. cbn in NO. rewrite HT4, HT2.
        destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [apply XCW4; dlia|]|]; left; dlia. }
      match goal with H : mem_inv usegs m6 |- _ => rename H into MI6 end.
      assert (PBY6 : bytes_at usegs m6 pY (u32s ys)).
      { flat constr:(MAY) 2%nat. intros FLt25 _. flat constr:(FLt25) 2%nat. flclear FLt25. intros _ FLt26. flat constr:(FLt26) 5%nat. flclear FLt26. intros _ _ _ _ OY. cbn [dY md_addr md_sg md_n md_p md_limbs md_pad md_own] in OY.
        assert (OCY : ownY = LHeap \/ ownY = LStatic) by (clear -OYN; destruct ownY; [exfalso; exact (OYN eq_refl)| left| right]; reflexivity).
        destruct OCY as [EOY|EOY].
        - eapply bytes_at_transport; [exact (PBY4 EOY)| exact MU|]. rewrite u32s_length. cbn. split; [generalize C5; dlia|]. split; [generalize C1; dlia| exact I].
        - rewrite EOY in OY. flat constr:(OY) 5%nat. flclear OY. intros _ _ _ PB0 RO. eapply static_limbs_any_mem; [exact MI0| exact MI6| exact PB0|]. rewrite u32s_length. intros j Hj. apply RO. dlia. }
      eapply (final_walk i i A (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (i - nX))) m6 mo4 h4 ((A, 4 * i) :: lb_remove pX LB)); try eassumption; try reflexivity.
      + clear_disj; dlia.
      + intros k w Hk HN. rewrite nth_error_app2 in HN by (clear_disj; dlia). apply nth_error_In in HN. apply repeat_spec in HN. exact HN.
      + rewrite HT4. exact HT2.
      + eapply mo_frame_trans; [exact MF2| exact MF4].
      + split; [| cbn; exact SGY]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [assumption|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite length_app, repeat_length; clear_disj; dlia|]. split; [unfold MPI_MAX_LIMBS; clear_disj; dlia|].
        split; [clear_disj; dlia|]. split; [left; reflexivity|]. split; [exact A16|].
        apply u32arr_app. split; [eapply u32arr_of_cells; [exact PA| reflexivity]|].
        match goal with H : rw_cells usegs m6 (A + 4 * nX) _ |- _ => replace (A + 4 * Z.of_nat (length xs)) with (A + 4 * nX) by (clear_disj; dlia); eapply u32arr_of_cells; [exact H|] end.
        rewrite u32s_repeat0. f_equal. clear_disj; dlia.
      + unfold dX. rewrite EO. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
        split. { intros b [<-|Hb]; [right; left; reflexivity| left; eapply In_lb_remove; exact Hb]. }
        split. { intros [B k] Hb Hn. right. apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb). intros E. apply Hn. left. symmetry. exact E. }
        intros b [<-|[]] [E|HinR]; [injection E; clear_disj; dlia| exfalso; exact (lb_remove_notin LB pX (4 * nX) ND HinR)].
      + unfold dX. rewrite EO. cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. intros HinA. destruct (Z.eq_dec A pX) as [EAP|NAP].
        * exact (nodup_fst_neq LB pX (4 * nX) A (4 * i) ND PIN HinA ltac:(intros E; injection E; clear_disj; dlia) EAP).
        * generalize (HAPA A (4 * i) HinA). dlia.
      + eapply heap_presx_trans; [exact HPX4|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
        intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho |- *. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
        split; [| split; [exact O1| exact I]].
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia].
      + eapply statics_ok_munch; [exact SOK4c| exact MU|]. intros a Ha NW. cbn. split; [clear_disj; dlia|]. split; [| exact I]. intros HX. exact (NW (XD a HX Ha)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00f0@D11913617988.130D27299517041.134D39409836362.135D39409836362.136D39409836362.137D40825300204.131D40825300204.132D41849979239.131D41849979239.132D44396710448.128D47955196208.128D52101704109.136D52101704109.137D52101704109.138D52101720110.134D52101720110.135D52101720110.136D52101733636.133D52101733636.134D52101733636.135D52101802538.142D52101802538.143D52101802538.144D54391985784.135D54391985784.136D54391985784.137D54398102733.136D54398102733.137D54398102733.138D54398282304.134D54398282304.135D54398282304.136D59308567928.123D59308628304.131D59308628433.131D59308628433.132D67987673230.129D67987673230.130D8927526560.128 L13972576688.130L13972576688.131L1599948709.133 L28767740167.130L28767740167.131L38541400496.130L40825300204.121L40825300204.124L42088244894.133L48773092713.120L48773092713.123L48773092840.121L48773092840.124L62965564504.133L791711292.130  00000F00G00\01101F01T01b02802^03303H04904j05[05m06?06Q07C08508g09^0:U0;L0<C0=:0>10>_0?M0@;0A10Ag0B]0CC0Cl0DS0E:0EJ0EZ0F50GI0H]0H^0J90KT0L90LG0LU0M90M]0NA0Ne0OI0Om0Q3S2sp1X2nX2xs1Y2ys1i2K1FS2sp1X2xs1Y2ys1a1H2H0S2sp1X2xs1Y2ys1a1H2H0S2sp1X2xs1Y2ys1a1H2H0S2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS2sp1X2nX2xs1Y2ys1i2K1S2sp1X2nX2xs1Y2nY2ys1i2Hi2X02Y03SPB2N0S2sp1X2nX2xs1Y2ys3NRXS2sp1X2nX2xs1Y2ys3NRXS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB1a1CS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB1a1CS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB1a1CS2sp1X2xs1Y2ys1a1CS2sp1X2xs1Y2ys1a1CS2sp1X2xs1Y2ys1a1CS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB1a2HaS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB1a2HaS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB1a2HaS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL2X02Y03SPB1a1B1k1R2B02B4S1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL2X02Y03SPB1a1B1k1R2B02B4S1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL2X02Y03SPB1a1B1k1R2B02B4S1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO4HTOP2X02Y03SPB1a2NO2H0S1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO4HTOP2X02Y03SPB1a2NO2H0S1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO4HTOP2X02Y03SPB1a2NO2H0S1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO2X02Y03SPB1a1CS1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO2X02Y03SPB1a1CS1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO2X02Y03SPB1a1CS1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO4HTOP2X02Y03SPB1a2NO1HS1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO4HTOP2X02Y03SPB1a2NO1HS1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO4HTOP2X02Y03SPB1a2NO1HS2sp1X2xs1Y2nY2pY2ys1i2Hi2X02Y03SPB2OYS2sp1X2nX2xs1Y2nY2ys1i2Hi2X02Y03SPB2N02K1S2sp1X2xs1Y2nY2ys1i2Hi2X02Y03NRY3SPB2K2S2sp1X2xs1Y2nY2ys1i2Hi2X02Y03NRY3SPB2K2S2sp1X2xs1Y2ys1iS2sp1X2xs1Y2ys1iS2sp1X2nX2xs1Y2ys2X02Y03SPBS1L3HLS2sp2lo1X2xs1Y3sgY2nY2pY2ys3NEQ3SLO2X02Y04LENY3SXY2XS2C12C53SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2xs1Y3sgY2nY2pY2ys3NEQ3SLO2X02Y04LENY3SXY2XS2C12C53SPB2HB5Ha_st5Hl_stFS1L3HLS2sp2lo1X2xs1Y3sgY2nY2ys3NEQ3SLO3SPA1i2Hi3XAL2X02Y04LENY3SXY2XS2C43SPB2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2xs1Y3sgY2nY2ys3NEQ3SLO3SPA1i2Hi3XAL2X02Y04LENY3SXY2XS2C43SPB2HB5Ha_st5Hl_stS2sp1X2xs1Y3sgY2ys3SXY2HB5Ha_st5Hl_stS2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS2sp1X2xs1Y3sgY2ys2X02HB5Ha_st5Hl_stS2sp1X2xs1Y2nY2ys1i2Hi2X02Y03NRY3SPBS2sp1X2xs1Y2nY2ys1i2Hi2X02Y03NRY3SPBS2sp1X2xs1Y2nY2ys1i2Hi2X02Y03NRY3SPBS2sp1X2xs1Y2nY2ys1i2Hi2X02Y03NRY3SPBS2sp1X2xs1Y3sgY2ys2XB2HB5Ha_st5Hl_stS2sp1X2nX2pX2xs1Y3sgY2ys3NEQ2X04LENX2Y03SXY3SPB3XPL3C2L2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  Lemma tail28 : forall (i : Z) (m1 : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    1 <= i <= nY -> zeros_above ys i -> trim_i ys i ->
    rw_cells usegs m1 X (mpi_cells pX (Z_to_bv 64 sgX) nX padX) -> (ownX = LHeap -> u32arr usegs m1 pX xs) ->
    rw_cells usegs m1 Y (mpi_cells pY (Z_to_bv 64 sgY) nY padY) -> bytes_at usegs m1 pY (u32s ys) ->
    HEAP usegs L HI h LB m1 mo -> munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    statics_ok usegs L m1 -> mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells usegs m1 (bv_unsigned sp + -48) (FRAME8 s4) ->
    aevtM usegs mo POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y)
      (Z_to_bv 64 (i - 1)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1f6c4) fc None m1 (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until t6. intros Hi ZY TI CHX PXH CHY PBY HH1 MU WM SOK1 MI1 ST1 FRM.
    flat constr:(facts) 14%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY XS. pose proof alloc_ceiling_pos as ACP.
    flat constr:(CSEP) 6%nat. intros C1 C2 C3 C4 C5 _. cbn [dX dY md_addr md_own md_p md_n] in C1, C2, C3, C4, C5.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. flat constr:((heap_blocks _ _ HI _ _ _ _ HH1)) 2%nat. intros HBR HAP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    assert (OYN : ownY <> LNull).
    { intros C. flat constr:(MAY) 2%nat. intros FLt27 _. flat constr:(FLt27) 2%nat. flclear FLt27. intros _ FLt28. flat constr:(FLt28) 5%nat. flclear FLt28. intros _ _ LY _ OY. cbn [dY md_own md_n md_p md_limbs] in OY, LY. rewrite C in OY. dlia. }
    specialize (C1 OYN). specialize (C5 OYN).
    flat constr:(XW) 3%nat. intros XCW XD XP. cbn [dX md_addr md_own md_p md_n] in XCW, XD, XP.
    unfold mpi_cells in CHX, CHY.
    apply (munch_weaken _ [(bv_unsigned sp - 48, bv_unsigned sp); (X, X + 16)]) in MU; [| intros x Hx; clear -Hx; cbn in Hx |- *; tauto].
    assert (OC : ownX = LNull \/ ownX = LHeap) by (clear -NST; destruct ownX; [left| right| exfalso; exact (NST eq_refl)]; reflexivity).
    assert (PXo : exists ws, (ownX = LHeap -> ws = xs) /\ (ownX = LHeap -> u32arr usegs m1 pX ws)).
    { destruct OC as [EO|EO]; [exists []; split; intros C; rewrite EO in C; discriminate| exists xs; split; [auto| exact PXH]]. }
    flat constr:(PXo) 3%nat. flclear PXo. intros ws WS1 WS2.
    assert (NN : bv_unsigned (zx16 (Z_to_bv 64 nX)) = nX) by (unfold zx16; rewrite !unsigned_lit by dlia; apply Z.mod_small; dlia).
    destruct OC as [EO|EO].
    - (* [comment removed for export] *)
      flat constr:(MAX) 2%nat. intros FLt29 _. flat constr:(FLt29) 2%nat. flclear FLt29. intros _ FLt30. flat constr:(FLt30) 5%nat. flclear FLt30. intros _ _ _ _ OX. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX. rewrite EO in OX. flat constr:(OX) 2%nat. flclear OX. intros P0 N0.
      zstep; if_false_x. zstep. land_zero_any. zstep. if_false.
      zstep. zstep. zstep. replace (i - 1 + 1) with i by dlia.
      zstep. rewrite sx16_sign in CHX by exact SGY.
      zstep. replace (i ≪ 2) with (4 * i) by (rewrite Z.shiftl_mul_pow2 by dlia; dlia).
      zstep; if_cases K1; zify_cond K1; [| exfalso; rewrite ?NN in K1; dlia].
      zstep. zstep. zstep. zstep; if_cases K2; zify_cond K2.
      { exfalso. rewrite Z.shiftr_div_pow2 in K2 by dlia. dlia. }
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      eapply (grow_path i m2); try eassumption; try reflexivity.
      + dlia.
      + intros C. rewrite EO in C. discriminate.
      + eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH0| exact ACL| exact MU| exact WM|].
        intros a Ha NO. cbn in NO.
        destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(dlia)) as [C|[C|C]]; [left; dlia| right; left; exact C| right; right; exact C] |]|]; left; dlia.
      + eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros O1 _.
        split; [| split; [exact O1| exact I]].
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia].
      + eapply statics_ok_munch; [exact SOK0| exact MU|]. intros a Ha NW. cbn. split; [dlia|]. split; [| exact I]. intros HX. exact (NW (XD a HX Ha)).
    - (* [comment removed for export] *)
      specialize (WS2 EO). rewrite (WS1 EO) in WS2. clear WS1 PXH. pose proof (XP EO) as XPL. pose proof (C2 EO) as C2L.
      flat constr:(WS2) 3%nat. intros PX0 PXB _. 
      zstep; if_false_x. zstep. land_zero_any. zstep. if_false.
      zstep. zstep. zstep. replace (i - 1 + 1) with i by dlia.
      zstep. rewrite sx16_sign in CHX by exact SGY.
      zstep. replace (i ≪ 2) with (4 * i) by (rewrite Z.shiftl_mul_pow2 by dlia; dlia).
      zstep; if_cases K1; zify_cond K1.
      + zstep. zstep. zstep. zstep; if_cases K2; zify_cond K2.
        { exfalso. rewrite Z.shiftr_div_pow2 in K2 by dlia. dlia. }
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
        eapply (grow_path i m2); try eassumption; try reflexivity.
        * rewrite ?NN in K1. dlia.
        * intros _. assumption.
        * eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH0| exact ACL| exact MU| exact WM|].
          intros a Ha NO. cbn in NO.
          destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(dlia)) as [C|[C|C]]; [left; dlia| right; left; exact C| right; right; exact C] |]|]; left; dlia.
        * eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros O1 _.
          split; [| split; [exact O1| exact I]].
          destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia].
        * eapply statics_ok_munch; [exact SOK0| exact MU|]. intros a Ha NW. cbn. split; [dlia|]. split; [| exact I]. intros HX. exact (NW (XD a HX Ha)).
      + rewrite ?NN in K1.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
        eapply (memset_path i m2); try eassumption; try reflexivity.
        * dlia.
        * eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH0| exact ACL| exact MU| exact WM|].
          intros a Ha NO. cbn in NO.
          destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(dlia)) as [C|[C|C]]; [left; dlia| right; left; exact C| right; right; exact C] |]|]; left; dlia.
        * eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros O1 _.
          split; [| split; [exact O1| exact I]].
          destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia].
        * eapply statics_ok_munch; [exact SOK0| exact MU|]. intros a Ha NW. cbn. split; [dlia|]. split; [| exact I]. intros HX. exact (NW (XD a HX Ha)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)



  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?D11497235722.7900000CS2sp1j1w2Hj1k2Hk2NE". (* [comment removed for export] *)
  Lemma zeros_above_down : ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "Pzs,(:.(;.&40.))Pj,$3.Pw,(;.&40.)P,(5.=R2.)P,(4;.R4.(16.R3.+1.))P,(2.(1<.(;.&40.))(3<.(;.&40.)R5.(4=.R4.))(3=.(;.&40.)R3.))P,(2.$3.(2<.(24.&40.R4.)(3>.+2.+20.))=)(4;.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros zs j w Hj HZ HN HW k w' Hk HN'.
    destruct (Nat.eq_dec k (Z.to_nat j)) as [->|NE]; [rewrite HN in HN'; injection HN' as <-; exact HW|].
    eapply HZ; [| exact HN']. dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@D12092728342.121D13565586014.120D33528906030.120D372354156.120  D42464325972.117D42470816451.118D42609306089.118D44309540429.117D45266433882.116D45272317262.118D47564374853.120D47578005180.120D59310778860.95 D59314841581.115D61507227851.120D68629579028.117L16586317372.11600000^01B01`02H02f03D03g04C04f05K06306Q06a07Q07R08;08oS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr2X02Y03PYB1w2J1S2sp1X2xs1Y2pY2ys1k1j2Hj2X02Y03PYB1wS2sp1X2xs1Y2pY2ys1k1j2Hj3PYB1wS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr3PYB1w2K2S2sp1X2xs1Y2pY2ys1k1j2Hj3PYB1wS2sp1X2xs1Y2pY2ys1k1j2Hj3PYB1wS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr3PYBS2sp1X2xs1Y2pY2ys1k1j2Hj3PYBS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr3PYBS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr3PYB1wS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr3PYB1w2K2S2sp1X2xs1Y2pY2ys1k1j2Hj3PYB1wS2sp2nY1j2Hj3HjrS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr2X02Y04LENY3PYB1NFS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr2X02Y03PYBS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr2X02Y04LENY3PY03PYB1w". (* [comment removed for export] *)
  Lemma scan_loop : forall (k : nat) (j : Z) (m1 : mem) (t0 t1 t2 t3 t4 t5 t6 : word),
    j = Z.of_nat k -> 1 <= j <= nY - 1 -> zeros_above ys (j + 1) ->
    rw_cells usegs m1 X (mpi_cells pX (Z_to_bv 64 sgX) nX padX) -> (ownX = LHeap -> u32arr usegs m1 pX xs) ->
    rw_cells usegs m1 Y (mpi_cells pY (Z_to_bv 64 sgY) nY padY) -> bytes_at usegs m1 pY (u32s ys) ->
    HEAP usegs L HI h LB m1 mo -> munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
    statics_ok usegs L m1 -> mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp + -48) ->
    rw_cells usegs m1 (bv_unsigned sp + -48) (FRAME8 s4) ->
    aevtM usegs mo POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y)
      (Z_to_bv 64 j) (Z_to_bv 64 pY) (Z_to_bv 64 0) (Z_to_bv 64 (pY + 4 * j)) (Z_to_bv 64 1) (Z_to_bv 64 (pY + 4 * j))
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1f698) fc None m1 (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until t6; intros Hj Hjr ZY CHX PXH CHY PBY HH1 MU WM SOK1 MI1 ST1 FRM; [exfalso; dlia|].
    flat constr:(facts) 14%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY XS.
    flat constr:(PBY) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    destruct (nth_error ys (Z.to_nat j)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; dlia].
    zstep; if_false_x. zstep. zstep. zstep; if_false_x. zstep; if_false_x.
    pose proof (u32ro_read usegs m1 pY ys j w _ PBY N ltac:(dlia) ltac:(f_equal; dlia)) as RD.
    zstep. clear RD.
    zstep; if_cases K; zify_cond K.
    - replace (Z_to_bv 64 j) with (Z_to_bv 64 (j + 1 - 1)) by (f_equal; dlia).
      assert (TI : trim_i ys (j + 1)).
      { right. exists w. split; [replace (Z.to_nat (j + 1 - 1)) with (Z.to_nat j) by dlia; exact N|].
        intros WZ. apply K. rewrite bv_unsigned_sx32. apply (proj2 (sxz_zero_iff _ (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(dlia)))). exact WZ. }
      eapply (tail28 (j + 1)); try eassumption. dlia.
    - assert (WZ : bv_unsigned w mod 2^32 = 0).
      { rewrite bv_unsigned_sx32 in K. pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(dlia)) as H.
        exact (proj1 (sxz_zero_iff _ H) K). }
      pose proof (zeros_above_down ys j w ltac:(dlia) ZY N WZ) as ZY'.
      zstep. zstep. zstep.
      zstep; if_cases K2; zify_cond K2.
      + replace (Z_to_bv 64 (pY + 4 * j + -4)) with (Z_to_bv 64 (pY + 4 * (j + -1))) by (f_equal; dlia).
        eapply (IH (j + -1)); try eassumption; try dlia. replace (j + -1 + 1) with j by dlia. exact ZY'.
      + assert (J1 : j = 1) by dlia. rewrite J1 in ZY'.
        replace (Z_to_bv 64 (j + -1)) with (Z_to_bv 64 (1 - 1)) by (f_equal; dlia).
        assert (TI : trim_i ys 1) by (left; reflexivity).
        eapply (tail28 1); try eassumption. dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  Local Ltac2 Set LiaOrc.tbl := fun () => "0180@D12996331683.164D1649607660.162 D22027126931.140D23079099505.162D2547701457.140 D2547963990.162 D32964697080.140D36037904305.140D36249740628.145D39409837249.143D39409837249.145D39411933386.146D41832577409.140D48794105081.142D48794105210.144D48794105210.146D52101703855.169D52101720110.143D52101720110.145D52101720110.146D52101720239.167D52101733636.165D52101802538.175D52476392461.143D52478557175.145D53518944813.143D54391984752.142D54391984752.144D54391985139.143D54391985139.145D54394083320.146D54398102733.144D54398102733.146D54398102733.147D57751203498.167D64056818505.162D68343600635.145D68345764353.143D6999162054.162 L11660649725.136L18124362632.135L20876567471.135L20876567471.142L22700267513.158L22704459656.3  L22704459656.4  L22704459656.6  L27909704021.159L30962707192.121L31378308326.123L33105263709.158L33512287714.158L39033014942.136L39033014942.143L43061741705.121L4855685921.0   L50678406341.122L52821374450.135L53705465148.159L57626602889.4  L57626602889.6  L59308579797.134L59310664906.9  L59310959187.134L59321607707.130L59321607707.132L59321607707.133L61277935351.135L62811875910.139L62811875910.140L66856265147.4  R22706564033.16500000L00d01O02302Q03503Z04C04l05F05\06306I07;07m08b09\0:60:h0;`0<50<m0=j0>b0?Z0?k0@O0AF0Aj0Bd0C_0DC0E10E_0FM0G10GY0HA0HV0Hj0IA0IB0IC0I`0Ik0J80JK0Jm0KI0KW0LL0M90M:0M;0M`0Ma0NH0N\0O>0OK0O^0P80PF0Ph0Q@0Qb0RD0Rb0SJ0T20T>0UBS2sp1X2nX2pX2xs1Y2pY2ys1a2NOS2sp1X2nX2pX2xs1Y2ys3NRXS1L3HLS2sp2lo1X2xs1Y2nY2pY2ys3SLO2X02Y03SPBS2sp1X2nX2pX2xs1Y2ys2X02Y03SPB2H32P0S2sp1X2nX2xs1Y2nY2ys2X02Y03SPBS2sp1X2nX2pX2xs1Y2nY2ys2X02Y03SPB2P0S1L3HLS2sp2lo1X2xs1Y2ys3SLO2X02Y03SPBS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL2X02Y03SPBS2sp1X2nX2pX2xs1Y2ys2X04LENX2Y03SPB2N12P0S2sp1X2xs1Y2ys3NEQ2H22H31aS2sp1X2xs1Y2ys1a2H82H9S2sp1X2xs1Y2ys1a2H93H10S2sp1X3sgX2xs1Y3sgY2ysS1L3HLS2sp2lo1X2nX2pX2xs1Y2ys3SLO3ACL2X02Y03SPB2P4S1L3HLS2sp2lo1X2nX2pX2xs1Y2ys3SLO3ACL2X02Y03SPB2P5S1L3HLS2sp2lo1X2nX2pX2xs1Y2ys3SLO3ACL2X02Y03SPB2P42P0S1L3HLS2sp2lo1X2pX2xs1Y2pY2ys3SLO3ACL3DHI2X02Y03SPB2P01a1CS2sp1X2xs1Y2ys3NEQ2H22H31aS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB1a2HaS1L3HLS2sp2lo1X2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB1a2Ha2pY2O1S2sp1X2pX2xs1Y2ys1a1CS1L3HLS2sp2lo1X2pX2xs1Y2ys3SLO3ACL3DHI2X02Y03SPB2P01a2HaS1L3HLS2sp2lo1X2pX2xs1Y2ys3SLO3ACL2X02Y03SPB2P01a1B1k1R2B02B4S1L3HLS2sp2lo1X2nX2pX2xs1Y2ys3SLO3ACL2X02Y03SPB2P42N12P0S1L3HLS2sp2lo1X2nX2pX2xs1Y2ys3SLO3ACL2X02Y03SPB2P42N12P0S2sp1X2pX2xs1Y2ysS1L2HI2sp1h2lo1X2xs1Y2ys3NEQ2H22H31aS1L2HI3HLS2sp1h2lo1X2xs1Y2pY2ys3SLO4HTOP2X02Y03SPB1a2NOS1L2HI2sp1h2lo1X2xs1Y2ys3NEQ2H22H31aS1L2HI3HLS2sp1h2lo1X2xs1Y2pY2ys3SLO4HTOP2X02Y03SPB1a2NO2H9S1L2HI3HLS2sp1h2lo1X2xs1Y2pY2ys3SLO4HTOP2X02Y03SPB1a2NO3H10S1L2HI2sp1h2lo1X2xs1Y2ys3NEQ2H22H31aS1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO2X02Y03SPB1a1CS1L2HI3HLS2sp1h2lo1X2xs1Y2ys3SLO2X02Y03SPB1a1CS1L2sp1X2nX2pX2xs1Y2ys2X02Y03SPB2P01a2Ha2H12H2S2sp1X2nX2pX2xs1Y2ys2X02Y03SPB2H32P0S2sp1X2nX2pX2xs1Y2ys2X03NRX2Y03SPB2N12P0S2sp1X2nX2pX2xs1Y2ys2X03NRX2Y03SPB2N12P0S2sp1X2pX2xs1Y3sgY2ysS2sp1X2xs1Y2nY2ys2H4S2sp1X2xs1Y2nY2ys2H32H4FFS2sp1X2nX2pX2xs1Y2pY2ys3x141HS2sp2xw3HxwS2sp1X2xw3HxwS2sp1X2nX2pX2xw3HxwS2sp1X2nX2pX2xs1Y2pY2ys3NEQ3SXY2XPS2sp1X2xs1Y2nY2pY2ys3NRY3OY0S2sp1X2xs1Y2ysS1L3HLS2sp2lo1X2nX2pX2xs1Y2ys3SLO3ACL2X02Y03SPB2P42P0S1L2sp2lo1X2nX2pX2xs1Y2ys3ACL2X02Y03SPB2P42P0FFS1L3HLS2sp2lo1X2xs1Y2ys3SLO2X02Y03SPBSS2sp1X2xs1Y2nY2pY2ys2X02Y04LENY3SPB3PYBS2sp1X2xs1Y2nY2ys2H3S2sp1X2nX2pX2xs1Y2pY2ys3NEQ3SXY2C2S2sp1X2xw3HxwS2sp1X2nX2pX2xw3HxwS2sp1X2xs1Y2nY2ys2H32H62H4S2nX2pX2H33OX'S2sp1X2nX1Y2ys1l2X04LENX2Y03SPB2H2S2sp1X2xs1Y2ys3NEQ2H22H3S2sp1X2xs1Y2nY1l2X02Y04LENY3SPB2H4S2sp1X2xs1Y2nY1l2X02Y04LENY3SPB2H3S2sp1X2xs1Y2nY2ys2X02Y03SPB2H3S2sp1X2xs1Y2nY2ys2X02Y04LENY3SPB2H31k2HkS2sp1X2xs1Y2nY2ys2X02Y04LENY3SPB2H31k2HkS1X2nX2pX2XPS1L4DIMG2sp1X2nX2pX2xs1Y2pY2ys3NEQ3XAL2X03YAL2Y03SPB2C22XP2P02P51a1H". (* [comment removed for export] *)
  Lemma body : ltac2:(CDefT.buildp (gd_tbl_P_mpi_copy ()) "Pm1,P,(;.&40.)(1<.(;.&8.))Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)P,(42.$43.R>.VX,(50.VpX,(2>.&40.VsgX,)VnX,VpadX,))P,(42.$43.R?.VY,(50.VpY,(2>.&40.VsgY,)VnY,VpadY,))P,(1?.$43.VL,VHI,Vh,VLB,R10.Vmo,)P,(5<.(44.(5:.$3.$3.)(5;.$3.$3.(29.(24.&40.Vsp,)+30.)(24.&40.Vsp,))(55.(5:.$3.$3.)))Vm,R11.)P,(5=.$43.Vm,R12.)P,(31.$43.VL,R13.)P,(30.$43.R14.)P,(28.$43.R15.Vlo,(24.&40.Vsp,))(33.$43.Vmo,(34.$43.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(3:.VdY,VdX,VLB,)Vlo,Vm,Vmo,)(36.(37.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(2>.&40.VX,)(2>.&40.VY,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(2>.&40.+1?638.)Vfc,(38.(;.&40.))R16.(39.$43.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CHX CHY HH MU WM SOK MI ST.
    flat constr:(facts) 14%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY XS. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK0. flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros HBR HAP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    unfold mpi_cells in CHX, CHY.
    flat constr:(CSEP) 6%nat. intros C1 C2 C3 C4 C5 _. cbn [dX dY md_addr md_own md_p md_n] in C1, C2, C3, C4, C5.
    flat constr:(XW) 3%nat. intros XCW XD XP. cbn [dX md_addr md_own md_p md_n] in XCW, XD, XP.
    assert (PXH : ownX = LHeap -> u32arr usegs m pX xs /\ pX + 4 * nX <= alloc_ceiling).
    { intros EO. flat constr:(MAX) 2%nat. intros FLt35 _. flat constr:(FLt35) 2%nat. flclear FLt35. intros _ FLt36. flat constr:(FLt36) 5%nat. flclear FLt36. intros _ _ _ _ OX'. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX'. rewrite EO in OX'.
      flat constr:(OX') 4%nat. flclear OX'. intros _ PIN _ PX. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5. split; [exact PX| exact P4]. }
    assert (PBY : ownY <> LNull -> bytes_at usegs m pY (u32s ys)).
    { intros ON. flat constr:(MAY) 2%nat. intros FLt37 _. flat constr:(FLt37) 2%nat. flclear FLt37. intros _ FLt38. flat constr:(FLt38) 5%nat. flclear FLt38. intros _ _ _ _ OY'. cbn [dY md_addr md_sg md_n md_p md_limbs md_pad md_own] in OY'.
      clear -OY' ON. destruct ownY; [exfalso; exact (ON eq_refl)| (flat constr:(OY') 4%nat; flclear OY'; intros _ _ _ (PB & _)); exact PB| (flat constr:(OY') 5%nat; flclear OY'; intros _ _ _ PB _); exact PB]. }
    flat constr:(MAY) 2%nat. intros FLt39 _. flat constr:(FLt39) 2%nat. flclear FLt39. intros _ FLt40. flat constr:(FLt40) 5%nat. flclear FLt40. intros _ _ _ _ OY0. cbn [dY md_addr md_sg md_n md_p md_limbs md_pad md_own] in OY0.
    assert (PYR : ownY <> LNull -> 0 <= pY /\ pY + 4 * nY <= 2^64).
    { intros ON. flat constr:((PBY ON)) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB. split; [exact PY0| lia]. }
    assert (NY0 : ownY = LNull -> nY = 0) by (intros EO; rewrite EO in OY0; lia).
    carve_frame 48%nat ST.
    lazymatch type of FR with rw_cells ?sg ?mx ?A [CB 48 ?j] =>
      set (JJ := j) in FR; clearbody JJ; change (rw_cells sg mx A ([] ++ CB 48 JJ :: [])) in FR;
      apply (rw_cells_split_CB sg mx A [] 48 JJ [] [8; 40]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
      cb8_to_c8 FR (@nil cell) end.
    (* [comment removed for export] *)
    lazymatch type of MU with ?T => change (lx_hidden T) in MU end. lazymatch type of WM with ?T => change (lx_hidden T) in WM end.
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK0).
    lx_run_tac (PLANS [0x1f698; 0x1f6c4; 0x46e44] [] 80%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    all: unfold lx_hidden in MU, WM; rewrite ?sh32m1.
    (* [comment removed for export] *)
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm : munch ?W1 ?mq mx, Hw : wmono _ ?mq' mx |- _ =>
           let MUf := fresh "MUf" in let WMf := fresh "WMf" in
           first [ assert (MUf : munch [(bv_unsigned sp - 48, bv_unsigned sp)] m mx)
                     by (eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact Hm]]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia)
                 | assert (MUf : munch [(bv_unsigned sp - 48, bv_unsigned sp); (X, X + 16)] m mx)
                     by (eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact Hm]]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia) ];
           assert (WMf : wmono usegs m mx) by (eapply wmono_trans; [exact WM| exact Hw]);
           pose proof (Asn1AuxA.HEAP_munch usegs L HI _ _ _ _ _ lo _ HH ACL Hm Hw
             ltac:(intros a Ha NO; cbn in NO; destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(dlia)) as [C|[C|C]]; [left; dlia| right; left; exact C| right; right; exact C] |]|]; left; dlia)) as HHx;
           pose proof (statics_ok_munch usegs L _ _ _ SOK Hm ltac:(intros a Ha NW; cbn; assert (O1 : ~ (X <= a < X + 16)) by (intros HX; exact (NW (XD a HX Ha))); (flsplit; repeat split); try exact I; dlia)) as SOKx;
           clear Hm Hw HH SOK
         end end.
    (* [comment removed for export] *)
    1: exfalso; flia.
    (* [comment removed for export] *)
    1: { assert (YS0 : ys = []) by (destruct ys; [reflexivity| cbn [length] in LENY; exfalso; flia]).
         assert (XS0 : xs = []) by (destruct xs; [reflexivity| cbn [length] in LENX; exfalso; flia]).
         apply aevtM_done. unfold mpi_binop_post. flexi 17%nat. exists LB, dX, 0.
         split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [apply mo_frame_refl|]. split; [reflexivity|].
         split; [exact HHx|].
         split; [eapply mpd_at_munch; [exact MAX| exact NST| exact MUf| exact WMf| cbn; split; [generalize XS; dlia| exact I]| intros EO; (flat constr:((PXH EO)) 2%nat; intros _ P4); cbn; split; [left; dlia| exact I]]|].
         split; [apply mpd_out_refl; exact NST|].
         split; [eapply heap_presx_frame; [exact MUf| exact WMf| exact HBR| exact DHI| dlia]|].
         split; [exact SOKx|].
         split; [| intros _; left; reflexivity].
         split; [| split; [reflexivity| split; [reflexivity| intros b Hb; left; exact Hb]]].
         left. split; [reflexivity|]. split; [| cbn [md_n dX dY]; dlia]. unfold mpd_val, dX, dY. cbn [md_sg md_limbs]. rewrite YS0, XS0. cbn [limbs_val]. dlia. }
    (* [comment removed for export] *)
    3: { lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
         assert (OYN : ownY <> LNull) by (intros C; pose proof (NY0 C); flia).
         assert (PBY' : bytes_at usegs m2 pY (u32s ys)) by (eapply u32ro_transport; [exact (PBY OYN)| exact MUf|]; cbn; rewrite LENY; split; [generalize (C5 OYN); dlia| exact I]).
         assert (PXH' : ownX = LHeap -> u32arr usegs m2 pX xs) by (intros EO; (flat constr:((PXH EO)) 2%nat; intros PX P5); eapply u32arr_transport; [exact PX| exact MUf| exact WMf|]; cbn; rewrite LENX; split; [left; dlia| exact I]).
         assert (PYF : pY mod 4 = 0 /\ 0 < pY).
         { flat constr:(MAY) 2%nat. intros FLtA _. flat constr:(FLtA) 2%nat. flclear FLtA. intros _ FLtB. flat constr:(FLtB) 5%nat. flclear FLtB. intros _ _ LY _ OY.
           cbn [dY md_own md_n md_p md_limbs] in OY, LY.
           destruct ownY; [exfalso; exact (OYN eq_refl)| destruct OY as (_ & PINY & PALY & _)| destruct OY as (_ & PALY & PY0' & _); split; dlia].
           flat constr:((proj1 (Forall_forall _ _) HBR _ PINY)) 5%nat. intros PY0' _ _ _ _. cbn in PY0'. split; dlia. }
         replace (Z_to_bv 64 (Z.land pY 3)) with (Z_to_bv 64 0)
           by (f_equal; change (Z.land pY 3) with (Z.land pY (Z.ones 2)); rewrite Z.land_ones by dlia; change (2 ^ 2) with 4; dlia).
         replace (Z_to_bv 64 (Z.b2z (0 <? zlow 64 pY))) with (Z_to_bv 64 1)
           by (f_equal; unfold zlow; rewrite Z.mod_small by (generalize (PYR OYN); dlia); rewrite (proj2 (Z.ltb_lt 0 pY)) by dlia; reflexivity).
         eapply (scan_loop (Z.to_nat (nY - 1)) (nY - 1)); try eassumption; try flia.
         intros k w Hk HN. exfalso. assert (HN' : nth_error ys k = None) by (apply (proj2 (nth_error_None ys k)); flia). rewrite HN' in HN. discriminate. }
    2: { lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
         assert (OYN : ownY <> LNull) by (intros C; pose proof (NY0 C); flia).
         assert (PBY' : bytes_at usegs m2 pY (u32s ys)) by (eapply u32ro_transport; [exact (PBY OYN)| exact MUf|]; cbn; rewrite LENY; split; [generalize (C5 OYN); dlia| exact I]).
         assert (PXH' : ownX = LHeap -> u32arr usegs m2 pX xs) by (intros EO; (flat constr:((PXH EO)) 2%nat; intros PX P5); eapply u32arr_transport; [exact PX| exact MUf| exact WMf|]; cbn; rewrite LENX; split; [left; dlia| exact I]).
         replace (Z_to_bv 64 (nY - 1)) with (Z_to_bv 64 (1 - 1)) by (f_equal; flia).
         assert (TI : trim_i ys 1) by (left; reflexivity).
         eapply (tail28 1); try eassumption; try flia.
         intros k w Hk HN. exfalso. assert (HN' : nth_error ys k = None) by (apply (proj2 (nth_error_None ys k)); flia). rewrite HN' in HN. discriminate. }
    (* [comment removed for export] *)
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with Hc : rw_cells _ m2 X _, Hy : rw_cells _ m2 Y _, Hf : rw_cells _ m2 (bv_unsigned sp + -48) _, Hs : stk _ m2 _ _, Hi : mem_inv _ m2 |- _ =>
      clear CHX CHY; rename Hc into CHX; rename Hy into CHY; rename Hf into FRM; rename Hs into ST2; rename Hi into MI2 end.
    assert (YS0 : ys = []) by (destruct ys; [reflexivity| cbn [length] in LENY; exfalso; flia]).
    assert (EO : ownX = LHeap).
    { flat constr:(MAX) 2%nat. intros FLt41 _. flat constr:(FLt41) 2%nat. flclear FLt41. intros _ FLt42. flat constr:(FLt42) 5%nat. flclear FLt42. intros _ _ _ _ OX'. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX'.
      clear -OX' H3 NST. destruct ownX; [exfalso; lia| reflexivity| exfalso; exact (NST eq_refl)]. }
    flat constr:((PXH EO)) 2%nat. intros PXm P4. specialize (XP EO). specialize (C2 EO).
    flat constr:(MAX) 2%nat. intros FLt43 _. flat constr:(FLt43) 2%nat. flclear FLt43. intros _ FLt44. flat constr:(FLt44) 5%nat. flclear FLt44. intros _ _ _ _ OX'. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX'. rewrite EO in OX'.
    flat constr:(OX') 4%nat. flclear OX'. intros N1 PIN PAL _.
    flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ _ P5. cbn in P0, P5.
    assert (PX : u32arr usegs m2 pX xs) by (eapply u32arr_transport; [exact PXm| exact MUf| exact WMf|]; cbn; rewrite LENX; split; [left; dlia| split; [clear -XP; lia| exact I]]).
    apply u32arr_cells in PX.
    clear MU WM ST MI FR.
    lazymatch type of MUf with ?T => change (lx_hidden T) in MUf end. lazymatch type of WMf with ?T => change (lx_hidden T) in WMf end.
    pose proof (munch_refl [(pX, pX + 4 * nX)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof U_memset_spec as SPs. unfold memset_stmt in SPs.
    eapply aevtM_cut_evt; [ exact MK0 | eapply SPs; rewrite ?unsigned_lit by dlia;
      [ replace (Z.to_nat (4 * nX)) with (4 * length xs)%nat by dlia; exact PX | assumption ] | ].
    clear SPs PX. unfold memset_post. rewrite !unsigned_lit by dlia. post_call usegs m2.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : rw_cells usegs m3 pX _ |- _ => rename H into PZ end.
    lazymatch type of PZ with ?T => change (lx_hidden T) in PZ end. unfold lx_hidden in MUf, WMf.
    assert (MU3 : munch [(bv_unsigned sp - 48, bv_unsigned sp); (X, X + 16); (pX, pX + 4 * nX)] m m3)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUf] | eapply munch_weaken; [| exact MU]]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia).
    assert (WM3 : wmono usegs m m3) by (eapply wmono_trans; [exact WMf| exact WM]).
    assert (HH3 : HEAP usegs L HI h LB m3 mo).
    { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HHx| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. right; right. exists (pX, 4 * nX). split; [exact PIN| cbn; dlia]. }
    clear MU WM MUf WMf HHx. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK3).
    lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs; unfold lx_hidden in PZ.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    unfold lx_hidden in PZ.
    lazymatch goal with Hm : munch _ m m3, Hw : wmono _ m m3, Hc : rw_cells _ m3 X _ |- _ =>
      rename Hm into MU; rename Hw into WM; clear CHX; rename Hc into CHX end.
    pose proof HH3 as HH5.
    apply aevtM_done. unfold mpi_binop_post. flexi 17%nat.
    exists LB, (mkMPD X 1 nX pX (repeat (Z_to_bv 64 0) (Z.to_nat nX)) padX LHeap), 0.
    split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [apply mo_frame_refl|]. split; [reflexivity|].
    split; [exact HH5|].
    split.
    { split; [| cbn; left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CHX|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite repeat_length; dlia|].
      split; [unfold MPI_MAX_LIMBS; dlia|]. split; [exact N1|]. split; [exact PIN|]. split; [exact PAL|].
      eapply u32arr_of_cells; [exact PZ|]. rewrite u32s_repeat0. cbn [Z.modulo]. f_equal. dlia. }
    split; [apply mpd_out_same_blocks; [reflexivity| cbn; discriminate| unfold dX; cbn [mpd_blk md_own md_p md_n]; rewrite EO; reflexivity]|].
    split.
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho |- *.
      flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _. split; [| split; [exact O1| split; [exact O2| exact I]]].
      destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia]. }
    split.
    { eapply statics_ok_munch; [exact SOK0| exact MU|]. intros a Ha NW. cbn. split; [dlia|]. split; [intros HX; exact (NW (XD a HX Ha))|]. split; [generalize P5; destruct DIMG; dlia| exact I]. }
    split; [| intros _; left; reflexivity].
    split; [| split; [reflexivity| split; [reflexivity| unfold dX; cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b Hb; left; exact Hb]]].
    left. split; [reflexivity|]. split; [| cbn [md_n dX dY]; dlia]. unfold mpd_val, dY. cbn [md_sg md_limbs]. rewrite YS0, limbs_val_repeat0. cbn [limbs_val]. dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Walk.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@D2550110198.101 D32966974175.101D36039788182.101D48794236798.103D52101733636.104D54391891673.104D65502165646.96 D772747997.96   L22704459656.3  L31378308326.94 L43061446955.92 L59310763256.4  00000I00i01M02:02g03V03b04B04M04Y05905GS2sp1X2nX2xs2nY3SPB2X02XBS1L3HLS2sp1X2xs2lo3SLO3SPB2X02XBS1L3HLS2sp1X2xs2lo3SLO3ACL3SPB2X02XBS1L3HLS2sp1X2nX2pX2xs2lo3SLO3ACL3SPB2X02XB2H1S1L3HLS2sp1X2xs2lo3SLO3ACL3DHI3SPB2X02XB1a2HaS1L2HI3HLS2sp1h1X2xs2lo3SLO4HTOP3SPB2X02XB1a2NOS2sp1X2xs2XBS1L3HLS2sp1X2xs2lo3SLO3SPB2X02XBS2sp2xw3HxwS2sp1X2xs2XBS1L3HLS2sp1X2xs2lo3SLO3SPB2X02XBS1X1Y4SEP'3EXY". (* [comment removed for export] *)
  Lemma U_mpi_copy_spec_x : mpi_copy_stmt_x usegs L HI U_MPI_COPY U_MEMSET_FUNC.
  Proof.
    unfold mpi_copy_stmt_x, U_MPI_COPY. intros until lo. intros HH MAX NST MAY SEP CSEP YCR YLCR XW ST SLO ACL HTOP SPA DHI TP MI SOK CA -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    destruct dX as [X sgX nX pX xs padX ownX]. destruct dY as [Y sgY nY pY ys padY ownY].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    destruct (Z.eq_dec X Y) as [EXY|NEQ].
    - (* [comment removed for export] *)
      assert (E : mkMPD X sgX nX pX xs padX ownX = mkMPD Y sgY nY pY ys padY ownY).
      { destruct SEP as [E|SEP']; [exact E|]. exfalso. cbn [md_addr] in SEP'. clear -SEP' EXY. lia. }
      flat constr:(MAX) 2%nat. intros FLt45 SGX. flat constr:(FLt45) 2%nat. flclear FLt45. intros CHX FLt46. flat constr:(FLt46) 5%nat. flclear FLt46. intros XAL X0 LENX NRX OX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CHX, XAL, X0, LENX, NRX, OX.
      unfold mpi_cells in CHX. unfold MPI_MAX_LIMBS in NRX.
      pose proof (rw_cells_bound _ _ _ _ CHX) as XB. cbn [cells_size csize Nat.add] in XB.
      flat constr:(XW) 3%nat. intros XCW XD XP. cbn [md_addr md_own md_p md_n] in XCW, XD, XP.
      pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(dlia) HBR DHI ACL ltac:(dlia)) as XS.
      rewrite <- EXY.
      assert (PXR : ownX = LHeap -> pX + 4 * nX <= alloc_ceiling).
      { intros EO. rewrite EO in OX. flat constr:(OX) 3%nat. flclear OX. intros _ PIN _. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros _ _ _ P4 _. cbn in P4. exact P4. }
      clear MAY SEP CSEP YCR YLCR OX.
      carve_frame 48%nat ST.
      (* [comment removed for export] *)
      assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
      lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      lazymatch goal with Hm : munch ?W1 m m5, Hw : wmono _ m m5 |- _ =>
        assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m5) by (eapply munch_weaken; [| exact Hm]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia);
        rename Hw into WM; clear Hm end.
      apply aevtM_done. unfold mpi_binop_post. flexi 17%nat. exists LB, (mkMPD X sgX nX pX xs padX ownX), 0.
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [apply mo_frame_refl|]. split; [reflexivity|].
      split. { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact ACL| exact MU| exact WM|]. intros a Ha NO. cbn in NO. left. dlia. }
      split.
      { eapply mpd_at_munch; [exact MAX| exact NST| exact MU| exact WM| cbn; split; [generalize XS; dlia| exact I]|].
        cbn [md_own md_p md_n]. intros EO. pose proof (PXR EO). cbn. split; [left; dlia| exact I]. }
      split; [apply mpd_out_refl; exact NST|].
      split; [eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| dlia]|].
      split; [eapply statics_ok_munch; [exact SOK| exact MU|]; intros a Ha NW; cbn; split; [dlia| exact I]|].
      split; [| intros _; left; reflexivity].
      split; [| cbn [md_addr md_pad]; split; [reflexivity| split; [reflexivity| intros b Hb; left; exact Hb]]].
      left. split; [reflexivity|]. split; [injection E; intros; subst; reflexivity| cbn [md_n]; dlia].
    - eapply body; try eassumption.
      + exact (proj1 (proj1 MAX)).
      + exact (proj1 (proj1 MAY)).
      + apply munch_refl.
      + apply wmono_refl.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma U_mpi_copy_spec : mpi_copy_stmt usegs L HI U_MPI_COPY U_MEMSET_FUNC.
  Proof.
    unfold mpi_copy_stmt. intros. eapply aevtM_mono; [eapply U_mpi_copy_spec_x with (dX := dX) (dY := dY) (h := h) (LB := LB) (lo := lo); eassumption|].
    intros c PO. unfold mpi_binop_post in PO |- *.
    flat constr:(PO) 22%nat. flclear PO. intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m' mo' h' LB' dX' r E PO.
    flexi 14%nat. exists m', mo', h', LB', dX', r. split; [exact E|].
    flat constr:(PO) 10%nat. flclear PO. intros P1 P2 P3 P4 P5 P6 P7 P8 P9 (P10 & _). repeat (split; [assumption|]). exact P10.
  Qed.
End CopyP.
