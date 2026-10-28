(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_init.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00d8bdbce1c2a600 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P01af8f3f93f633b8 1 1 8 3 0 1 33 1 34 1 5 2 2 28 2 32 2 35 2 36 16P01b328d6e0261d24 1 1 8 3 0 1 33 1 34 1 5 2 2 28 2 32 2 35 2 36 16P01d594794f529ff9 1 1 8 2 27 1 31 1 3 0 1 30 1 32 8P024851761c8ef128 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P02a13f99524744ea 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P02fea8857c20e9c6 1 1 8 2 27 1 31 1 3 0 1 30 1 32 8P05501b4da62d45dd 1 1 8 2 27 1 31 1 3 0 1 30 1 32 8P0551d203401be2a1 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P061bf98c02f99bca 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P0655e3f15ad094e7 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P072dfb2c94fee581 0 4 0 1 2 1 34 1 35 1P0784b34429822140 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P09ba79e9aeb6c6bc 1 1 8 2 27 1 31 1 3 0 1 30 1 32 8P0c7d35fe1f496c3a 1 1 8 2 27 1 31 1 3 0 1 30 1 32 8P0cb194d74542078b 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P0cc90b07508cd5c0 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P0da4d1f4c587ca69 0 4 0 1 2 1 34 1 35 1P1104b2dd228eda1f 1 1 8 3 0 1 33 1 34 1 5 2 2 28 2 32 2 35 2 36 16P11506faf34544603 1 1 8 3 1 1 33 1 34 1 4 2 1 32 1 35 1 36 8P115a6dcd99654a3c 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P1184916a38dc47f7 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P118a0039d155a920 1 1 8 3 1 1 33 1 34 1 4 2 1 32 1 35 1 36 8P16ecafd9f754d223 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P171fcea578227bb3 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P1741b0125a5e1957 0 4 0 1 2 1 34 1 35 1P174d11b2d60cd95d 1 1 8 3 0 1 33 1 34 1 5 2 2 28 2 32 2 35 2 36 16P184eccacb6876cef 1 1 8 3 1 1 32 1 35 1 4 2 2 33 2 34 2 36 16P19d34c49588d8bd2 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P1a2a0f7e0a3fd28d 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P1a9c80aaa091eb6f 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P1c3df8a5850ec649 1 1 8 3 0 1 33 1 34 1 5 2 2 28 2 32 2 35 2 36 16P1cbab21aaf99cbf6 1 1 8 3 1 1 32 1 35 1 4 2 2 33 2 34 2 36 16P1cef09312c3f33e6 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P1dca404fe1690085 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P1e31f31b38970b19 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P2234050e10e7db79 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P2275d8d5c7f60146 0 4 0 1 2 1 34 1 35 1P227940b785f87d0b 1 1 8 3 1 1 33 1 34 1 4 2 1 32 1 35 1 36 8P2392495dac9a663f 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P23bb019209bef6bd 1 1 8 3 1 1 33 1 34 1 4 2 1 32 1 35 1 36 8P23d82717dd31cfcf 1 1 8 3 1 1 33 1 34 1 4 2 1 32 1 35 1 36 8P25f0835fda2e80ce 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P26ddd92ab8ac6449 1 1 8 3 1 1 32 1 35 1 4 2 2 33 2 34 2 36 16P2793d4cf1f36929d 0 4 0 1 2 1 34 1 35 1P2c82bfd8f7d7ab57 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P2d28b9eec0dc3ce6 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P2db4f0b0cd485924 0 4 0 1 26 1 30 1 31 1P322f058d939106aa 1 1 8 3 0 1 33 1 34 1 5 2 2 28 2 32 2 35 2 36 16P32a2094fe50e5709 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P334c4d03f866fa3c 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P35403f26a163f87f 1 1 8 3 0 1 33 1 34 1 5 2 2 28 2 32 2 35 2 36 16P356654b3afb32144 0 4 0 1 2 1 34 1 35 1P35796ca5ede779d7 2 26 1 1 8 3 2 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 1 1 32 1 35 1 4 0 2 33 2 34 2 36 16P36384ae4c1c6e740 1 1 8 3 1 1 32 1 35 1 4 2 2 33 2 34 2 36 16P38ca622be2fbe072 1 1 8 3 1 1 32 1 35 1 4 2 2 33 2 34 2 36 16P3970b6f0a4961530 0 4 0 1 2 1 34 1 35 1P398a713d7324370a 1 1 8 2 27 1 31 1 3 0 1 30 1 32 8P399690605a96778b 1 1 8 2 27 1 31 1 3 0 1 30 1 32 8P3a67c1787c9bdbee 1 1 8 3 1 1 32 1 35 1 4 2 2 33 2 34 2 36 16P3bfff36306f8f48c 1 1 8 3 1 1 33 1 34 1 4 2 1 32 1 35 1 36 8P3c0bf38c0b7cf82a 1 1 8 3 1 1 33 1 34 1 4 2 1 32 1 35 1 36 8P3caa344e7e7c0183 2 26 1 1 8 3 1 1 33 1 34 1 5 0 1 28 1 32 1 35 1 36 8 1 1 8 3 2 1 32 1 35 1 4 0 2 33 2 34 2 36 16P3f43b9ae53e07a36 1 1 8 3 1 1 32 1 35 1 4 2 2 33 2 34 2 36 16N006b5b95156b6be3N00b92d8110414fdeN01974e070af49b0fN02043a93b5014fdbN02302218321f531dN063418e4c5e388edN07e4b0b70de9d627N099200dc4d4d48f0N1144ed9c0e98e6d6N12b86f6ed135d504N136209dc79968430N16291bd3cab3602cN219981222fda0c9dN276408f3d0344fcbN29dde573f8c8d759N2fd4ecd97cc4b0f4N2ff858e7a9a6d8e0N300ad0237d832f36N35b16ed1a63b1fafN35bfe915351c928dN39a2bc9c2933b61aN3b605ab0c1af1068N3c5951096f6fbfd2N3f5a4bc2cbb0b406"%lxh.
Ltac2 gd_tbl_P_ecp_group_init () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_GROUP_SIZE"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_init"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "ecp_group_init_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].


Definition U_ECP_GROUP_INIT : Z := 0x383e4.
Notation ECP_GROUP_INIT_STACK := 16 (only parsing).

Definition ecp_group_init_post (segs : list Segment) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (LB : list blk) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_init ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lidpad,(2.&40.)(1.(2.&40.)LpP,(2.&40.)(1.(2.&40.)LpA,(2.&40.)(1.(2.&40.)LpB,(2.&40.)(1.(2.&40.)LpX,(2.&40.)(1.(2.&40.)LpY,(2.&40.)(1.(2.&40.)LpZ,(2.&40.)(1.(2.&40.)LpN,(2.&40.)(1.(2.&40.)Lhpad,(2.&40.)(4.(5.$0.R1:.(6.(7.O16.O15.O14.O13.R19.R18.R17.O12.O11.R16.R15.R14.R13.R12.R11.R10.R?.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R>.R=.R<.R;.)O6.(8.O16.)O5.(9.(2.&40.))R:.(:.O18.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.O4.(10.O4.$11.))(<.(=.$>.$>.)(?.$>.$>.(12.(13.&40.O15.)+10.)(13.&40.O15.))(14.(=.$>.$>.))))O1.R:.)(4.(15.O18.O1.R:.)(4.(16.O18.R:.)(4.(17.O18.O17.R:.O3.O4.(18.O4.R9.R8.R7.R6.R5.R4.R3.R2.R1.))(19.O18.R:.O2.(13.&40.O15.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_group_init_stmt (segs : list Segment) (MT : list modp_ent) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_init ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$>.Plo,$>.PLB,(1;.$1<.)Pjunk,(1;.(2.&8.))P,(1=.O3.R5.R4.(<.$1>.(1?.#<0.R1.)(14.$1>.)))P,(5.$>.(20.R5.+8.)=)P,(21.=R6.)P,(19.O3.R8.R6.(13.&40.R28.))P,(22.R7.(12.(13.&40.R29.)+10.))P,(5.$>.(20.(13.&40.R2:.)+10.)=)P,(23.(22.(10.R:.$11.)R9.)(22.(13.&40.R2;.)R:.))P,(16.O3.R<.)P,(5.$>.(20.(13.&40.R2>.)+2.)=)P,(5.(2.&40.)R26.(24.&40.R=.))(25.O3.(26.O3.O2.R30.R2?.R2>.R2=.R29.R28.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R11.R10.R>.R<.R=.R?.)(6.(7.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(24.&40.O1.)R10.(9.(2.&40.))R?.(:.O3.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma ecp_group_at_init : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_init ()) "Psegs,(1;.$27.)PMT,(1;.$28.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(1;.$1<.)PA,$>.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)P,(1=.R>.R<.R:.(<.$1>.(29.(24.&40.=))(<.$1>.(29.R9.)(14.$1>.))))P,(5.$>.(20.R;.+8.)=)P,(21.=R<.)P,(1=.R11.R?.(10.R=.+8.)(2:.=(24.&40.+1.)=R;.))P,(1=.R12.R10.(10.R>.+18.)(2:.=(24.&40.+1.)=R;.))P,(1=.R13.R11.(10.R?.+28.)(2:.=(24.&40.+1.)=R;.))P,(1=.R14.R12.(10.R10.+38.)(2:.=(24.&40.+1.)=R;.))P,(1=.R15.R13.(10.R11.+48.)(2:.=(24.&40.+1.)=R;.))P,(1=.R16.R14.(10.R12.+58.)(2:.=(24.&40.+1.)=R;.))P,(1=.R17.R15.(10.R13.+68.)(2:.=(24.&40.+1.)=R;.))P,(1=.R18.R16.(10.R14.+78.)(<.$1>.(2;.(24.&40.=))(<.$1>.(2;.(24.&40.=))(<.$1>.(29.(24.&40.=))(<.$1>.(29.R;.)(<.$1>.(2;.(24.&40.=))(<.$1>.(2;.(24.&40.=))(<.$1>.(2;.(24.&40.=))(<.$1>.(2;.(24.&40.=))(<.$1>.(2;.(24.&40.=))(<.$1>.(2;.(24.&40.=))(14.$1>.))))))))))))(17.R19.R18.R17.R16.R15.(18.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.))")
(* [comment removed for export] *).
Proof.
  intros until hpad. intros HD AL POS HP HA HB HX HY HZ HN HT.
  unfold ecp_group_at, grp_init, ecp_point_at, pt_init; cbn -[mpdr_at rw_cells Z.pow Z.add Z.mul Z.le Z.lt].
  refine (conj HD (conj AL (conj POS _))).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply mpdr_at_init; [exact HP| lia| lia]|]. split; [apply mpdr_at_init; [exact HA| lia| lia]|]. split; [apply mpdr_at_init; [exact HB| lia| lia]|].
  split. { split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
           replace (A + 56 + 16) with (A + 72) by lia. replace (A + 56 + 32) with (A + 88) by lia.
           split; [apply mpdr_at_init; [exact HX| lia| lia]|]. split; [apply mpdr_at_init; [exact HY| lia| lia]|]. apply mpdr_at_init; [exact HZ| lia| lia]. }
  split; [apply mpdr_at_init; [exact HN| lia| lia]|]. split; [exact HT|].
  repeat (split; [lia|]).
  split. { unfold grp_free_mpds; cbn. repeat constructor; cbn; discriminate. }
  split. { unfold grp_kept_mpds; cbn. constructor. }
  left. reflexivity.
Qed.

Lemma U_ecp_group_init_spec : forall MT, ecp_group_init_stmt usegs MT U_ECP_GROUP_INIT.
Proof.
  intros MT.
  unfold ecp_group_init_stmt, U_ECP_GROUP_INIT.
  intros until junk.
  intros HG AL POS ST LO SPA SX MI RA ->.
  unfold ECP_GROUP_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (rw_cells_bound _ _ _ _ HG) as GB.
  cbn [cells_size csize Nat.add] in GB.
  destruct (grp_chunks_of_bytes _ _ _ _ HG) as (HD & S1 & S2 & S3 & S4 & S5 & S6 & S7 & HT).
  clear HG.
  apply mpi_cells_of_bytes in S1.
  apply mpi_cells_of_bytes in S2.
  apply mpi_cells_of_bytes in S3.
  apply mpi_cells_of_bytes in S4.
  apply mpi_cells_of_bytes in S5.
  apply mpi_cells_of_bytes in S6.
  apply mpi_cells_of_bytes in S7.
  pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold mpi_cells in S1, S2, S3, S4, S5, S6, S7.
  carve_frame 16%nat ST.
  lxp_split_frame [8;8]%nat. lxp_seps 16.
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [] [] 64%N SUMS1).
  lxp_ret.
  all: try (eapply ecp_group_at_init; lxp_apply_post).
Qed.
