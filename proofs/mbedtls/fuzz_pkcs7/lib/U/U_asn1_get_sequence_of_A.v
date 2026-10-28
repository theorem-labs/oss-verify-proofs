(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPHeap. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsHeap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02358c8bb05daf4b 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P0436effa2a288879 0 2 0 1 35 1P05155c005e953f0b 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P05dc26e938313446 2 38 0 6 0 1 3 1 40 1 41 1 51 1 52 1 0 4 0 1 2 1 51 1 52 1P0632d1aad4f01bb6 1 1 16 3 0 1 49 1 50 1 7 1 1 36 1 37 1 38 1 48 1 51 1 52 16P065a7478d8d1df8e 3 5 0 1 1 1 0 4 0 16 1 16 50 16 51 16 0 4 0 16 2 16 50 16 51 16P08fdf1e17a0d202a 2 34 0 6 0 1 1 1 39 1 40 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P0c548893c45b96e6 2 39 0 6 0 1 1 1 39 1 40 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P0ce90c9ca994bc6e 0 2 0 1 2 1P0d108a254402328e 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P0fd863db563fffb7 2 40 0 6 0 1 2 1 39 1 40 1 50 1 51 1 0 4 0 1 1 1 50 1 51 1P1056c60f0f8139fe 1 2 16 2 0 1 48 1 16 2 2 1 49 1 2 50 1 51 1P1393d9d770de18ab 0 4 0 16 1 16 46 16 47 16P13a21f26817e71a2 2 39 0 6 0 1 1 1 39 1 40 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P15aa67a6fdf168e8 2 34 0 6 0 1 1 1 39 1 40 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P1840ef6a9c418082 0 5 0 1 37 1 38 1 48 1 49 1P19a5b3082bb01dce 3 4 0 1 1 1 0 4 0 16 1 16 50 16 51 16 0 4 0 16 2 16 50 16 51 16P1cfaef64ebd494ae 3 5 0 1 1 1 0 4 0 16 1 16 50 16 51 16 0 4 0 16 2 16 50 16 51 16P206bac33ca626d50 2 34 0 6 0 1 1 1 39 1 40 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P21a4cf55faf936cb 0 4 0 1 23 1 46 1 47 1P2262431a9b716a46 3 4 0 1 1 1 0 4 0 16 1 16 50 16 51 16 0 4 0 16 2 16 50 16 51 16P22a2df3853ee2f2b 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P233ef9a9da74753b 1 1 16 3 1 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P2467a7aacadc7e57 0 2 0 1 1 1P24ccbb9abb6c66b9 3 4 0 1 1 1 0 4 0 16 1 16 50 16 51 16 0 4 0 16 2 16 50 16 51 16P261da952cbf85add 1 1 16 3 0 1 49 1 50 1 7 1 1 36 1 37 1 38 1 48 1 51 1 52 16P2c192a5e0a6d540d 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P2c1fc67cd8ce0a64 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P2c3d2648f70ca1e4 2 39 0 6 0 1 1 1 39 1 40 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P2edf6e695809032e 0 4 0 1 25 1 48 1 49 1P30c489178304f103 3 5 0 1 1 1 0 4 0 16 1 16 50 16 51 16 0 4 0 16 2 16 50 16 51 16P317226b636b49bd8 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P34655a769fa993e7 3 4 0 1 1 1 0 4 0 16 2 16 50 16 51 16 0 4 0 16 1 16 50 16 51 16P36534cf5f69fa03f 1 1 16 2 2 1 49 1 3 0 1 48 1 50 16P377887cb64ae7dc6 0 2 0 1 34 1P37b33f5c9ea28ee5 2 39 0 6 0 1 2 1 39 1 40 1 50 1 51 1 0 4 0 1 1 1 50 1 51 1P37f6d29042c3837f 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P38dc1d613cd330b8 0 4 0 1 36 1 46 1 47 1P3bd26b0a39682434 1 1 16 3 0 1 50 1 51 1 7 2 1 37 1 38 1 39 1 49 1 52 1 53 16P3f122e2747750f84 0 8 0 16 1 16 30 16 36 16 37 16 38 16 48 16 49 16N0586f87ee2b1925eN072c2fb6060456dbN0bbae79ac3679357N0d622b8ff4ba58b7N0d6abf6b44bc637bN10fe890bdbad0dc3N137438cf75a7fce5N14df2765029f83adN15e647303786dcf6N1780b204c326a66cN1855839d4da282ddN195333e5adb1c115N1996533d7553900eN1a40db790a40571fN1c5189119bb03e89N1c5e8247f45dd9bfN1e4783392adc5844N1e96c9588a053416N1f3c4b8a6906b6bdN22598cf8bdc746e9N2289b25a4c9af802N2a72f10f198b0230N2ace04c72716be7eN2d1c2d31ec99ea96N2d872b71a96bcf1bN2efe2ff6bfae81f0N328a50b35d85c2c1N32d65769d4e02696N32e664b6fc06b22cN344a35f03cde1e9fN36e03263061278b7N378819343e928bf7N38f9b3ff3c596d12N396c524e82aecd18N3dd0978082f3f803"%lxh.
Ltac2 gd_tbl_P_asn1_get_sequence_of_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.hd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.seq_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.rev"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "asn1_get_sequence_of_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Walk.LBof"; "Walk.fresh"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_lseg"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Stdlib.Lists.List.last"; "Walk.inv"; "Walk.cb_post"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"].


Definition U_ASN1_GET_SEQUENCE_OF : Z := 0x1ecc4.
Definition U_CALLOC : Z := 0x3f960.

Definition asn1_get_sequence_of_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1?.O1>.O1=.)Lh',(5.O1?.O1>.O1=.)(1.$6.Lr,$6.(1.$6.Lp',$6.(1.(2.&40.)Lct,(2.&40.)(1.(2.&40.)Lcpad,(2.&40.)(1.$6.Lcl,$6.(1.$6.Lcp,$6.(1.$6.Lcn,$6.(1.(7.$6.)Lnodes,(7.$6.)(8.(9.$0.R1;.(:.(;.(<.O1<.O1;.O1:.O19.R1:.R19.R18.O18.O17.R17.R16.R15.R14.R13.R12.R11.R10.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R?.R>.R=.R<.)O<.(=.O1<.)O;.(>.(2.&40.))R;.(?.O1?.))R:.))(8.(10.O1?.R;.)(8.(11.O1?.R;.O3.(12.&40.O1;.))(8.(13.O1.R:.)(8.(9.$6.(14.O1?.O1>.O1=.R9.)(14.O1?.O1>.O1=.O:.))(8.(9.(2.&40.)R17.(15.&40.R8.))(8.(8.(16.-7?.R8.)(17.R8.=))(8.(18.O1?.R;.O8.(19.$1:.(1;.(15.&40.R7.))(1<.$1:.)))(8.(8.(17.O6.R7.)(17.R7.O5.))(8.(18.O1?.R;.O7.(1=.R6.R5.R4.R3.R2.))(8.(1>.(8.(9.$6.R3.=)(8.(9.$6.R4.=)(9.(7.$6.)R1.(1<.$6.))))(8.(17.O4.R3.)(8.(17.=R4.)(17.(1?.R3.R4.)O5.))))(8.(9.$6.R2.(20.$6.=R1.))(8.(21.O1?.L,(7.$1:.)$22.R;.(23.(24.$6.$6.)(25.$6.(24.$6.$6.)La,$6.(26.$6.$6.R1.+20.)(27.$6.R1.))O9.)R2.R1.)(8.(28.$6.R1.)(8.Px,$6.P,(29.$6.R1.R2.)PB,$6.Pk,$6.P,(29.(24.$6.$6.)(26.$6.$6.R2.R1.)O9.)(1>.(17.(1?.R5.+20.)R3.)(17.(1?.R3.R2.)R5.))(8.(2:.O1?.O1>.O1=.R9.(23.(24.$6.$6.)(25.$6.(24.$6.$6.)La,$6.(26.$6.$6.R1.+20.)(27.$6.R1.))O9.)R;.R:.)(2;.O1?.O1>.O9.(12.&40.O1;.)(19.(24.$6.$6.)(26.$6.$6.O8.(1?.O8.+8.))(19.(24.$6.$6.)(26.$6.$6.O7.(1?.O7.+20.))(1<.(24.$6.$6.))))O2.R;.)))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_sequence_of_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O4.O3.O2.)PLB,(7.$2=.)PPP,$6.PCUR,$6.PP,$6.PEND,$6.PBUF,$6.Plo,$6.Ptag,$6.Pbs,(7.(2.&8.))Pcjunk,(7.(2.&8.))P,(2:.O4.O3.O2.R;.R:.R=.R<.)P,(18.O4.R>.R:.(19.$1:.(1;.(15.&40.R8.))(1<.$1:.)))P,(18.O4.R?.R:.(19.$1:.(2>.#20.R3.)(1<.$1:.)))P,(2?.O4.R10.R8.R5.)P,(17.R9.R;.)P,(17.R<.R;.)P,(17.R<.(1?.R;.(30.(31.(2.&8.)R8.))))P,(16.(1?.R<.(30.(31.(2.&8.)R9.)))(32.+2.+3?.))P,(1>.(17.(1?.R11.+8.)R10.)(17.(1?.R10.+20.)R11.))P,(1>.(17.(1?.R12.+8.)R>.)(17.(1?.R>.(30.(31.(2.&8.)R;.)))R12.))P,(1>.(17.(1?.R12.+20.)R?.)(17.(1?.R?.(30.(31.(2.&8.)R<.)))R12.))P,(9.$6.(33.R14.+8.)=)P,(9.$6.(33.R14.+8.)=)P,(16.=R16.)P,(16.=R16.)P,(16.=R14.)P,(11.O4.R1=.R14.(12.&40.R3=.))P,(17.R15.(34.(34.(12.&40.R3>.)+;0.)(35.O3.)))P,(17.(36.O3.)R16.)P,(17.(12.&40.R40.)(14.O4.O3.O2.R1>.))P,(9.$6.(33.(12.&40.R41.)+10.)=)P,(17.(37.O3.)(36.O3.))P,(17.(38.O3.)(39.O3.))P,(17.(37.O3.)(3:.O3.))P,(1>.(17.(1?.R21.+8.)R1<.)(17.(12.&40.R45.)R21.))P,(1>.(17.(1?.R21.+20.)R1=.)(17.(12.&40.R46.)R21.))P,(1>.(17.(1?.R1?.(30.(31.(2.&8.)R1<.)))R1>.)(17.(12.&40.R47.)R1?.))P,(3;.O3.R25.R1?.(14.O4.O3.O2.R26.)R24.+8.)P,(3;.O3.R26.R20.(14.O4.O3.O2.R27.)R24.+20.)P,(3<.O3.R27.R21.R22.(30.(31.(2.&8.)R1?.)))P,(9.(2.&40.)R49.(15.&40.(3=.O3.)))P,(10.O4.R2<.)P,(9.(2.&40.)R45.(15.&40.R29.))P,(9.(2.&40.)R45.(15.&40.R27.))P,(9.(2.&40.)R45.(15.&40.R2:.))P,(9.(2.&40.)R45.(15.&40.R26.))(3>.O4.R30.(3?.O4.O3.O2.R52.R51.R50.R4?.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R33.R32.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R31.R30.)(;.(<.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(15.&40.O1.)R32.(>.(2.&40.))R31.(?.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk)
            (PP CUR P END BUF lo tag : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : CUR + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis CURB : 0 <= CUR /\ CUR + 32 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CUR mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < CUR.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 176 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CUR + 32 <= lo \/ bv_unsigned sp <= CUR.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
  Hypothesis CWCUR : client_wrange L LB lo (heap_top usegs L HI h) CUR 32.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (asn1_get_sequence_of_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation CTX := (bv_unsigned sp + -24).
  (* [comment removed for export] *)
  Notation SPG := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SPT := (Z_to_bv 64 (bv_unsigned sp + -128)).

  Definition LBof (nodes : list Z) : list blk := map (fun a => (a, 32)) (rev nodes) ++ LB.

  (* [comment removed for export] *)
  Definition fresh (nodes : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "Px,$6.P,(29.$6.R1.O1.)(8.(17.(1?.R2.+20.)(36.VL,))(8.(1>.(17.(1?.R2.+20.)(38.VL,))(17.(3:.VL,)R2.))PB,$6.Pk,$6.P,(29.(24.$6.$6.)(26.$6.$6.R2.R1.)VLB,)(1>.(17.(1?.R5.+20.)R3.)(17.(1?.R3.R2.)R5.))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition inv (mm : mem) (moc : Model) (hc : HST usegs L HI) (nodes : list Z)
             (ct cpad : word) (cl cp : Z) (tagw zpad : word) (j0 j1 : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "(8.(2:.$40.VL,VHI,O:.(41.O9.)O<.O;.)(8.(9.$6.(14.$40.VL,VHI,O:.)(14.$40.VL,VHI,Vh,))(8.(28.$6.O9.)(8.(42.O9.)(8.(43.$40.O<.(41.O9.)VBUF,VEND,O9.=)(8.(18.$40.O<.VCUR,(1=.O8.O7.O6.O5.(20.$6.=O9.)))(8.(1>.(8.(9.$6.O5.=)(8.(9.$6.O6.=)(9.(7.$6.)O9.(1<.$6.))))(8.(17.VBUF,O5.)(8.(17.=O6.)(17.(1?.O5.O6.)VEND,))))(8.(18.$40.O<.(1?.(12.&40.Vsp,)-20.)(19.$1:.(2>.#8.O2.)(19.$1:.(44.O4.)(19.$1:.(44.O3.)(19.$1:.(1;.(15.&40.(45.$6.O9.VCUR,)))(19.$1:.(1;.Vra,)(1<.$1:.)))))))(8.(18.$40.O<.(1?.(12.&40.Vsp,)-80.)(19.$1:.(2>.#8.O1.)(19.$1:.(1;.Vs9,)(19.$1:.(1;.Vs8,)(19.$1:.(1;.Vs7,)(19.$1:.(1;.Vs6,)(19.$1:.(1;.Vs5,)(19.$1:.(1;.Vs4,)(19.$1:.(1;.Vs3,)(19.$1:.(1;.Vs2,)(19.$1:.(1;.Vs1,)(19.$1:.(1;.Vs0,)(19.$1:.(1;.(15.&40.+1>=08.))(1<.$1:.))))))))))))))(8.(11.$40.O<.Vlo,(1?.(12.&40.Vsp,)-80.))(8.(10.$40.O<.)(8.(2?.$40.O<.VBUF,Vbs,)(8.(2;.$40.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))Vm,O<.)(13.Vmo,O;.))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition cb_post (p : Z) (j1 : list byte) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 : word) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "Lc,$0.(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lx28,(2.&40.)(1.(2.&40.)Lx29,(2.&40.)(1.(2.&40.)Lx30,(2.&40.)(1.(2.&40.)Lx31,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.$4.Lmoc,$4.(1.(5.$40.VL,VHI,)Lhc,(5.$40.VL,VHI,)(1.(7.$6.)Lnodes,(7.$6.)(1.(2.&40.)Lct,(2.&40.)(1.(2.&40.)Lcpad,(2.&40.)(1.$6.Lcl,$6.(1.$6.Lcp,$6.(1.(2.&40.)Ltagw,(2.&40.)(1.(2.&40.)Lzpad,(2.&40.)(1.(7.(2.&8.))Lj0,(7.(2.&8.))(1.$6.Lr,$6.(8.(9.$0.R1<.(:.(;.(<.(15.&40.+1>;48.)(15.&40.(1?.(12.&40.Vsp,)-80.))Vgp,Vtp,R1;.R1:.R19.O:.O9.R18.R17.R16.R15.R14.R13.R12.R11.O8.O7.O6.O5.O4.O3.O2.O1.Vs10,Vs11,R10.R?.R>.R=.)VF,(15.&40.+1>;48.)Vfc,(>.(2.&40.))R<.(?.$40.))R;.))(8.(9.(2.&40.)R18.(15.&40.R1.))(8.(1>.(9.$6.R1.=)(9.$6.R1.-6:.))(8.(46.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.O;.)(18.$40.R<.VPP,(19.$1:.(1;.(15.&40.O<.))(1<.$1:.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma inv_intro : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$40.VL,VHI,)Pnodes,(7.$6.)Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Ptagw,(2.&40.)Pzpad,(2.&40.)Pj0,(7.(2.&8.))Pj1,(7.(2.&8.))P,(2:.$40.VL,VHI,R:.(41.R9.)R<.R;.)P,(9.$6.(14.$40.VL,VHI,R;.)(14.$40.VL,VHI,Vh,))P,(28.$6.R;.)P,(42.R<.)P,(43.$40.R10.(41.R=.)VBUF,VEND,R=.=)P,(18.$40.R11.VCUR,(1=.R=.R<.R;.R:.(20.$6.=R>.)))P,(1>.(8.(9.$6.R;.=)(8.(9.$6.R<.=)(9.(7.$6.)R?.(1<.$6.))))(8.(17.VBUF,R;.)(8.(17.=R<.)(17.(1?.R;.R<.)VEND,))))P,(18.$40.R13.(1?.(12.&40.Vsp,)-20.)(19.$1:.(2>.#8.R9.)(19.$1:.(44.R;.)(19.$1:.(44.R:.)(19.$1:.(1;.(15.&40.(45.$6.R10.VCUR,)))(19.$1:.(1;.Vra,)(1<.$1:.)))))))P,(18.$40.R14.(1?.(12.&40.Vsp,)-80.)(19.$1:.(2>.#8.R9.)(19.$1:.(1;.Vs9,)(19.$1:.(1;.Vs8,)(19.$1:.(1;.Vs7,)(19.$1:.(1;.Vs6,)(19.$1:.(1;.Vs5,)(19.$1:.(1;.Vs4,)(19.$1:.(1;.Vs3,)(19.$1:.(1;.Vs2,)(19.$1:.(1;.Vs1,)(19.$1:.(1;.Vs0,)(19.$1:.(1;.(15.&40.+1>=08.))(1<.$1:.))))))))))))))P,(11.$40.R15.Vlo,(1?.(12.&40.Vsp,)-80.))P,(10.$40.R16.)P,(2?.$40.R17.VBUF,Vbs,)P,(2;.$40.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))Vm,R18.)P,(13.Vmo,R18.)(46.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)")
(* [comment removed for export] *).
  Proof. intros. unfold inv. repeat (split; [assumption|]). assumption. Qed.
  Lemma cb_post_intro : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "Pp,$6.Px8,(2.&40.)Px9,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$40.VL,VHI,)Pnodes,(7.$6.)Pct,(2.&40.)Pcpad,(2.&40.)Pcl,$6.Pcp,$6.Ptagw,(2.&40.)Pzpad,(2.&40.)Pj0,(7.(2.&8.))Pj1,(7.(2.&8.))Pr,$6.P,(1>.(9.$6.R1.=)(9.$6.R1.-6:.))P,(46.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(18.$40.R?.VPP,(19.$1:.(1;.(15.&40.R28.))(1<.$1:.)))(47.R29.R5.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.(:.(;.(<.(15.&40.+1>;48.)(15.&40.(1?.(12.&40.Vsp,)-80.))Vgp,Vtp,R1>.R1=.R1<.R28.R27.(15.&40.R4.)R1;.R1:.R19.R18.R17.R16.R15.R26.R25.R24.R23.R22.R21.R20.R1?.Vs10,Vs11,R14.R13.R12.R11.)VF,(15.&40.+1>;48.)Vfc,(>.(2.&40.))R10.(?.$40.))R?.))")
(* [comment removed for export] *).
  Proof.
    intros * Hr Hinv Hpp. unfold cb_post. flexi 15%nat. exists mm, moc, hc, nodes, ct, cpad, cl, cp, tagw, zpad, j0, r.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hr|]. split; [exact Hinv| exact Hpp].
  Qed.

  (* [comment removed for export] *)
  Lemma presx_munch : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "PW,(7.$48.)Pmm,P,(2.&40.)(3.(2.&8.))Pm1,P,(2.&40.)(3.(2.&8.))P,(49.R3.R2.R1.)P,(4:.$40.R3.R2.)P,Pa,$6.P,(8.(17.=R1.)(16.R1.(32.+2.+40.)))P,(1>.(17.(12.&40.Vsp,)R2.)(1>.(8.(17.(39.VL,)R2.)(16.R2.(37.VL,)))(4;.VLB,R2.)))P,(4<.(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))R3.)(4<.R9.R4.)(2;.$40.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))R5.R4.)")
(* [comment removed for export] *).
  Proof.
    clear. intros W mm m1 MU WM HW. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. apply HW; [exact Ha| | exact Ho].
    destruct Hc as [Hs|[[Hd1 Hd2]|Hb]]; [left; exact Hs| right; left; lia| right; right; exact Hb].
  Qed.

  Lemma in_block_below : forall a, in_block LB a -> a < alloc_ceiling.
  Proof.
    clear -HBR0. intros a (b & Hb & Hr). rewrite Forall_forall in HBR0. flat constr:((HBR0 b Hb)) 5%nat. intros _ _ _ Hc _. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HCALLOC => idtac | B1 => idtac | B3 => idtac | B4 => idtac | D1 => idtac | D2 => idtac | D3 => idtac | PPB => idtac | CURB => idtac | AL1 => idtac | AL2 => idtac | NZ1 => idtac | NZ2 => idtac | NZ3 => idtac | SLO => idtac | HLS => idtac | ACL => idtac | ACP => idtac | HTOP => idtac | SPA => idtac | DHI => idtac | DIM1 => idtac | DIM2 => idtac | DS1 => idtac | DS2 => idtac | DS3 => idtac | CWPP => idtac | CWCUR => idtac | CRBUF => idtac | TP => idtac | SPB => idtac | HBR0 => idtac end.
  Lemma cb_alloc_head : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_A ()) "Pp,$6.Pq,$6.Ptb,$6.PLw,(2.&40.)Pct,(2.&40.)Pcpad,(2.&40.)Ptagw,(2.&40.)Pzpad,(2.&40.)Pcl,$6.Pcp,$6.Pj0,(7.(2.&8.))Pj1,(7.(2.&8.))Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px10,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Px25,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$40.VL,VHI,)P,(2:.$40.VL,VHI,R1.(41.(1<.$6.))R3.R2.)P,(9.$6.(14.$40.VL,VHI,R2.)(14.$40.VL,VHI,Vh,))P,(18.$40.R5.VCUR,(1=.R24.R23.R20.R1?.=))P,(8.(17.VBUF,R20.)(8.(17.=R21.)(17.(1?.R20.R21.)VEND,)))P,(18.$40.R7.(1?.(12.&40.Vsp,)-20.)(19.$1:.(2>.#8.R20.)(19.$1:.(44.R24.)(19.$1:.(44.R23.)(19.$1:.(1;.(15.&40.VCUR,))(19.$1:.(1;.Vra,)(1<.$1:.)))))))P,(18.$40.R8.(1?.(12.&40.Vsp,)-80.)(19.$1:.(2>.#8.R20.)(19.$1:.(1;.Vs9,)(19.$1:.(1;.Vs8,)(19.$1:.(1;.Vs7,)(19.$1:.(1;.Vs6,)(19.$1:.(1;.Vs5,)(19.$1:.(1;.Vs4,)(19.$1:.(1;.Vs3,)(19.$1:.(1;.Vs2,)(19.$1:.(1;.Vs1,)(19.$1:.(1;.Vs0,)(19.$1:.(1;.(15.&40.+1>=08.))(1<.$1:.))))))))))))))P,(18.$40.R9.(1?.(12.&40.Vsp,)-;0.)(19.$1:.(1;.R14.)(19.$1:.(1;.R15.)(19.$1:.(1;.R16.)(19.$1:.(1;.R1<.)(19.$1:.(1;.R1=.)(19.$1:.(1;.(15.&40.+1>;48.))(1<.$1:.))))))))P,(11.$40.R:.Vlo,(1?.(12.&40.Vsp,)-;0.))P,(10.$40.R;.)P,(2?.$40.R<.VBUF,Vbs,)P,(2;.$40.VL,VLB,(12.&40.Vsp,)(19.(24.$6.$6.)(26.$6.$6.VPP,(1?.VPP,+8.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(1<.(24.$6.$6.))))Vm,R>.)P,(49.(19.(24.$6.$6.)(26.$6.$6.(34.(12.&40.Vsp,)+;0.)(34.(12.&40.Vsp,)+80.))(19.(24.$6.$6.)(26.$6.$6.VCUR,(1?.VCUR,+20.))(19.(24.$6.$6.)(26.$6.$6.(34.(12.&40.Vsp,)+20.)(12.&40.Vsp,))(1<.(24.$6.$6.)))))R?.R>.)P,(4:.$40.R10.R?.)P,(13.Vmo,R?.)P,(18.$40.R11.VPP,(19.$1:.(1;.(15.&40.R34.))(1<.$1:.)))P,(17.VBUF,R34.)P,(17.(1?.R35.(12.&40.R33.))VEND,)P,(8.(17.=R35.)(16.R35.+100.))(3>.$40.R14.(47.R38.R2=.R29.R28.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)(;.(<.(15.&40.+1>;48.)(15.&40.(1?.(12.&40.Vsp,)-;0.))Vgp,Vtp,R2<.R2;.R2:.(15.&40.R37.)R35.R27.(15.&40.R36.)(15.&40.R37.)R35.R26.R25.R24.R23.(15.&40.(1?.(12.&40.Vsp,)-18.))(15.&40.R36.)(15.&40.VCUR,)R1?.R1>.R1=.R1<.R1;.Vs10,Vs11,R1:.R19.R18.R17.)VF,(15.&40.+1>=64.)Vfc,(>.(2.&40.))R15.(?.$40.)))")
(* [comment removed for export] *).
  Proof.
    (* [comment removed for export] *)
    intros p q tb Lw ct cpad tagw zpad cl cp j0 j1 x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm0 mm moc hc
      HH HT HCUR HBUFOK FRG FRT FR ST MI HBUF HPX MU WM MF HPP Hq HqL Htb.
    clear AL1 AL2 NZ1 NZ2 B1.   (* [comment removed for export] *)
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    assert (HTOPc : bv_unsigned sp <= heap_top usegs L HI hc) by (rewrite HT; exact HTOP).
    unfold seq_cells in HCUR. change (LBof []) with LB in HH.
    pose proof CWCUR as CWc. rewrite <- HT in CWc. pose proof CWPP as CWp. rewrite <- HT in CWp.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BBF.
    (* [comment removed for export] *)
    pose proof (heapkit_intro L HI hc LB mm moc [(lo, heap_top usegs L HI hc); (CUR, CUR + 32)] HH
       ltac:(constructor; [apply ok_stack; exact ACL | constructor; [apply (ok_cwrange L LB lo); [exact CWc | exact ACL] | constructor]])) as HK.
    pose proof (hcli_cwrange L LB lo _ (bv_unsigned sp) CUR 32 CWc DS2) as T1.
    pose proof (hcli_cwrange L LB lo _ (bv_unsigned sp) PP 8 CWp DS1) as T2.
    pose proof (hcli_crange L LB lo (bv_unsigned sp) BUF _ CRBUF DS3) as T3.
    pose proof (obj_cwrange L LB lo _ CUR 32 CWc ACL ltac:(clear; lia)) as O1.
    pose proof (obj_cwrange L LB lo _ PP 8 CWp ACL ltac:(clear; lia)) as O2.
    pose proof (obj_crange L LB lo BUF _ CRBUF ACL (Nat2Z.is_nonneg _)) as O3.
    pose proof (SUMS_callocP_ok L HI HCALLOC DIM1 DIM2 32 (cb_post p j1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25) LB (heap_top usegs L HI hc) moc ltac:(cbn; lia)) as SU.
    rewrite TP. change (id (mo_frame mo moc)) in MF.
    lazymatch type of HPX with ?T => change (id T) in HPX end. lazymatch type of MU with ?T => change (id T) in MU end. lazymatch type of WM with ?T => change (id T) in WM end.
    lx_run_tac (PLANS [0x1eb48] [] 60%N [SUM_calloc1P 32]); lx_tree.
    (* [comment removed for export] *)
    all: (let flt1 := fresh "FLt" in let flt2 := fresh "FLt" in flat constr:(LXHK) 2%nat; flclear LXHK; intros flt1 _; flat constr:(flt1) 2%nat; flclear flt1; intros flt2 _; flat constr:(flt2) 4%nat; flclear flt2; intros h2 HH2 HT2 MF2); change (mo_frame mo moc) in MF;
         lazymatch type of HPX with id ?T => change T in HPX end; lazymatch type of MU with id ?T => change T in MU end; lazymatch type of WM with id ?T => change T in WM end;
         pose proof (mo_frame_trans _ _ _ MF MF2) as MF9; try rewrite <- TP.
    all: let xmm := constr:(mm) in lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hl : lawP L LB _ [] ?mc ?mp, Hm1 : munch [] xmm ?mc', Hm2 : munch ?Wl ?mp' mx, Hw2 : wmono _ ?mp'' mx |- _ =>
           assert (HPX9 : heap_presx usegs L LB (bv_unsigned sp) X m mx);
           [ eapply heap_presx_trans; [exact HPX|]; eapply heap_presx_trans;
             [ eapply presx_munch; [exact MU| exact WM|]; intros a Ha Hc Ho; cbn [outside] in *;
               destruct Hc as [Hs|[Hd|Hb]]; [clear -Hs Ho Ha SLO HLS; lia| clear -Hd Ho Ha DHI ACL SLO HLS; lia| pose proof (in_block_below a Hb) as HBL; clear -HBL Ho Ha ACL SLO HLS; lia] |];
             eapply heap_presx_trans; [ eapply (heap_presx_of_munch usegs L); [exact Hm1| assumption| intros a _ _ _; exact I] |];
             eapply heap_presx_trans; [ eapply heap_presx_of_pres_sub; [exact Hl| intros b Hb; exact Hb| clear; lia| clear; lia] |];
             eapply presx_munch; [exact Hm2| exact Hw2|]; intros a Ha Hc Ho; cbn [outside] in Ho |- *;
             destruct Hc as [Hs|[Hd|Hb]];
             [ first [ clear -Hs Ho Ha SLO HLS; lia
                     | match goal with Hc14 : 0 <= alloc_ceiling + (- _ + -32) |- _ => clear -Hs Ho Ha SLO HLS Hc14 ACL; lia end ]
             | first [ clear -Hd Ho Ha DHI ACL SLO HLS; lia
                     | match goal with Hi13 : _ + 32 <= hl_img_lo L \/ _ <= _ |- _ => clear -Hd Ho Ha DHI ACL SLO HLS Hi13 DIM1 DIM2; lia end ]
             | first [ pose proof (in_block_below a Hb) as HBL; clear -HBL Ho Ha ACL SLO HLS; lia
                     | (flat constr:(Hb) 3%nat; flclear Hb; intros b Hb' Hr); destruct b as [Bb kb]; cbn in Hr;
                       match goal with Hap : forall b k, In (b, k) LB -> _ |- _ => pose proof (Hap Bb kb Hb') as HX end;
                       pose proof (in_block_below a ltac:(exists (Bb, kb); split; [exact Hb'| cbn; lia])) as HY;
                       clear -HX HY Hr Ho Ha ACL SLO HLS; lia ] ]
           | ] end end.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hst : stk _ mx lo _, Hfr : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ => release_frame Hfr Hst (bv_unsigned sp + -128) end end.
    - (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hcur : rw_cells _ mx CUR [_; _; _; _; C8 (Z_to_bv 64 ?v)] |- _ =>
        match goal with Z1 : 0 <= v, Z2 : 0 <= - v |- _ => replace v with 0 in Hcur by (clear -Z1 Z2; lia) end;
        apply aevtM_done; eapply (cb_post_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx lxmo h2 [] ct cpad cl cp tagw zpad j0 j1 (-106));
        [ right; reflexivity | | assumption ]
      end end.
      eapply inv_intro; try assumption.
      + rewrite HT2; exact HT. + constructor. + intros y Hy; destruct Hy. + exact I. + right; exact HBUFOK.
    - (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : rw_cells _ mx (bv_unsigned sp + -128) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?rest) |- _ =>
        destruct (proj1 (rw_cells_app usegs mx _ [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] rest) Hm) as [HFRT HFRG]; clear Hm;
        match type of HFRG with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -32) in HFRG by (cbn; clear; lia) end
      end end.
      (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hn : rw_cells _ mx ?N [C4 ?t; CB 4 _; C8 ?w; C8 (Z_to_bv 64 ?pq); CB 8 _] |- _ =>
        assert (HNEW : rw_cells usegs mx N (seq_cells t (Z_to_bv 64 0) (bv_unsigned w) pq 0));
        [ unfold seq_cells; rewrite (Z_to_bv_bv_unsigned w); eapply rw_cells_reshape;
          [ exact Hn | cbv [cells_wf cell_wf]; (flsplit; repeat split)
          | cbv [cells_bytes cbytes]; replace (le4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4) by (vm_compute; reflexivity);
            replace (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8) by (vm_compute; reflexivity); reflexivity ]
        | clear Hn ]
      end end.
      (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hl : lawP L LB _ [] ?mc ?mp, Hm1 : munch [] _ ?mc', Hm2 : munch ?Wl ?mp' mx, HO3 : lx_fprop (PROPSP L LB) 0 [BUF; _] |- _ =>
        assert (HBUF9 : bytes_at usegs mx BUF bs);
        [ destruct bs as [|b0 bs'] eqn:Ebs;
          [ apply bytes_at_nil; clear -BBF; lia
          | rewrite <- Ebs in *;
            assert (HB1 : bytes_at usegs mc BUF bs) by (eapply bytes_at_transport; [exact HBUF| exact Hm1| cbn; exact I]);
            assert (HB2 : bytes_at usegs mp BUF bs)
              by (eapply (heap_pres_bytes_at usegs L); [exact Hl| exact HB1|];
                  intros a Ha; destruct (CRBUF a Ha) as [S|[D|B]]; [left; clear -S Ha DS3 SLO HLS; lia| right; left; exact D| right; right; exact B]);
            pose proof (obj_apart L HI _ LB LB _ _ _ _ BUF (Z.of_nat (length bs)) HH2 ltac:(intros bb Hbb; exact Hbb) DIM1 DIM2 HO3 ltac:(clear; lia)) as APB;
            assert (HBS1 : 1 <= Z.of_nat (length bs)) by (rewrite Ebs; cbn [length]; clear; lia);
            eapply bytes_at_transport; [exact HB2| exact Hm2| cbn [disjoint_from]; clear -APB HBS1 D3 DS3 SLO HLS; lia] ] | ]
      end end.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HNEW : rw_cells _ mx ?N (seq_cells _ _ _ _ 0) |- _ =>
        apply aevtM_done; eapply (cb_post_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx lxmo h2 [N] ct cpad cl cp tagw zpad j0 j1 0);
        [ left; reflexivity | | assumption ];
        eapply inv_intro; try assumption; change (last [N] CUR) with N; change (hd 0 [N]) with N; change (LBof [N]) with ((N, 32) :: LB); try assumption
      end end.
      + rewrite HT2; exact HT.
      + constructor; [intros HIn; destruct HIn | constructor].
      + intros y [<-|[]].
        match goal with Hc14 : 0 <= alloc_ceiling + (- _ + -32), Hi13 : _ + 32 <= hl_img_lo L \/ _ <= _, Hap : forall b k, In (b, k) LB -> _ |- _ =>
          split; [clear -Hc14; lia|]; split; [clear -Hi13; lia| intros B k HBk; apply (Hap B k HBk)] end.
      + cbn [seq_lseg hd]. split; [left; reflexivity|].
        match goal with Hal : ?N mod 2 ^ Z.of_N 4 = 0, Hpos : 0 <= ?N + -1 |- _ =>
          split; [change (2 ^ Z.of_N 4) with 16 in Hal; exact Hal|]; split; [clear -Hpos; lia|]; split; [| exact I] end.
        eexists (Z_to_bv 64 tb), (Z_to_bv 64 0), (bv_unsigned Lw), q. split; [exact HNEW| clear -Hq HqL LR; lia].
      + right; exact HBUFOK.
  Qed.


  Lemma LBof_snoc : forall nodes N, LBof (nodes ++ [N]) = (N, 32) :: LBof nodes.
  Proof. intros. unfold LBof. rewrite rev_app_distr. reflexivity. Qed.

  Lemma hd_app_ne : forall (l l' : list Z) d, l <> [] -> hd d (l ++ l') = hd d l.
  Proof. intros [|a l] l' d H; [congruence| reflexivity]. Qed.

End Walk.
