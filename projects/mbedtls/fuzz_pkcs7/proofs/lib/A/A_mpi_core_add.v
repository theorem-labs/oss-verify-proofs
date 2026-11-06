(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_add.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAMpiTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0251e3ec3ca6e7aa 0 2 0 1 2 1P02afa8326d4ad8cf 0 2 0 1 81 1P02d19f43f425a7a7 0 2 0 1 22 1P04ee27b00c67c4db 0 2 0 1 10 1P06219617457a7a53 0 2 0 1 14 1P065dd421d4300783 0 5 0 4 42 16 71 4 81 4 82 4P0674a4f0fca2d5f8 2 75 0 5 0 1 1 1 35 4 44 4 73 1 0 4 0 1 2 1 45 4 74 1P0745f32bed5301cc 0 4 0 1 38 1 53 1 54 1P0772bbdff6a4cd00 0 2 0 1 23 1P07da821b99466569 0 4 0 1 39 1 54 1 55 1P087ea51e1b9e6623 0 4 0 1 33 1 45 1 67 1P0885f4e0e0d9defe 0 5 0 1 43 4 68 1 80 1 81 1P096cac3aee4a4e4a 0 2 0 1 2 1P099afb95c9218a35 0 2 0 1 1 1P09d1a0ec55d000a5 0 2 0 1 77 1P0ad8e346c6cb91fe 0 2 0 1 1 1P0c0c5f3af47f31cb 0 5 0 4 43 16 72 4 81 4 82 4P0d2ec9c584b654b4 0 5 0 1 40 4 67 1 77 1 78 1P0e03195fb2c6e4f0 0 3 0 1 44 1 68 1P0e527db9da29f4d0 0 5 0 1 43 4 70 1 79 1 80 1P0e651ccc05c6f181 0 2 0 1 1 1P0ea5db5269d2d342 0 2 0 1 16 1P0f7d370f8f87d094 0 2 0 1 15 1P10f212a16a4e0ec2 0 5 0 4 44 16 73 4 80 4 81 4P115e2a7bfae84658 0 5 0 4 43 16 72 4 81 4 82 4P15ccf0dec4b0b163 0 2 0 1 2 1P1928e79fe44ef1ae 0 5 0 1 44 4 69 1 80 1 81 1P1a553eb73a8e729f 0 5 0 1 41 4 68 1 77 1 78 1P1baa6423c0a0d961 0 2 0 1 2 1P1e4035b4191ab05d 0 2 0 1 23 1P1ebbead268578bd0 0 5 0 1 41 4 68 1 77 1 78 1P1fae53d1bd7cd346 0 2 0 1 2 1P1fe0a6f301293f2c 0 2 0 1 77 1P2073cce059759a43 0 3 0 1 81 1 83 1P20aa88a5abd42fdf 0 2 0 1 2 1P216875a4185dd6ce 0 2 0 1 2 1P2199ca9db9db2fa0 0 2 0 1 1 1P22ef2c2903581959 0 2 0 1 79 1P237fcfc45c3bfc4d 0 2 0 1 16 1P2391ce64e280186e 0 2 0 1 2 1P24a247c31f4bcb63 0 2 0 1 81 1P25dcb7fb43e13598 0 5 0 1 42 4 69 1 79 1 80 1P26920e04452c2bb3 0 2 0 1 1 1P26d98f7aeac709ac 0 2 0 1 18 1P2929e924daf84f12 0 5 0 4 43 16 72 4 80 4 81 4P2a9aeea78cbf30d4 0 5 0 4 42 16 71 4 81 4 82 4P2af660f1bcdd9b87 0 5 0 1 44 4 71 1 80 1 81 1P2bc2c867301d9f04 0 2 0 1 1 1P2c9344c5168e7738 0 5 0 1 42 4 67 1 79 1 80 1P2cb1e76b669db1bc 0 4 0 1 39 1 54 1 55 1P2f237026a75f5e14 0 5 0 1 43 4 68 1 81 1 82 1P2fef0a5aaf2530e3 0 2 0 1 79 1P303c552d5773a0d1 0 3 0 1 82 1 84 1P304996661c3a896a 0 5 0 1 42 4 67 1 81 1 82 1P319a5af85739eeb4 0 5 0 4 42 16 71 4 81 4 82 4P335bd9e8e52a99e3 0 2 0 1 1 1P33763aed4a9ddbdc 0 4 0 1 33 1 45 1 67 1P33b430af56de1fab 0 2 0 1 14 1P3595626986079b80 0 3 0 1 45 1 81 1P35c52d5120ad6034 0 2 0 1 79 1P36392551f3fed518 0 2 0 1 17 1P364c65ce61453a98 0 5 0 1 40 4 67 1 77 1 78 1P37acd6914fe68914 0 3 0 1 44 1 68 1P37e9225aaa9137df 0 5 0 1 43 4 68 1 81 1 82 1P39361f90e26aa366 0 3 0 1 44 1 68 1P39ee58345b008672 0 2 0 1 22 1P3a94e1090f016033 0 2 0 1 23 1P3aa01104d62d38cb 0 2 0 1 79 1P3aa7ba7b54f6daec 0 2 0 1 2 1P3b74c99bbdfbc4b1 0 2 0 1 1 1P3d6ff8382898368f 0 2 0 1 1 1P3dfd6b0ec3079326 0 5 0 1 43 4 70 1 80 1 81 1P3e4e61336a134f10 0 5 0 1 43 4 68 1 79 1 80 1P3e97b06ae6fd1784 0 2 0 1 11 1P3f3367cd6a6e448f 0 5 0 1 42 4 67 1 81 1 82 1P3fee2f968422c5f0 0 5 0 4 43 16 72 4 81 4 82 4N012db24724594179N014093aafa3a6c2bN01b7ea50baac746bN025394129780bb54N0389889cbf56d767N04098f7cb0f16158N044b61d5c5986fa9N04619e9e2312feddN04b8f6edf6023bc7N05312f173cd75423N056f5dc7049afd09N05892b1f454ed45fN06408009a10bd653N06e595aab928ddf4N0733f3794be21dafN073e8ed0a855411cN0755c932e94f73cdN0805067f4422f0d8N084dc3f588df1ac6N08b1c21377ee85b4N08fad311c539dd82N092ad9cb6610446eN0a2ec5bf48a42e87N0a7ff46b2a1bc099N0a8253332be5012fN0aa1023c41505517N0ba26a9ce3020f17N0c96a5f43691a2b7N0d1943657e051809N0d3f91c31c0454e3N0d52e205caf1a2e3N0d8dd5f0ae4dfd94N0dff9edd96593a91N0f80078eb89dc7c5N0f82c3dec6f2f51bN0fa3955f299c0b0dN0fc2bb8a00995761N1035a76dc65c865fN1048f279a646ada0N1051ea16edd084e3N10758067e9bf8bc2N119b8f235285ad05N11c972e0645ebad9N11ec2e888333e266N12d2239744372b75N133a476c5282069eN139e348e40177c6fN13d30fa5bbfa0849N14c4bb8fd9961422N151243ae2a50cebbN15e049be78c48d8dN16385f7bf429ea02N168e7c9fdeb5240aN17143834fa1aa164N1771d8b6e1dd0e39N1944a563d6dcc2d4N194cb6a378d3de88N19b284331ca2f18dN1b7e9b68a48248afN1c1c335cd6a00ad2N1c352ee5442499d5N1d961f2fc63cbbdcN1d9f8c8c8c651514N1da8523d895d9c3eN1f0d9b8ff042ec95N1fff48ddbb21dde3N2100cdf5aee406b1N22173d70df6f73d7N22b5f451ebc5d9edN24066b9e862cff39N248510f6c8eb7164N25232aed6aed229eN255f23628374642aN25885a9fdb2a49bbN25eba8b63d32730cN26036f4eb20774cdN260e48456ecf159bN261e3cfe3cecc756N263a3618ff825b0eN26441831e0c685d8N274f2b2386f5fb89N27fe540170ac266bN281f8eda32aca84dN292d49de5384645fN29e50558c504a833N2a700821887df1c6N2b3b4233d5c5a716N2b415849a3940094N2b9a499f5e3e2dfdN2c30527c16a5813fN2c5c11a5d7ad0534N2cd4cb4d34d200d9N2d8f2478608816c0N2d993e909dc01a15N2e95c1925e6beb2fN2ec407c4d35988d8N2fd5b777594a2de2N318d7d1f1656bf57N3300897d19b43245N334ea13accb7e88fN3363738e4606dbabN336da8e34bfc9a98N34a416d5ff8e2fcaN3532e1698ce8682eN3598c36bdc8a9886N36fc7c6788b6d668N379525759bac9a9dN37d7be72c80acf91N38507be0646a051fN38617000d580a480N389637fbeee17fb8N393a78e8fdf2dc96N39d1096f95a44350N3bb95395f8c16edfN3be40f53463a0040N3c44145ae7074175N3c44248083ab3e18N3e3d88fc3de8664bN3f8a32b491068b4c"%lxh.
Ltac2 gd_tbl_A_mpi_core_add () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_ADD_STACK_A"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.LibA.AShadow.al_wf"; "OSSVerify.KrLib.LibA.AShadow.cs_ok"; "OSSVerify.KrLib.LibA.AShadow.abase"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "mpi_core_add_postA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"; "OSSVerify.KrLib.Lib.MpiCoreAux.add_inv"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.LibA.ALazy.al_sb"].


Definition A_MPI_CORE_ADD : Z := 0x0a4ae0.
Definition MPI_CORE_ADD_STACK_A : Z := 16.

Definition mpi_core_add_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n : Z) (xs ys zs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_add ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lc,$4.(1.(5.(2.&40.))Lxs',(5.(2.&40.))(6.(7.$0.R13.(8.(9.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(:.O19.)O8.(;.(2.&40.))R3.(<.O1:.)))(6.(=.(>.(?.$4.$4.)(10.$4.$4.O7.(11.O7.(12.+4.O6.)))(>.(?.$4.$4.)(10.$4.$4.(13.(14.&40.O18.)$15.)(14.&40.O18.))(16.(?.$4.$4.))))O1.R3.)(6.(17.O1:.O1.R3.)(6.(18.O1:.R3.)(6.(7.(2.&40.)R?.(19.&40.R2.))(6.(6.(1:.=R2.)(1:.R2.+1.))(6.(1;.O1:.R3.O7.R1.)(6.(7.$1<.(1=.(2.&40.)R1.)(1=.(2.&40.)O5.))(6.(7.(5.(2.&40.))(1>.(2.&40.)(1?.O6.)R1.)(1>.(2.&40.)(1?.O6.)O5.))(6.(7.$4.(11.(20.R1.O6.)(12.R2.(21.+2.(12.+20.O6.))))(11.(20.O4.O6.)(20.O3.O6.)))(22.O1:.R3.O2.(14.&40.O18.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_add_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_add ()) "PCS,P,$4.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$4.PA,$4.PB,$4.Pn,$4.Plo,$4.Pxs,(5.(2.&40.))Pys,(5.(2.&40.))Pzs,(5.(2.&40.))P,(1;.O3.R9.R8.R3.)P,(24.O3.R:.R8.(25.R3.))P,(24.O3.R;.R8.(25.R3.))P,(6.(1:.=R8.)(1:.R8.+2710.))P,(1:.R9.(26.(1=.(2.&40.)R7.)))P,(1:.R:.(26.(1=.(2.&40.)R7.)))P,(1:.R;.(26.(1=.(2.&40.)R7.)))P,(27.(6.(7.$4.R>.R?.)(7.(5.(2.&40.))R9.R:.))(27.(1:.(11.R>.(12.+4.(26.(1=.(2.&40.)R9.))))R?.)(1:.(11.R?.(12.+4.(26.(1=.(2.&40.)R:.))))R>.)))P,(27.(6.(7.$4.R>.R10.)(7.(5.(2.&40.))R9.R;.))(27.(1:.(11.R>.(12.+4.(26.(1=.(2.&40.)R9.))))R10.)(1:.(11.R10.(12.+4.(26.(1=.(2.&40.)R;.))))R>.)))P,(7.$4.(28.R11.+4.)=)P,(7.$4.(28.R11.+4.)=)P,(7.$4.(28.R11.+4.)=)P,(29.=R14.)P,(29.=R14.)P,(29.=R14.)P,(18.O3.R18.)P,(2:.O2.)P,(2;.O2.R3<.)P,(2<.O3.O2.R1;.)P,(2=.O3.O2.R3>.R1<.R1;.(12.+4.R18.))P,(2=.O3.O2.R3?.R1=.R1;.(12.+4.R19.))P,(2=.O3.O2.R40.R1>.R1;.(12.+4.R1:.))P,(22.O3.R1?.R1:.(14.&40.R3?.))P,(1:.R1;.(13.(14.&40.R40.)$15.))P,(7.$4.(28.(14.&40.R41.)+10.)=)P,(2>.R44.R1=.(13.(14.&40.R42.)R1=.))P,(27.(1:.(11.R22.(12.+4.(26.(1=.(2.&40.)R1=.))))(13.(14.&40.R43.)$15.))(1:.(14.&40.R43.)R22.))P,(27.(1:.(11.R22.(12.+4.(26.(1=.(2.&40.)R1=.))))(13.(14.&40.R44.)$15.))(1:.(14.&40.R44.)R22.))P,(27.(1:.(11.R22.(12.+4.(26.(1=.(2.&40.)R1=.))))(13.(14.&40.R45.)$15.))(1:.(14.&40.R45.)R22.))P,(7.(2.&40.)R3>.(19.&40.R25.))P,(7.(2.&40.)R3>.(19.&40.R25.))P,(7.(2.&40.)R3>.(19.&40.R25.))P,(7.(2.&40.)R3>.(19.&40.R25.))(2?.O3.O2.R4<.(30.O3.R4;.R4:.R49.R48.R44.R43.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R2<.R2;.R29.R26.R24.R23.R22.R25.R2:.)(8.(9.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)R2<.(19.&40.O1.)R2;.(;.(2.&40.))R2:.(<.O3.)))")
(* [comment removed for export] *).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A B n lx la lb lo : Z) (xs0 ys0 zs0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx /\ n <= la /\ n <= lb.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis DA : (A = X /\ la = lx /\ ys0 = xs0) \/ A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis DB : (B = X /\ lb = lx /\ zs0 = xs0) \/ B + 4 * lb <= X \/ X + 4 * lx <= B.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis AB : 0 < A /\ A + 4 * la <= 2^64.
  Hypothesis BB : 0 < B /\ B + 4 * lb <= 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis ALB : B mod 4 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SX : X + 4 * lx <= bv_unsigned sp - 16 \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A.
  Hypothesis SB' : B + 4 * lb <= bv_unsigned sp - 16 \/ bv_unsigned sp <= B.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_core_add_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n xs0 ys0 zs0 lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - MPI_CORE_ADD_STACK_A, bv_unsigned sp)].

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_add ()) "Pk,$1<.Pi,$4.Pc,$4.Pxs,(5.(2.&40.))Pys,(5.(2.&40.))Pzs,(5.(2.&40.))Px6,(2.&40.)Px7,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pjunk,(5.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pex,$4.Pea,$4.Peb,$4.Pen,$4.P,(7.$1<.(1?.(13.Vn,R11.))R12.)P,(6.(1:.=R12.)(29.R12.Vn,))P,(6.(1:.=R12.)(1:.R12.+1.))P,(7.$4.R7.(11.VX,(12.+4.R14.)))P,(7.$4.R7.(11.VA,(12.+4.R15.)))P,(7.$4.R7.(11.VB,(12.+4.R16.)))P,(7.$4.R7.(13.Vn,R17.))P,(1;.$31.R<.VX,R16.)P,(24.$31.R=.VA,(25.R16.))P,(24.$31.R>.VB,(25.R16.))P,(7.$4.(26.(1=.(2.&40.)R19.))Vlx,)P,(7.$4.(26.(1=.(2.&40.)R19.))Vla,)P,(7.$4.(26.(1=.(2.&40.)R19.))Vlb,)P,(32.(2.&40.)(1?.R1>.)R1<.Vxs0,)P,(32.(2.&40.)(1?.R1?.)R1<.Vys0,)P,(32.(2.&40.)(1?.R20.)R1<.Vzs0,)P,(33.R1?.R21.R20.Vys0,Vzs0,)P,(2=.$31.VAL,VCS,R16.VX,(12.+4.Vn,))P,(2=.$31.VAL,VCS,R17.VA,(12.+4.Vn,))P,(2=.$31.VAL,VCS,R18.VB,(12.+4.Vn,))P,(34.$31.R19.(11.(14.&40.Vsp,)-10.)(>.$35.(36.#8.R1:.)(>.$35.(37.Vra,)(16.$35.))))P,(22.$31.R1:.Vlo,(11.(14.&40.Vsp,)-10.))P,(=.(>.(?.$4.$4.)(10.$4.$4.VX,(11.VX,(12.+4.Vn,)))(>.(?.$4.$4.)(10.$4.$4.(13.(14.&40.Vsp,)$15.)(14.&40.Vsp,))(16.(?.$4.$4.))))Vm,R1;.)P,(17.$31.Vm,R1<.)P,(18.$31.R1=.)(2?.$31.VAL,VCS,(30.$31.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vxs0,Vys0,Vzs0,Vlo,Vm,)(8.(9.Vra,(19.&40.(11.(14.&40.Vsp,)-10.))Vgp,Vtp,(19.&40.(38.VAL,))R25.R24.Vs0,Vs1,(19.&40.R1=.)(19.&40.R1<.)(19.&40.R1;.)(19.&40.R1:.)(19.&40.R1<.)(19.&40.R1;.)(19.&40.R1=.)(19.&40.R29.)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R23.R22.R21.R20.)VF,(19.&40.+:4;08.)Vfc,(;.(2.&40.))R1>.(<.$31.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i c xs ys zs x6 x7 x28 x29 x30 x31 junk mm ex ea eb en Hk Hi Hc Ex Ea Eb En HX HA HB LX LA LB FX FA FB INV
      OX OA OB FR ST MU WM MI; [exfalso; xlia Hk Hi|].
    al_facts.
    (* [comment removed for export] *)
    lx_limb_ro HA FA i Ea (proj1 Hi) ltac:(xlia Hi LA Ln) wa VA. lx_limb_ro HB FB i Eb (proj1 Hi) ltac:(xlia Hi LB Ln) wb VB.
    lx_limb_rw HX i Ex (proj1 Hi) ltac:(xlia Hi LX Ln) wx NX.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. lx_hide HX.
    lx_run_tac (PLAN [0x0a4b08] [(0xa4b14, DJoin); (0xa4b28, DJoin); (0xa4b3c, DJoin)] 106%N); lx_tree.
    all: lx_unhide; lx_gc.
    (* [comment removed for export] *)
    all: lazymatch goal with DEF : ?cv = Z.b2z _ + Z.b2z _ |- _ => destruct (lx_core_add_exact wa wb c cv Hc DEF) as [Hc' V]; clear DEF end.
    all: lx_rn_rw ex CX'; lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'.
    all: pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX (proj1 Hi) Ex MUl WMl CX') as HX';
         pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(xlia Ex Hi) ltac:(xlia Ex Hi)) as MU';
         pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    - (* [comment removed for export] *)
      lx_rn_rw (bv_unsigned sp + -16) FR'. lx_rn_aobj X OX'. lx_rn_aobj A OA'. lx_rn_aobj B OB'.
      match goal with K : 0 <= en + _ |- _ => rename K into BR end.
      destruct (u32ro_next _ _ _ _ _ _ _ _ _ _ _ _ _ DA HX' LX FX HA LA FA ltac:(xlia Hi Ln) Ex MUl) as (ys' & HA' & LA' & FA').
      destruct (u32ro_next _ _ _ _ _ _ _ _ _ _ _ _ _ DB HX' LX FX HB LB FB ltac:(xlia Hi Ln) Ex MUl) as (zs' & HB'' & LB'' & FB').
      eapply (IH (i + 1)); [xlia Hk Hi | xlia Hi BR En | exact Hc' | xlia Ex | xlia Ea | xlia Eb | xlia En
        | exact HX' | exact HA' | exact HB''
        | exact (upd_length_Z _ _ _ _ LX) | exact LA' | exact LB''
        | exact (same_from_upd_Z _ _ _ _ FX (proj1 Hi)) | exact (same_from_S_Z _ _ _ FA' (proj1 Hi)) | exact (same_from_S_Z _ _ _ FB' (proj1 Hi))
        | exact (add_inv_next _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA VB V)
        | exact OX' | exact OA' | exact OB' | exact FR' | exact ST' | exact MU' | exact WM' | exact MI' ].
    - (* [comment removed for export] *)
      match goal with K : 0 <= _ + (- en + _) |- _ => rename K into BR | K : 0 <= - en + _ |- _ => rename K into BR end.
      lx_post.
      all: lazymatch goal with
           | |- munch _ _ _ => exact MU'
           | |- wmono _ _ _ => exact WM'
           | |- u32arr _ _ _ _ => exact HX'
           | |- @eq nat (length _) _ => rewrite upd_length; xlia LX L0
           | |- skipn _ _ = skipn _ _ => eapply skipn_upd_Z; [exact FX | xlia Hi | xlia Hi BR En | xlia LX L0]
           | |- lval _ ?nn + _ = _ => replace nn with (i + 1) by xlia Hi BR En; exact (add_inv_next _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA VB V)
           | |- _ => first [reflexivity | assumption | xlia Hc']
           end.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
End Walk.

Lemma A_mpi_core_add_spec : forall AL, asan_img_ok AL -> mpi_core_add_stmtA asegs AL A_MPI_CORE_ADD.
Proof.
  intros AL IMG. unfold mpi_core_add_stmtA, A_MPI_CORE_ADD.
  intros until zs. intros HX HA HB Hn LX LA LB DA DB ALX ALA ALB NZX NZA NZB MI ALWF CSOK ABS OX OA OB ST LO SPA SCS SX SA SB -> -> -> ->.
  pose (lxi := lxA_img AL IMG).
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  unfold MPI_CORE_ADD_STACK_A in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB. pose proof (u32ro_bound _ _ _ _ HB) as BB.
  pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  lx_run_tac (PLAN [0x0a4b08] [] 40%N); lx_tree.
  all: lx_gc.
  - (* [comment removed for export] *)
    match goal with K : 0 <= - n |- _ => rename K into BR end.
    lx_post. all: first [reflexivity | eassumption | xlia Hn BR | rewrite !lval_nonpos by xlia Hn BR; xlia0 | idtac].
    all: match goal with |- ?g => idtac "N0-LEFT:" g end.
  - (* [comment removed for export] *)
    match goal with K : 0 <= n + _ |- _ => rename K into BR end.
    eapply (@loop_walk AL IMG ALWF CS CSOK) with (X := X) (A := A) (B := B) (n := n) (lo := lo)
             (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (lb := Z.of_nat (length zs))
             (xs0 := xs) (ys0 := ys) (zs0 := zs) (k := Z.to_nat (n - 0)) (i := 0) (c := 0) (xs := xs) (ys := ys) (zs := zs).
    all: try assumption.
    all: lazymatch goal with
         | |- _ \/ _ => first [ destruct DA as [[EA EY]|DA']; [left; subst; repeat split; reflexivity | right; exact DA']
                              | destruct DB as [[EB EZ]|DB']; [left; subst; repeat split; reflexivity | right; exact DB'] ]
         | |- same_from _ _ _ => apply same_from_refl
         | |- add_inv _ _ _ _ _ => apply add_inv_0
         | |- 0 <= 0 < _ => xlia BR
         | |- _ /\ _ => first [xlia LX LA LB | xlia XB NZX | xlia AB NZA | xlia BB NZB | xlia0]
         | |- _ => first [ eassumption | reflexivity | xlia0 ]
         end.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
