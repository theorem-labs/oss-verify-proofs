(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac LxP_SumsArr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00cfbbffc536e71f 1 1 4 1 0 1 4 18 1 20 1 23 1 32 1P0207a5bbb079a5ad 1 1 4 3 1 1 31 1 34 1 4 2 1 32 1 33 1 35 4P044ff234274b0a4b 1 1 4 1 0 1 2 17 1 29 1P06fd0e9d36230d71 0 2 0 1 25 1P07f2283cbb555418 0 5 0 2 19 2 20 2 22 2 25 2P0838d450ce678673 1 1 4 1 0 1 2 20 1 34 1P0b4a679c54c166ac 2 24 1 1 4 4 3 1 19 4 33 1 34 1 6 0 1 24 1 27 4 32 1 35 1 36 4 1 1 4 3 2 1 32 1 35 1 4 0 1 33 1 34 1 36 4P0b4cd9a0d52d2fec 2 24 1 1 4 4 3 1 19 4 33 1 34 1 6 0 1 24 1 27 4 32 1 35 1 36 4 1 1 4 3 2 1 32 1 35 1 4 0 1 33 1 34 1 36 4P0b73a5158338e56b 1 1 4 2 13 1 34 1 7 0 2 19 8 20 8 25 8 31 8 35 2 36 8P0bc93e3549a848b6 1 1 4 2 9 1 27 1 5 0 1 8 4 22 4 28 1 29 4P0cec089b2213dab6 0 4 0 1 6 1 11 1 20 1P0d3b8165fa265395 1 1 4 2 0 1 31 1 3 12 1 32 1 33 4P0d49689d9bfaffe0 0 6 0 4 1 16 10 4 24 16 29 4 30 4P0dbdba8a5367356b 0 2 0 1 1 1P0e0bcc4e032d06fa 1 1 4 1 0 1 4 12 1 19 1 26 1 34 2P0f230f7e01f0785d 0 6 0 4 2 16 11 4 26 16 31 4 32 4P10c6ce9a87feb273 2 24 1 1 4 4 3 1 19 4 33 1 34 1 6 0 1 24 1 27 4 32 1 35 1 36 4 1 1 4 3 2 1 32 1 35 1 4 0 4 33 4 34 4 36 16P11a9c824a7e29461 0 2 0 1 1 4P1262bbe40c29c40b 0 4 0 1 8 1 13 1 22 1P12720d7f36cae500 0 7 0 4 5 4 20 16 22 16 25 16 34 4 35 4P12bc916f3f4c378d 0 4 0 1 21 1 29 1 30 1P1444b6392206fbc0 0 3 0 1 4 1 15 1P14e30ca78609bcac 1 1 4 3 1 1 32 1 33 1 4 2 4 31 4 34 4 35 16P1748f059ca852686 0 5 0 1 2 1 26 4 33 1 34 1P17e73dc175b04566 1 1 4 1 0 1 4 19 2 20 2 25 2 34 2P182451604070b2db 0 2 0 1 1 4P188e35dce468e199 0 2 0 1 9 1P1a2ead41200edba8 1 1 4 2 0 1 24 1 2 8 1 27 1P1af997324de25ca9 1 1 4 2 7 1 28 1 3 0 1 25 1 29 1P1d1fb0b293aa9a2d 0 2 0 1 26 1P1dcf268f1447de91 2 29 1 1 4 3 1 1 37 1 38 1 8 0 1 19 1 22 4 27 4 33 4 36 1 39 1 40 4 1 1 4 3 2 1 36 1 39 1 8 0 2 21 8 22 8 27 8 28 8 37 2 38 2 40 8P1ee11debd536ebd3 1 2 4 2 0 1 34 1 4 2 14 1 35 1 6 19 2 20 2 25 2 26 2 36 2 37 2P200695022654924f 0 6 0 4 1 4 16 16 23 4 27 4 28 4P201c56603cb44ef3 1 2 4 2 10 1 28 1 4 3 0 1 24 1 27 1 3 8 1 29 1 30 1P20c49b761cf8085f 1 2 4 2 0 1 34 1 4 2 14 1 35 1 3 20 1 36 1 37 1P21e71d33a114f267 1 1 4 1 0 1 3 20 1 25 1 34 1P2203fa52ce3f1f1a 0 3 0 1 4 1 15 1P221039914e2086f0 0 2 0 1 5 1P22eecf637fc12f4b 1 1 4 1 0 1 2 1 1 29 1P232ba9010f7a66fc 1 1 4 1 0 1 4 10 1 17 1 24 1 32 2P25248d16e9f6c9a2 1 1 4 1 0 1 2 16 1 30 1P252715c7b663472b 0 2 0 1 20 1P2775a18dd49404ac 0 2 0 1 7 1P2a7344a60b59fa06 1 1 4 1 0 1 2 2 1 31 1P2ab64183e38298b6 0 2 0 1 2 1P2b16f4702be5e2ad 0 3 0 1 1 4 17 4P2b6ec252131c0af6 0 2 0 1 5 1P2c3f7f88b3530a83 1 1 4 1 0 1 2 1 1 29 1P2d8e4a36f0f20985 0 4 0 1 21 1 29 1 30 1P2de372f55c2af9b7 2 24 1 1 4 4 3 1 19 4 33 1 34 1 6 0 1 24 1 27 4 32 1 35 1 36 4 1 1 4 3 2 1 32 1 35 1 4 0 1 33 1 34 1 36 4P2feb2f97ad5d6b04 0 6 0 4 6 1 11 1 20 1 26 4 27 1P30d0fa943083ed8e 2 20 0 2 0 1 2 1 1 1 4 2 0 1 31 1 3 1 1 30 1 32 4P31933feee3bfeb63 0 3 0 1 3 1 14 1P320c5ec136090d4e 1 1 4 3 0 1 32 1 33 1 6 2 1 23 1 26 4 31 1 34 1 35 4P33563dd896490c00 0 4 0 1 21 1 29 1 30 1P337136a6c57a941c 0 5 0 4 11 4 26 16 31 4 32 4P33b1e9d96134c8eb 0 4 0 1 21 1 29 1 30 1P34331e963d73b58a 0 4 0 1 20 1 22 1 25 1P3612e83438e21df1 0 2 0 1 9 1P3836058c69f6d7e5 0 2 0 1 4 1P39cdc626d0e58dd7 2 24 1 1 4 4 3 1 19 4 33 1 34 1 6 0 1 24 1 27 4 32 1 35 1 36 4 1 1 4 3 2 1 32 1 35 1 4 0 4 33 4 34 4 36 16P3a7398b596d6cbaf 0 2 0 1 9 1P3b1e37fda8312ca9 1 1 4 1 0 1 5 15 2 16 2 18 2 21 2 30 2P3c09298cbf0bd7d0 1 1 4 2 0 1 31 1 4 2 4 12 1 32 1 33 4P3c27af75e9bd566d 1 1 4 2 0 1 27 1 3 3 1 28 1 29 4P3cfbf7c542b654e7 0 4 0 1 18 1 35 1 36 1P3dbbdc5398111884 0 3 0 1 4 1 15 1P3e856ce076c4657a 2 29 1 1 4 3 1 1 37 1 38 1 9 0 32 19 32 21 128 22 128 27 128 33 128 36 32 39 32 40 128 1 1 4 3 2 1 36 1 39 1 5 0 1 22 4 37 1 38 1 40 4P3ee3ba11d2894bd6 0 4 0 2 12 1 19 1 26 1P3fe1bbd23b1e195c 0 4 0 1 21 1 29 1 30 1N0029168c6d356369N0088c1ba762d9f93N00b724815c8a0550N0150ce4051c14facN01879f063a2c35cdN0218c89dcd0fa889N024b8172090457c9N028df424acb31b8bN0322f071ab333263N047418a87fb1c055N04f921fa4c8b72cdN05713e9f4fc8a6c5N058e8bc2eea48954N05acd80a254167ecN0719d7beb45514e8N071c10ed700d527cN073a9251734a97c5N077fcdb7c930728fN07bbdf17093c8b9bN07f7c178a7df2db3N09d8dcdeada1c62eN0a13587ae2404aaaN0a1645d51690ab0fN0b7e5ac056735096N0c2858563fa9a1fdN0c45f5a68aa9865eN0c859138f85f2eb3N0c94847b17fb0995N0c9cb7b4af245f5cN0daaa6e000bb3b6dN0e089f1ceb6a07e7N0e82a90127c93d45N1096ea297b7c84b4N10b0492bfc73d3e1N10d0d3b0dc8f8292N10d7016390f854c5N1141d212f99c44caN128497b9fa04d46bN15390df26da3c8c9N1542d3fe098265a6N15a9fd86e1fedafdN16ead8e6fe99490bN1859ccd388a89dfbN1899df7e95734cb8N194d62c4cf045587N1bf4cd3c79b6d600N1c774971f8456765N1d455f24fab52682N1e5fe1907a841cbdN1e63f44cd37ba509N1e7ac157a5054834N204950051657f482N2060ab3cc80b085bN20b8913a7d9bad8bN211e8c962863dd16N2139a7bb8f3c5dc9N213b2234aa2653e3N22a58256a9df6b70N233b895951340a63N24e7469570b825c5N25cd1fa015147be1N280e53278d4fbd53N2930a8ae6d349cb0N2a37d48800e049d1N2aef5852ae5291d3N2b4d8407695d6587N2bfc9ee93daf7715N2c01cdc6ef6eed8eN2cf698cf34b0d3a0N2ed09d45d7e78517N304c21f849f34850N3099c0013173e6ccN3285207406509a62N32c1d6ae0c2e3790N32f2721fc0276c1fN33059e58b8178401N34f68b4183d0eafdN3536ce26552cca66N36267cbf0a7ed446N3765b9b47109392cN388b6303de5911c0N39adaa787782e367N3a1e6900a4e570c8N3a2c56bcb7285798N3afc06bdbde1915fN3b2b66c90829a061N3d0139e90216b5fdN3d4d0080604cc2d7N3d6b18a55e02fdd3N3dbab3cc45ba8ed4N3e4851406769a000N3e63aef89d1213fbN3ea41c91e5a33a62"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_read_be () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_READ_BE_STACK"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_read_be_post"; "read_be_ret"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"].


Definition P_MPI_CORE_READ_BE : Z := 0x22538.
Definition MPI_CORE_READ_BE_STACK : Z := 48.

(* [comment removed for export] *)
Definition chars_to_limbs4 (len : Z) : Z := (len + 3) / 4.
Definition read_be_ret (n len : Z) : Z := if n <? chars_to_limbs4 len then (-8) else 0.

Definition mpi_core_read_be_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n r : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O18.O17.O16.O15.R10.R?.R>.O14.O13.(9.&40.O4.)R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(:.O18.)O7.(;.(2.&40.))R2.(<.O19.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.O6.(12.O6.(13.+4.O5.)))(>.(?.$10.$10.)(11.$10.$10.(14.(15.&40.O17.)$16.)(15.&40.O17.))(17.(?.$10.$10.))))O1.R2.)(5.(18.O19.O1.R2.)(5.(19.O19.R2.)(5.(1:.O19.R2.O6.R1.)(5.(6.$1;.(1<.(2.&40.)R1.)(1<.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1=.(2.&40.)(1>.O5.)R1.)(1=.(2.&40.)(1>.O5.)O3.))(1?.O19.R2.O2.(15.&40.O17.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_read_be_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$10.Pn,$10.PB,$10.Pblen,$10.Plo,$10.Pxs,(4.(2.&40.))Pbs,(4.(2.&8.))P,(1:.O2.R8.R7.R2.)P,(21.O2.R9.R6.R2.)P,(5.(22.=R8.)(22.R8.+2710.))P,(22.R9.(23.(1<.(2.&40.)R5.)))P,(5.(22.=R8.)(22.R8.(23.(1<.(2.&8.)R5.))))P,(24.(22.(12.R:.(23.(1<.(2.&8.)R6.)))R<.)(22.(12.R<.(13.+4.(23.(1<.(2.&40.)R7.))))R:.))P,(6.$10.(25.R=.+4.)=)P,(24.(6.$10.R=.=)(26.+4.R>.))P,(24.(6.$10.R<.=)(26.=R=.))P,(26.(12.R10.(13.+4.(23.(1<.(2.&40.)R;.))))(27.+2.+40.))P,(26.(12.R?.(23.(1<.(2.&8.)R;.)))(27.+2.+40.))P,(1?.O2.R13.R>.(15.&40.R33.))P,(22.R?.(14.(15.&40.R34.)$16.))P,(6.$10.(25.(15.&40.R35.)+10.)=)P,(24.(22.(12.R15.(13.+4.(23.(1<.(2.&40.)R10.))))R11.)(22.(15.&40.R36.)R15.))P,(24.(22.(12.R14.(23.(1<.(2.&8.)R10.)))R12.)(22.(15.&40.R37.)R14.))P,(19.O2.R18.)P,(6.$10.(25.(15.&40.R3:.)+2.)=)P,(6.(2.&40.)R32.(9.&40.R19.))P,(6.(2.&40.)R32.(9.&40.R19.))P,(6.(2.&40.)R32.(9.&40.R19.))P,(6.(2.&40.)R32.(9.&40.R19.))(28.O2.(29.O2.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.R1=.R1<.(2:.R1<.R1:.)R18.R19.R1>.)(7.(8.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R20.(9.&40.O1.)R1?.(;.(2.&40.))R1>.(<.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L22426354934.5L38189876470.5000004008S2ysS2xs". (* [comment removed for export] *)
Lemma u8arr_app : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Psegs,(4.$2;.)Pm,P,(2.&40.)(3.(2.&8.))PA,$10.Pxs,(4.(2.&8.))Pys,(4.(2.&8.))(2<.(2=.R5.R4.R3.(2>.(2.&8.)R2.R1.))(5.(2=.R5.R4.R3.R2.)(2=.R5.R4.(12.R3.(23.(1<.(2.&8.)R2.)))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A xs ys. unfold u8arr. rewrite app_length, bytes_at_app, Nat2Z.inj_add.
  rewrite (wr_at_app segs m A (Z.of_nat (length xs)) (Z.of_nat (length ys))) by lia. tauto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020=L7029460431.3L8857200067.300000900BS3len1H1ES3len1H1E". (* [comment removed for export] *)
Lemma chars_to_limbs4_eq : forall len, 0 <= len ->
  len / 4 + Z.b2z (0 <? Z.land len 3) = chars_to_limbs4 len.
Proof.
  intros len H. unfold chars_to_limbs4. rewrite land_3_mod'.
  destruct (0 <? len mod 4) eqn:E; cbn [Z.b2z]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n blen lx lo : Z) (xs0 : list word).
  Hypothesis Hn : 1 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis XB : 4 < X /\ X + 4 * lx < 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO : 0 <= lo <= bv_unsigned sp - 48.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis OK : chars_to_limbs4 blen <= n.
  (* [comment removed for export] *)
  Hypothesis HXhi : u32arr psegs m (X + 4 * n) (skipn (Z.to_nat n) xs0).

  Notation POST := (mpi_core_read_be_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n (read_be_ret n blen) xs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation DINV mm xs := (u32arr psegs mm X xs /\ Z.of_nat (length xs) = n
                          /\ munch W m mm /\ wmono psegs m mm /\ mem_inv psegs mm /\ stk psegs mm lo (bv_unsigned sp + -40)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2977899845.3800000IS2ra2sp1X1n4blen3xs02OK1E". (* [comment removed for export] *)
  Lemma ret_ok : read_be_ret n blen = 0.
  Proof. unfold read_be_ret. destruct (n <? chars_to_limbs4 blen) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L23907401973.4L36962904668.8L56174851022.4L6330159503.11L64980102424.400000=00W00c01D01QS1n2Hn3xs'2LXS1n2lx3xs02Hn2Ln2L03xs'2LXS1X1n3xs'2LXS2sp1X1n2lx2lo3xs02Hn2Ln2L02LO2SXS1n2Hn3xs'2LX". (* [comment removed for export] *)
  Lemma fin_post : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Pm',P,(2.&40.)(3.(2.&8.))Pxs',(4.(2.&40.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(=.(>.(?.$10.$10.)(11.$10.$10.VX,(12.VX,(13.+4.Vn,)))(>.(?.$10.$10.)(11.$10.$10.(14.(15.&40.Vsp,)+30.)(15.&40.Vsp,))(17.(?.$10.$10.))))Vm,R10.)P,(18.$2?.Vm,R11.)P,(19.$2?.R12.)P,(1?.$2?.R13.Vlo,(15.&40.Vsp,))P,(1:.$2?.R14.VX,R13.)P,(6.$10.(23.(1<.(2.&40.)R14.))Vn,)(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,(2:.Vn,Vblen,)Vxs0,Vlo,Vm,(7.(8.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(9.&40.=)R11.R10.R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(:.Vra,)Vfc,(;.(2.&40.))R16.(<.$2?.)))")
(* [comment removed for export] *).
  Proof.
    intros until yt6. intros MU WM MI ST HX LX.
    unfold mpi_core_read_be_post, MPI_CORE_READ_BE_STACK. rewrite ret_ok.
    flexi 15%nat. exists (xs' ++ skipn (Z.to_nat n) xs0). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split. { apply u32arr_app. split; [exact HX|]. replace (X + 4 * Z.of_nat (length xs')) with (X + 4 * n) by xlia LX.
             eapply u32arr_transport; [exact HXhi | exact MU | exact WM |]. cbn [disjoint_from]. rewrite skipn_length. clear -Hn Ln L0 SX LO. lia. }
    split. { rewrite app_length, skipn_length. xlia LX L0 Ln Hn. }
    split. { rewrite skipn_app, skipn_all2 by xlia LX Hn. replace (Z.to_nat n - length xs')%nat with 0%nat by xlia LX Hn. reflexivity. }
    exact ST.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac rdbe_ret :=
    try rewrite (Z_to_bv_bv_unsigned sp); first [ apply evt_done | idtac ];
    let mx := lx_cur_mem in
    lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
    lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
    lazymatch goal with Hm : munch _ m mx |- _ =>
    lazymatch goal with Hw : wmono _ m mx |- _ =>
    lazymatch goal with Hi' : mem_inv _ mx |- _ =>
    lazymatch goal with Hs : stk _ mx lo (bv_unsigned sp) |- _ =>
      eapply (fin_post mx l);
      [ first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | exact Hw | exact Hi' | exact Hs | exact Hu
      | rewrite ?upd_length; rewrite ?upd_length in Hl; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] ]
    end end end end end end.
  (* [comment removed for export] *)
  Ltac rdbe_dinv :=
    let mx := lx_cur_mem in
    lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
    lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
    lazymatch goal with Hm : munch _ m mx |- _ =>
    lazymatch goal with Hw : wmono _ m mx |- _ =>
    lazymatch goal with Hi' : mem_inv _ mx |- _ =>
    lazymatch goal with Hs : stk _ mx lo _ |- _ =>
      assert (DI' : DINV mx l);
      [ refine (conj Hu (conj _ (conj _ (conj Hw (conj Hi' Hs)))));
        [ rewrite ?upd_length; rewrite ?upd_length in Hl; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption]
        | first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx Hn; lia] ] | ]
    end end end end end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L25421253429.5 L30529455224.2 L50193283012.2 L59310683793.4 M53645022417.85M6278369229.85 00000:00?00D00P00\00fS1k1l1r2HkS1X1rS1X1lS1l1r2Hk3HlrS1l1r3Hlr2H2S1n1l1r2Hs". (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Pk,$1;.Pl,$10.Pr,$10.Pxs,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxs1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxs2,(2.&40.)Pxs3,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwl,(2.&40.)Pwr,(2.&40.)P,(26.(14.R16.R17.)(13.+2.(23.R18.)))P,(5.(22.=R18.)(22.R18.R17.))P,(6.$10.(12.R19.R18.)(14.Vn,+1.))P,(6.(2.&40.)R5.(9.&40.(12.VX,(13.+4.(12.R1:.+1.)))))P,(6.(2.&40.)R5.(9.&40.(12.VX,(13.+4.R1:.))))P,(5.(1:.$2?.R19.VX,R1:.)(5.(6.$10.(23.(1<.(2.&40.)R1:.))Vn,)(5.(=.(>.(?.$10.$10.)(11.$10.$10.VX,(12.VX,(13.+4.Vn,)))(>.(?.$10.$10.)(11.$10.$10.(14.(15.&40.Vsp,)+30.)(15.&40.Vsp,))(17.(?.$10.$10.))))Vm,R19.)(5.(18.$2?.Vm,R19.)(5.(19.$2?.R19.)(1?.$2?.R19.Vlo,(12.(15.&40.Vsp,)-28.)))))))P,(30.$2?.R1:.(12.(15.&40.Vsp,)-28.)(>.$31.(32.Vs3,)(>.$31.(32.Vs2,)(>.$31.(32.Vs1,)(>.$31.(32.Vs0,)(>.$31.(32.Vra,)(17.$31.)))))))(28.$2?.(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,(2:.Vn,Vblen,)Vxs0,Vlo,Vm,)(7.(8.R1:.(9.&40.(12.(15.&40.Vsp,)-30.))Vgp,Vtp,R19.R18.R17.R9.R16.R8.(9.&40.+??00.)R15.R14.R13.R12.R11.R10.R?.R>.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(9.&40.+225;<.)Vfc,(;.(2.&40.))R1;.(<.$2?.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros l r xs mm xra xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 wl wr Hk Hlr Hs -> ->
      (HX & LX & MU & WM & MI & ST) FR; [exfalso; xlia Hk Hlr|].
    lx_run_tac (PLAN [0x225bc] [] 40%N); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x225bc) _ _ _ _) =>
             rdbe_dinv; eapply (IH (l + 1) (r - 1)); [xlia Hk Hlr | klia | klia | f_equal; xlia0 | f_equal; xlia0 | exact DI' | assumption]
         | |- _ => rdbe_ret
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L30529653348.2 M29098476572.64M57641705468.64M63722619209.6400000500800>00DS1X1nS1nS1n2HnS1n2Hn". (* [comment removed for export] *)
  Lemma conv_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_read_be ()) "Pxs,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxs2,(2.&40.)Pxs3,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pw4n,(2.&40.)P,(5.(1:.$2?.R14.VX,R15.)(5.(6.$10.(23.(1<.(2.&40.)R15.))Vn,)(5.(=.(>.(?.$10.$10.)(11.$10.$10.VX,(12.VX,(13.+4.Vn,)))(>.(?.$10.$10.)(11.$10.$10.(14.(15.&40.Vsp,)+30.)(15.&40.Vsp,))(17.(?.$10.$10.))))Vm,R14.)(5.(18.$2?.Vm,R14.)(5.(19.$2?.R14.)(1?.$2?.R14.Vlo,(12.(15.&40.Vsp,)-28.)))))))P,(30.$2?.R15.(12.(15.&40.Vsp,)-28.)(>.$31.(32.Vs3,)(>.$31.(32.Vs2,)(>.$31.(32.Vs1,)(>.$31.(32.Vs0,)(>.$31.(32.Vra,)(17.$31.)))))))P,(6.(2.&40.)R3.(9.&40.(13.Vn,+4.)))(28.$2?.(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,(2:.Vn,Vblen,)Vxs0,Vlo,Vm,)(7.(8.R16.(9.&40.(12.(15.&40.Vsp,)-30.))Vgp,Vtp,R15.R14.R13.(9.&40.VX,)R4.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(9.&40.+225:4.)Vfc,(;.(2.&40.))R17.(<.$2?.)))")
(* [comment removed for export] *).
  Proof.
    intros until w4n. intros (HX & LX & MU & WM & MI & ST) FR ->.
    lx_run_tac (PLAN [0x225bc] [] 20%N); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x225bc) _ _ _ _) =>
             try lx_same_mem; rdbe_dinv; eapply (loop_walk (Z.to_nat n) 0 (n - 1)); [klia | klia | klia | f_equal; xlia0 | f_equal; xlia0 | exact DI' | assumption]
         | |- _ => rdbe_ret
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422282358.2000001S". (* [comment removed for export] *)
Lemma lxp_c2l_be : forall len, 0 <= len -> Z.shiftr len 2 + Z.b2z (0 <? Z.land len 3) = chars_to_limbs4 len.
Proof. intros len H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. apply chars_to_limbs4_eq. exact H. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@L11801586693.118L18575840433.15 L20751747072.8  L22700267513.119L26051611366.3  L32663987161.4  L39016585212.5  L40175532981.4  L40601571469.117L41302442785.0  L42630579519.16 L43718696244.9  L44484923210.118L45146811896.4  L48363581927.9  L49161362620.3  L51428599399.12 L56174851022.5  L57517539375.16 L57519753105.94 L57628700040.6  L60897247877.5  L61197137045.11 L64784277.94    L66126176899.16 M1279833341.94  M1282097512.115 M13593897596.115M13595942889.94 M24906101043.115M27961132820.95 M29767952398.115M29769932187.94 M30534460422.94 M31843829089.96 M320765254.115  M322799827.94   M37464644674.67 M37464644674.69 M41071404659.115M41073251302.94 M42263054604.94 M42265017497.115M46772383403.94 M5382175897.115 M5384341772.94  M57641755481.94 M58704229413.115M58706133424.69 M58706133424.94 M63722749420.94 M7048231845.94  M7050137136.115 M8515874747.94  M8517982766.115 00001B01a02903203?03H03Z03f04U04V04o05I06M06Y06n07;07V07d08=08h09509D09c0:D0:d0:m0;60;B0;N0;Q0;\0;e0;n0<30<<0<K0<Z0<i0<j0=10=80=@0=H0=I0=W0=e0=k0>60>E0>T0>Z0>d0>n0?:0?FS2ra2sp1X1n1B4blen2lo2xs2bs2LX3Hbl2DB3ALX2LO3SPA2SX2SB2XB3SPR2l02H22H32LL4Hbl13BL4S2sp1X1n1B2lo2xs2bs2LX2DB2LO2SBS1n4blen2bs3Hbl2l02LL2OKS2ra2sp1X1n4blen2lo2xs2bs2LO2SX2XB3SPR2l02H22H33BL43x141HS4blen2bs3HblS1X1n3NZXS1n4blen2bs3Hbl2OKS1n2xs2Hn2LXS2ra2sp1X1n4blen2xs2bs2XB3SPR2l02H32LL4Hbl13BL4SS1B4blen2xs2bs3Hbl2BT3BB0S1X1n4blen2bs3Hbl2l02OK2LLS2ra2sp1X1n1B4blen2lo2xs2bs2LX3Hbl2DB2SX2SB2XB3SPR2l02H22H34Hbl13BL4S1n2Hn2ws2LWS1n4blen2bs3Hbl2l02LLS4blen2bs3HblS1n4blen2xs2bs3Hbl2l02LL2OKS1X1n2xs2Hn2LXS1B4blen2xs2bs3Hbl2BT3BB0S2ra2sp1X1n4blen2xs2bs2Hn3Hbl2XB3SPR2l03BL4S2sp1X1n1x2HxS1B4blen2bs3NZBS1X1n1B4blen2xs2bs2LX3Hbl2DB2OKS2ra2sp1X1n2xs2bs2Hn2XB3SPR2l02H3S1X1n4blen2xs2bs2LX3Hbl2XT2XB2OKS1n2xs2LXS1n2xs2LXS2sp3SPA3SPRS2sp3SPA3SPRS1nS1n4blen2H4S1n2Hn2H3S1n2Hn2H3S1X1nS4blen2H2S2sp1X2lo2xs2SXS2sp1X2lo2xs2SXS1n4blen2H13C2LFS2ra2RAS2ra2RAS2sp3SPRS2sp3SPRFS2sp2lo2LO3LO0S2sp2lo2LO3LO0S1n2H3S1n4blen2OKS1n4blen2H23C2LS1n4blen2H43C2LS1n2H3S1X3ALX2H5S1X3ALX2H5S1X2xs2XT2H5S1X2xs2XT2H5". (* [comment removed for export] *)
Lemma P_mpi_core_read_be_spec : mpi_core_read_be_stmt psegs P_MPI_CORE_READ_BE.
Proof.
  unfold mpi_core_read_be_stmt, P_MPI_CORE_READ_BE.
  intros until bs. intros HX HB Hn LX Hbl DB ALX NZX NZB XT BT ST LO SPA SX SB MI RA -> -> -> ->.
  unfold MPI_CORE_READ_BE_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (bytes_at_bound _ _ _ _ HB) as BB0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
  assert (NZX' : n <= 0 \/ 5 <= X) by (clear -NZX Hn; lia). clear NZX.
  assert (NZB' : blen <= 0 \/ 1 <= B) by (clear -NZB Hbl; lia). clear NZB.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (lock HB) as HB0. pose proof (lock HX) as HX0.
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn (Z.to_nat n) xs) in HX. apply u32arr_app in HX. flat constr:(HX) 2%nat. flclear HX. intros HXlo HXhi.
  rewrite firstn_length in HXhi. replace (X + 4 * Z.of_nat (Nat.min (Z.to_nat n) (length xs))) with (X + 4 * n) in HXhi by xlia LX Hn.
  assert (LXlo : Z.of_nat (length (firstn (Z.to_nat n) xs)) = n) by (rewrite firstn_length; xlia LX Hn).
  pose proof (lock HXhi) as HXhi'. clear HXhi HB.
  pose proof (sumsarr_ok [X]) as LXSUMS.
  (* [comment removed for export] *)
  lx_run_tac (PLANS [0x22590; 0x225bc] [] 60%N SUMSARR); lx_tree.
  all: lxp_unjunk; try lx_same_mem; pose proof (lxp_c2l_be blen ltac:(xlia Hbl)) as C2L.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x225bc) _ _ _ _) =>
         (* [comment removed for export] *)
         let mx := lx_cur_mem in let xX := constr:(X) in let xm := constr:(m) in let xlo := constr:(lo) in let xsp := constr:(sp) in
         lazymatch goal with Hu : u32arr _ mx xX ?lw0 |- _ =>
         lazymatch goal with Hl : Z.of_nat (length lw0) = _ |- _ =>
         lazymatch goal with Hm : munch _ xm mx |- _ =>
         lazymatch goal with Hw : wmono _ xm mx |- _ =>
         lazymatch goal with Hi' : mem_inv _ mx |- _ =>
         lazymatch goal with Hs : stk _ mx xlo _ |- _ =>
         lazymatch goal with Hf : rw_cells _ mx (bv_unsigned xsp + -40) _ |- _ =>
           eapply (@loop_walk) with (k := Z.to_nat n) (l := 0) (r := n - 1) (lx := Z.of_nat (length xs)) (xs0 := xs) (blen := blen);
           first [ exact Hf | exact (unlock _ HXhi') | refine (conj Hu (conj _ (conj _ (conj Hw (conj Hi' Hs))))); [rewrite Hl; exact LXlo | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx Hn; lia]
                 | reflexivity | klia | f_equal; klia ]
         end end end end end end end
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22590) _ _ _ ?mx) => idtac
       | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?xa0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mf _) =>
         tryif constr_eq mf m then
           ((* [comment removed for export] *)
            apply evt_done; unfold mpi_core_read_be_post, read_be_ret;
            first [ rewrite (proj2 (Z.ltb_lt n (chars_to_limbs4 blen))) by klia
                  | rewrite (proj2 (Z.ltb_ge n (chars_to_limbs4 blen))) by klia ];
            flexi 15%nat; exists xs;
            split; [reflexivity|];
            split; [apply munch_refl|]; split; [apply wmono_refl|]; split; [exact MI|]; split; [exact (unlock _ HX0)|];
            split; [reflexivity|]; split; [reflexivity|]; exact ST)
         else
           ((* [comment removed for export] *)
            try rewrite (Z_to_bv_bv_unsigned sp); apply evt_done;
            let mx := lx_cur_mem in let xX := constr:(X) in let xm := constr:(m) in let xlo := constr:(lo) in let xsp := constr:(sp) in
            lazymatch goal with Hu : u32arr _ mx xX ?l |- _ =>
            lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
            lazymatch goal with Hm : munch _ xm mx |- _ =>
            lazymatch goal with Hw : wmono _ xm mx |- _ =>
            lazymatch goal with Hi' : mem_inv _ mx |- _ =>
            lazymatch goal with Hs : stk _ mx xlo (bv_unsigned xsp) |- _ =>
              eapply fin_post with (lx := Z.of_nat (length xs)) (xs0 := xs);
              first [ exact Hw | exact Hi' | exact Hs | exact Hu | exact (unlock _ HXhi') | exact eq_refl
                    | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia
                    | rewrite Hl; exact LXlo | klia ]
            end end end end end end)
       end.
  (* [comment removed for export] *)
  let mx := lx_cur_mem in
  lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
  lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
  lazymatch goal with Hm : munch _ m mx |- _ =>
  lazymatch goal with Hw : wmono _ m mx |- _ =>
    rename Hu into RWu; rename Hm into MU1; rename Hw into WM1;
    assert (LL : Z.of_nat (length l) = n) by (rewrite Hl; exact LXlo); clear Hl;
    set (l0 := l) in RWu, LL; clearbody l0
  end end end end.
  try clear MU WM. rename MU1 into MU. rename WM1 into WM.
  assert (OK : chars_to_limbs4 blen <= n) by (rewrite <- C2L; klia).
  assert (Hbl1 : 1 <= blen) by klia.
  assert (BL4 : blen <= 4 * n) by (clear -OK Hbl; unfold chars_to_limbs4 in OK; lia).
  lx_gc.
  pose proof (unlock _ HB0) as HB1. eapply (bytes_at_transport psegs _ _ _ _ _) in HB1; [| exact MU | cbn [disjoint_from]; clear -DB SB LO Hn LX Hbl BB0; lia].
  zstep. zstep. zstep. zstep. zstep.
  apply u32arr_cells in RWu. apply u8arr_of_rw_cells in RWu.
  rewrite <- (firstn_skipn (Z.to_nat (4 * n - blen)) (u32s l0)) in RWu. apply u8arr_app in RWu. flat constr:(RWu) 2%nat. flclear RWu. intros RW1 RW2.
  rewrite firstn_length, u32s_length in RW2. replace (Nat.min (Z.to_nat (4 * n - blen)) (4 * length l0)) with (Z.to_nat (4 * n - blen)) in RW2 by (clear -LL Hbl C2L OK Hn; unfold chars_to_limbs4 in OK; lia).
  apply rw_cells_of_u8arr in RW2. rewrite skipn_length, u32s_length in RW2.
  replace (X + Z.of_nat (Z.to_nat (4 * n - blen))) with (X + (4 * n - blen)) in RW2 by (clear -LL Hbl OK Hn; unfold chars_to_limbs4 in OK; lia).
  apply rw_cells_of_u8arr in RW1. rewrite firstn_length, u32s_length in RW1.
  rewrite <- (firstn_skipn (Z.to_nat blen) bs) in HB1. apply bytes_at_app in HB1. flat constr:(HB1) 2%nat. flclear HB1. intros HB1 _.
  pose proof P_memcpy_spec as SP. unfold memcpy_stmt in SP.
  eapply evt_cut.
  { eapply SP with (src := firstn (Z.to_nat blen) bs); rewrite ?unsigned_lit by (clear -XB XT BT LX Hn Hbl BB0 OK SPR; unfold chars_to_limbs4 in OK; lia);
      [ exact HB1 | rewrite firstn_length; clear -Hbl; lia
      | replace (Z.to_nat blen) with (4 * length l0 - Z.to_nat (4 * n - blen))%nat by (clear -LL Hbl OK Hn; unfold chars_to_limbs4 in OK; lia); exact RW2
      | clear -DB Hbl LX Hn OK; unfold chars_to_limbs4 in OK; lia | assumption ]. }
  clear SP HB1 RW2. unfold memcpy_post. rewrite !unsigned_lit by (clear -XB XT BT LX Hn Hbl BB0 OK SPR; unfold chars_to_limbs4 in OK; lia).
  match goal with H : mem_inv psegs ?mc |- _ => post_call psegs mc end.
  match goal with H : rw_cells psegs ?m2 (X + (4 * n - blen)) _ |- _ => rename H into RW2 end.
  apply u8arr_of_rw_cells in RW1. apply u8arr_of_rw_cells in RW2.
  lazymatch type of RW2 with u8arr _ ?m2 _ _ =>
    assert (U8 : u8arr psegs m2 X (firstn (Z.to_nat (4 * n - blen)) (u32s l0) ++ firstn (Z.to_nat blen) bs))
      by (apply u8arr_app; split; [exact RW1|]; rewrite firstn_length, u32s_length;
          replace (X + Z.of_nat (Nat.min (Z.to_nat (4 * n - blen)) (4 * length l0))) with (X + (4 * n - blen)) by (clear -LL Hbl OK Hn; unfold chars_to_limbs4 in OK; lia); exact RW2);
    clear RW1 RW2;
    destruct (u32arr_of_u8arr psegs m2 X _ (Z.to_nat n) U8 ltac:(rewrite app_length, !firstn_length, u32s_length; clear -LL Hbl OK Hn LX BB0; unfold chars_to_limbs4 in OK; lia)) as (ws & HXB & LW);
    clear U8
  end.
  lx_mkR.
  match goal with H4 : mem_inv psegs ?m2, H5 : stk psegs ?m2 lo _, Hf : rw_cells psegs ?m2 (bv_unsigned sp + -40) _ |- _ =>
    eapply (@conv_walk) with (lx := Z.of_nat (length xs)) (xs0 := xs) (blen := blen);
    first [ exact Hf | exact (unlock _ HXhi')
          | refine (conj HXB (conj _ (conj _ (conj _ (conj H4 H5)))));
            [ clear -LW Hn; lia
            | first [exact MU | eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
            | exact WM ]
          | f_equal; klia | klia ] end.
  all: match goal with |- ?g => idtac "LEFT" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
