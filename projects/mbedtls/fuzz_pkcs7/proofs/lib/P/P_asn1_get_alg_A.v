(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_platform_zeroize.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02fd36669b9e15d3 0 6 0 1 15 1 17 1 18 1 26 1 27 1P063d55bd74da9b5e 0 4 0 1 16 1 25 1 28 1P077a332b5b3faf04 2 26 0 5 0 1 1 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P082a934037a31897 0 2 0 1 15 1P0af81bb8ec09a7dd 0 5 0 1 13 1 15 1 16 1 25 1P10002385d5f99175 0 2 0 1 15 1P14f4074dd576cb68 0 4 0 1 23 1 33 1 34 1P1ae7266a20662c17 0 5 0 1 15 1 16 1 25 1 28 1P1d5df734740ba529 0 2 0 1 16 1P1daf2694cacb4dc7 0 4 0 1 16 1 25 1 28 1P22aafe7d5906b1a9 2 24 0 5 0 1 1 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P2460cf40176c46ea 0 3 0 1 14 1 26 1P27b4cd95c648f339 0 5 0 1 17 1 18 1 26 1 27 1P294ca0ade5a45590 0 5 0 1 15 1 16 1 25 1 28 1P2afd04d16adc38f3 0 2 0 1 15 1P2fa9357f833023af 2 24 0 5 0 1 1 1 25 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1P319c56d77cd3ab96 0 6 0 1 15 1 17 1 18 1 26 1 27 1P32252adebf693875 0 5 0 1 17 1 18 1 26 1 27 1P3885e904c8307542 0 4 0 1 23 1 33 1 34 1P3e074916845b02b5 2 26 0 5 0 1 1 1 25 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1P3e12ec3b087dc355 0 2 0 1 13 1P3fa408a187a569d9 0 7 0 1 14 1 17 1 24 1 25 1 26 1 27 1N0024583f1be3a0e5N00593332a7d8341cN007781c3debe1483N0217259882b74272N029b69003272437bN03c2b76df7a9ef4fN0426181880910277N0469dca3d8bce716N046b09339fca9c6aN04ca3a40a080ca46N069d668f66ef4b92N08deacdf4431a4d7N08edf71a321d8ea4N0975615623037604N098c776452834e33N0a442307fc883c11N0a586606def9dc24N0a9ca1ac8ec0e2d0N0b0039c553b7707aN0b2b7f551a283e7cN0c4062c45b9c7e42N0c40fad088592026N0cd045ef4fceb64dN0d789eba62ca5deeN0d9ee355ac2aa0efN0e775ffc2cc32214N0e7a06b654398ff6N0e920f59d2049054N0f6ef7dc64c472efN11ddcede6b161394N121977222caa534dN12a45403defc1194N135eb3bc66041defN136de06cc57b7991N13adbe8935e9653cN13c209e10e9f603fN13e52879b712b1cfN14a3b66931d8beb4N14d71c39f4f95ca5N15ac1de3ffc10912N16b466d85391c971N16b472d4b2123334N17f5f67a5ca788d2N18a7d629d8d3de97N1910637a76c88f17N19c825a71a235a37N1a415b8c4892e922N1af22b59cd9b8213N1b0dd81898c9fba1N1b2e43d0f0b547f0N1c46fee830e16c4fN1e63856df4908a41N1e9cca1a0148e71dN1fcb57019b7a308eN206611ceb9fb0462N207845379c070318N2175c52472a52096N22374d670bf0529aN2262a8960a2ec509N2365ffb4be522d13N23c4074105c91645N240f302880e692b0N2516fc1626f4610dN25a899cd262f4277N2779dedf4094de9eN278955b7c289651aN284100645f7e69a6N28e8dc6522603e64N295b212a270c92f3N29dec945286de138N2a39be31fe0962d5N2ac7dbf10ae96771N2b67625a0c44eb40N2b711ef4e04ba14eN2bdc0657abae8f85N2cc0cde046b836d7N2f8af27853c0db7cN30388ceb67f33137N30aca1c896c9a1f8N327a0794ce142aaaN336292d416d08172N33b97a5b0a4654fbN33c539223cb75e38N350e1f3b16c171ebN356504e5bd2eef80N35c8c99c85b410afN36114e3e68e9a673N3640a5ef7596c8afN36fefe5f3492fc6eN373a51efe240814dN37ec5fa48a369d25N388c9ee911d12c2aN390362bd160908cdN39165c92f8e5f85fN395226a0360b6f79N3994a3984ce53320N3a2cebbd324806f4N3a5f51840004a162N3acc42b8edf072eaN3ae3de27bea7e522N3b2799c77737abafN3b83f232011eacabN3b856d228796d86dN3be8861cd99b32b9N3c68920b64eb169aN3c9a4b8d6960dd3cN3d2e180c365189fbN3d4b2e09962b7ae5N3d5c32e258d54248N3d8cec2a4ce5a30fN3e337f7e7ec0d84eN3e349c8461a975c0N3e457655f68cd497N3e5c6556203b3b11"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_asn1_get_alg_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.Exec.evt"; "asn1_get_alg_post"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"].


Definition P_ASN1_GET_ALG : Z := 0x1e7b4.

(* [comment removed for export] *)
Notation ASN1_GET_ALG_STACK := 64 (only parsing).   (* [comment removed for export] *)

Definition asn1_get_alg_post (segs : list Segment) (L : heap_layout)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP ALG PAR P END BUF lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_alg_A ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Latag,(2.&40.)(1.(2.&40.)Lapad,(2.&40.)(1.(2.&40.)Lalen,(2.&40.)(1.(2.&40.)Lapw,(2.&40.)(1.(2.&40.)Lptag,(2.&40.)(1.(2.&40.)Lppad,(2.&40.)(1.(2.&40.)Lplen,(2.&40.)(1.(2.&40.)Lppw,(2.&40.)(5.(6.$0.R1;.(7.(8.O1:.O19.O18.O17.R1:.R19.R18.O16.O15.R17.R16.R15.R14.R13.R12.R11.R10.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R?.R>.R=.R<.)O:.(9.O1:.)O9.(:.(2.&40.))R;.(;.O1<.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O8.(10.O8.+8.))(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+18.))(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O19.)+40.)(12.&40.O19.))(13.(>.$4.$4.))))))O1.R;.)(5.(14.O1<.O1.R;.)(5.(15.O1<.R;.)(5.(6.(2.&40.)R17.(16.&40.R:.))(5.(5.(17.-7?.R:.)(18.R:.=))(5.(19.O1<.R;.O8.(=.$1:.(1;.(16.&40.R9.))(13.$1:.)))(5.(19.O1<.R;.O7.(=.$1:.(1<.R8.)(=.$1:.(1<.R7.)(=.$1:.(1;.R6.)(=.$1:.(1;.R5.)(13.$1:.))))))(5.(19.O1<.R;.O6.(=.$1:.(1<.R4.)(=.$1:.(1<.R3.)(=.$1:.(1;.R2.)(=.$1:.(1;.R1.)(13.$1:.))))))(5.(1=.O1<.R;.O2.(12.&40.O19.))(5.(1>.O1<.O1;.R;.)(5.(5.(18.O5.R9.)(18.R9.O4.))P,(6.$4.R:.=)(1.$4.Lap,$4.(1.$4.Lpp,$4.(5.(6.(2.&40.)R8.(16.&40.R2.))(5.(6.(2.&40.)R4.(16.&40.R1.))(5.(18.O3.R2.)(5.(18.(10.R2.(12.&40.R9.))R<.)(1?.(5.(6.$4.R1.=)(5.(6.$4.(12.&40.R5.)=)(6.(2.&40.)R7.(16.&40.=))))(5.(18.O3.R1.)(6.$4.(10.R1.(12.&40.R5.))R<.)))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_alg_stmt (segs : list Segment) (L : heap_layout) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_alg_A ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$4.PALG,$4.PPAR,$4.PP,$4.PEND,$4.PBUF,$4.Plo,$4.Pbs,(21.(2.&8.))Patag,(2.&40.)Papad,(2.&40.)Palen,(2.&40.)Papw,(2.&40.)Pptag,(2.&40.)Pppad,(2.&40.)Pplen,(2.&40.)Pppw,(2.&40.)P,(19.O4.R11.R10.(=.$1:.(1;.(16.&40.R=.))(13.$1:.)))P,(19.O4.R12.R10.(=.$1:.(1<.R9.)(=.$1:.(1<.R8.)(=.$1:.(1;.R7.)(=.$1:.(1;.R6.)(13.$1:.))))))P,(19.O4.R13.R10.(=.$1:.(1<.R6.)(=.$1:.(1<.R5.)(=.$1:.(1;.R4.)(=.$1:.(1;.R3.)(13.$1:.))))))P,(22.O4.R14.R>.R<.)P,(18.R?.R11.)P,(18.R12.R11.)P,(18.R12.(10.R11.(23.(24.(2.&8.)R?.))))P,(17.(10.R12.(23.(24.(2.&8.)R10.)))(25.+2.+3?.))P,(1?.(18.(10.R18.+8.)R17.)(18.(10.R17.+18.)R18.))P,(1?.(18.(10.R19.+8.)R17.)(18.(10.R17.+18.)R19.))P,(1?.(18.(10.R19.+18.)R18.)(18.(10.R18.+18.)R19.))P,(1?.(18.(10.R1;.+8.)R16.)(18.(10.R16.(23.(24.(2.&8.)R14.)))R1;.))P,(1?.(18.(10.R1;.+18.)R17.)(18.(10.R17.(23.(24.(2.&8.)R15.)))R1;.))P,(1?.(18.(10.R1;.+18.)R18.)(18.(10.R18.(23.(24.(2.&8.)R16.)))R1;.))P,(6.$4.(26.R1>.+8.)=)P,(6.$4.(26.R1>.+8.)=)P,(6.$4.(26.R1>.+8.)=)P,(17.=R21.)P,(17.=R21.)P,(17.=R21.)P,(17.=R1?.)P,(1=.O4.R26.R1?.(12.&40.R46.))P,(18.R20.(11.(12.&40.R47.)+40.))P,(18.(27.O3.)R21.)P,(6.$4.(26.(12.&40.R49.)+10.)=)P,(1?.(18.(10.R29.+8.)R23.)(18.(12.&40.R4:.)R29.))P,(1?.(18.(10.R29.+18.)R24.)(18.(12.&40.R4;.)R29.))P,(1?.(18.(10.R29.+18.)R25.)(18.(12.&40.R4<.)R29.))P,(1?.(18.(10.R27.(23.(24.(2.&8.)R25.)))R26.)(18.(12.&40.R4=.)R27.))P,(1>.O4.O3.R2>.)P,(28.O3.O1.+8.)P,(18.(29.O3.)(27.O3.))P,(1?.(18.(10.R30.+8.)(2:.O3.))(18.(29.O3.)R30.))P,(1?.(18.(10.R30.+18.)(2:.O3.))(18.(29.O3.)R30.))P,(1?.(18.(10.R30.+18.)(2:.O3.))(18.(29.O3.)R30.))P,(15.O4.R34.)P,(6.(2.&40.)R4=.(16.&40.R34.))P,(6.(2.&40.)R4=.(16.&40.R31.))P,(6.(2.&40.)R4=.(16.&40.R35.))P,(6.(2.&40.)R4=.(16.&40.R35.))(2;.O4.(2<.O4.O3.R5:.R59.R58.R57.R53.R52.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3;.R3:.R38.R37.R36.R35.R34.R33.R32.R39.)(7.(8.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.)R3;.(16.&40.O2.)R3:.(:.(2.&40.))R39.(;.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable L : heap_layout.
  Hypothesis HZ : platform_zeroize_stmt psegs L P_PLATFORM_ZEROIZE P_MEMSET_FUNC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP ALG PAR P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= ALG \/ ALG + 24 <= PP.
  Hypothesis D1b : PP + 8 <= PAR \/ PAR + 24 <= PP.
  Hypothesis D1c : ALG + 24 <= PAR \/ PAR + 24 <= ALG.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : ALG + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= ALG.
  Hypothesis D3b : PAR + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= PAR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis ALGB : 0 <= ALG /\ ALG + 24 <= 2^64.
  Hypothesis PARB : 0 <= PAR /\ PAR + 24 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis NZ3 : 0 < PAR.
  Hypothesis SLO : lo <= bv_unsigned sp - 64.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : ALG + 24 <= lo \/ bv_unsigned sp <= ALG.
  Hypothesis DS3 : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DS4 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CA : const_at L P_MEMSET_FUNC 8.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis OD1 : PP + 8 <= hl_data_lo L \/ hl_data_hi L <= PP.
  Hypothesis OD2 : ALG + 24 <= hl_data_lo L \/ hl_data_hi L <= ALG.
  Hypothesis OD3 : PAR + 24 <= hl_data_lo L \/ hl_data_hi L <= PAR.
  Hypothesis SPB : bv_unsigned sp < 2^64.

  Notation W := [(PP, PP + 8); (ALG, ALG + 24); (PAR, PAR + 24); (bv_unsigned sp - ASN1_GET_ALG_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_alg_post psegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP ALG PAR P END BUF lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HZ => idtac | B1 => idtac | B3 => idtac | B4 => idtac | D1 => idtac | D1b => idtac | D1c => idtac | D2 => idtac | D3 => idtac | D3b => idtac | PPB => idtac | ALGB => idtac | PARB => idtac | BUF0 => idtac | NZ3 => idtac | SLO => idtac | ACL => idtac | ACP => idtac | SPA => idtac | DS1 => idtac | DS2 => idtac | DS3 => idtac | DS4 => idtac | CA => idtac | DHI => idtac | OD1 => idtac | OD2 => idtac | OD3 => idtac | SPB => idtac end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L28448998296.77L28448999180.77L36936459268.86L38388647590.77L39457293334.78L39459141925.81L39459143089.81L40271527066.82L42814931121.74L43518462335.75L47739296203.75L57622410744.6 L57628696595.28L58232958215.74L59314873579.6 L8486015426.77 00000k01g02`02n03X04>04?05105?06L07Y07l08m09_09`09nS1L2sp1P3END2lo2bs3SLO3ACL3ACP2p42e22L22jk2Hp3He22LR3LXJ2H4S1L2sp1P3END2lo2bs3SLO3ACL3ACP2p42e22L22jk2Hp3He22LR3LXJ3XEQS1L2sp1P3BUF2lo2bs2B13SLO3ACL3ACP2p42e22L24ptag2jk2Hp3LXJS2sp2bs2jk3LXJS2sp3BUF2bs2p42L24alen3apw4ptag3ppw2jk3LXJS2sp3BUF2bs2p42L24alen3apw4ptag2jk3LXJFS1L2sp2lo2bs3SLO3ACL3ACP2p42L24alen2jk2LR3LXJ1x2H2S2sp2bs2jk3LXJS1L2sp1P3END3BUF2lo2bs2B12B32B44BUF03SLO3ACL3ACP2p42e22L22jk2Hp3He22LR3LXJ2H4S1L2sp1P3END3BUF2lo2bs2B12B32B44BUF03SLO3ACL3ACP2p42e22L22jk2Hp3He22LR3LXJ2H4S2sp2PP3ALG3PAR1x1HS1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2HaS1L2sp1P3END2lo2bs3SLO3ACL3ACP2p42e22jk2Hp3He23LXJSS2sp2bs2jk3LXJ". (* [comment removed for export] *)
  Lemma j3_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_alg_A ()) "Pp4,$4.Pe2,$4.PL2,(2.&40.)Patag,(2.&40.)Papad,(2.&40.)Palen,(2.&40.)Papw,(2.&40.)Pptag,(2.&40.)Pppad,(2.&40.)Pppw,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px14,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pjk,(21.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))P,(5.(18.(10.VP,+2.)R12.)(18.R12.R11.))P,(18.R12.VEND,)P,(19.$2=.R3.VPP,(=.$1:.(1;.(16.&40.R14.))(13.$1:.)))P,(19.$2=.R4.VALG,(=.$1:.(1<.R12.)(=.$1:.(1<.R11.)(=.$1:.(1;.R10.)(=.$1:.(1;.R?.)(13.$1:.))))))P,(19.$2=.R5.VPAR,(=.$1:.(1<.R?.)(=.$1:.(1<.R>.)(=.$1:.(1;.R14.)(=.$1:.(1;.R=.)(13.$1:.))))))P,(1.$4.Lap,$4.(5.(6.(2.&40.)R12.(16.&40.R1.))(5.(18.VBUF,R1.)(18.(10.R1.(12.&40.R13.))R18.))))P,(22.$2=.R7.VBUF,Vbs,)P,(1=.$2=.R8.Vlo,(10.(12.&40.Vsp,)-10.))P,(19.$2=.R9.(10.(12.&40.Vsp,)-10.)(=.$1:.(2>.#8.R:.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1>.$2=.VL,R:.)P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VALG,(10.VALG,+18.))(=.(>.$4.$4.)(?.$4.$4.VPAR,(10.VPAR,+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+40.)(12.&40.Vsp,))(13.(>.$4.$4.))))))Vm,R;.)P,(14.$2=.Vm,R<.)P,(15.$2=.R=.)(2;.$2=.(2<.$2=.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VALG,VPAR,VP,VEND,VBUF,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(16.&40.VPP,)(16.&40.R1?.)R1=.(16.&40.VPAR,)R12.(16.&40.R1>.)R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1>898.)Vfc,(:.(2.&40.))R>.(;.$2=.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros p4 e2 L2 atag apad alen apw ptag ppad ppw x5 x6 x7 x14 x16 x17 jk mm Hp He2 HPP HALG HPAR HA HBUF ST FR SOK MU WM MI.
  pose proof (bv_unsigned_in_range 64 L2) as LR.
  try (unfold bv_modulus in LR).
  try (cbn in LR).
  lxp_run (PLAN [0x1e9dc; 0x242bc] [(0x1ea00, DMerge 14)] 171%N).
  (* [comment removed for export] *)
  all: first [ lxp_ret ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HZ => idtac | B1 => idtac | B3 => idtac | B4 => idtac | D1 => idtac | D1b => idtac | D1c => idtac | D2 => idtac | D3 => idtac | D3b => idtac | PPB => idtac | ALGB => idtac | PARB => idtac | BUF0 => idtac | NZ3 => idtac | SLO => idtac | ACL => idtac | ACP => idtac | SPA => idtac | DS1 => idtac | DS2 => idtac | DS3 => idtac | DS4 => idtac | CA => idtac | DHI => idtac | OD1 => idtac | OD2 => idtac | OD3 => idtac | SPB => idtac end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L19514068839.82 L48072710941.82 L57622410744.6  L57628696595.54 L6279931793.82  L65169667317.86 L68515083543.88 L68515131806.86 L8208516130.86  R30208483112.113R35904382004.97 R57416785374.11300000V01S01f02g03^04c05W06K06L0730:B0:jS2sp1P2bs1k3cur4stop2jk2Hk4Hcur3LXJ2H5S1L2sp1P2lo2bs3SLO3ACL3ACP1k3cur4stop2e22jk2Hk4Hcur5Hstop3LXJS2sp2PP3ALG3PAR1x1HS1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2HaS1L2sp1P2lo2bs3SLO3ACL3ACP1k3cur4stop2jk2Hk4Hcur3LXJ2H5S1L2sp1P3END3BUF2lo2bs2B33SLO3ACL3ACP1k3cur4stop2e22Hk4Hcur5Hstop3He2S1L2sp1P3BUF2lo2bs2B13SLO3ACL3ACP1k3cur4stop2Hk4HcurS1L2sp1P3BUF2lo2bs2B13SLO3ACL3ACP1k3cur4stop2Hk4HcurFS2sp3BUF2bs1k3cur4stop2jk2Hk2ap3HA13LXJS1L2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2PP3ALG3PAR1P3END3BUF2lo2bs2B12B32D13D1b3D1c2D22D33D3b3SLO3ACL3ACP3DS13DS23DS33DS43cur4stop2e22L22x52x62x73x163x172mm2Hk4Hcur5Hstop3He2S2sp2bs1k3cur4stop4alen2jk2Hk2ap3HA23LXJ". (* [comment removed for export] *)
  Lemma loop3_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_alg_A ()) "Pk,$2?.Pcur,$4.Pstop,$4.Pe2,$4.PL2,(2.&40.)Patag,(2.&40.)Papad,(2.&40.)Palen,(2.&40.)Papw,(2.&40.)Pptag,(2.&40.)Pppad,(2.&40.)Pppw,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pjk,(21.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))P,(6.$2?.(30.(11.R11.R12.))R13.)P,(5.(18.(10.VP,+2.)R13.)(17.R13.R12.))P,(18.R13.R12.)P,(18.R13.VEND,)P,(19.$2=.R5.VPP,(=.$1:.(1;.(16.&40.R16.))(13.$1:.)))P,(19.$2=.R6.VALG,(=.$1:.(1<.R13.)(=.$1:.(1<.R12.)(=.$1:.(1;.R11.)(=.$1:.(1;.R10.)(13.$1:.))))))P,(19.$2=.R7.VPAR,(=.$1:.(1<.R10.)(=.$1:.(1<.R?.)(=.$1:.(1;.R15.)(=.$1:.(1;.R>.)(13.$1:.))))))P,(1.$4.Lap,$4.(5.(6.(2.&40.)R13.(16.&40.R1.))(5.(18.VBUF,R1.)(18.(10.R1.(12.&40.R14.))R1:.))))P,(22.$2=.R9.VBUF,Vbs,)P,(1=.$2=.R:.Vlo,(10.(12.&40.Vsp,)-10.))P,(19.$2=.R;.(10.(12.&40.Vsp,)-10.)(=.$1:.(2>.#8.R<.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1>.$2=.VL,R<.)P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VALG,(10.VALG,+18.))(=.(>.$4.$4.)(?.$4.$4.VPAR,(10.VPAR,+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+40.)(12.&40.Vsp,))(13.(>.$4.$4.))))))Vm,R=.)P,(14.$2=.Vm,R>.)P,(15.$2=.R?.)(2;.$2=.(2<.$2=.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VALG,VPAR,VP,VEND,VBUF,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(16.&40.VPP,)(16.&40.R21.)R1>.(16.&40.VPAR,)(16.&40.R20.)(16.&40.R1?.)R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1>9=<.)Vfc,(:.(2.&40.))R10.(;.$2=.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  induction k as [|k IH]; intros cur stop e2 L2 atag apad alen apw ptag ppad ppw x5 x6 x7 x16 x17 jk mm Hk Hcur Hstop He2
    HPP HALG HPAR HA HBUF ST FR SOK MU WM MI; [plia|].
  get_byte bs (cur - BUF) b NB.
  read_at HBUF NB (cur - BUF) RD.
  lxp_run (PLAN [0x1e898; 0x1e9dc; 0x242bc] [(0x1ea00, DMerge 14)] 171%N).
  (* [comment removed for export] *)
  all: first [ lxp_at 125404; (lxp_apply (IH (cur + 1) stop e2)) | lxp_at 125080; (first [ solve [ lxp_apply j3_walk ] | solve [ eapply j3_walk with (p4 := cur + 1) (e2 := e2); lxp_apply_post; lxp_apply_post ] | lxp_apply j3_walk ]) ].
  all: try (destruct HA as (ap & -> & HA1 & HA2); exists ap; repeat split; plia).
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?R15549877360.96R65637467018.9600000H00jS2sp1P2bs2nn3cur2HN4HcurS1L2sp2lo2bs3SLO3ACL3ACP2nn3cur2HN". (* [comment removed for export] *)
  Lemma loop3_entry : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_alg_A ()) "Pnn,$4.Pcur,$4.Pe2,$4.Pstopw,(2.&40.)Patag,(2.&40.)Papad,(2.&40.)Palen,(2.&40.)Papw,(2.&40.)Pptag,(2.&40.)Pppad,(2.&40.)Pppw,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pjk,(21.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))P,(5.(18.+1.R12.)(18.R12.+4.))P,(18.(10.VP,+2.)R12.)P,(18.(10.R13.R14.)R12.)P,(18.R13.VEND,)P,(6.(2.&40.)R13.(16.&40.(10.R15.R16.)))P,(19.$2=.R6.VPP,(=.$1:.(1;.(16.&40.R16.))(13.$1:.)))P,(19.$2=.R7.VALG,(=.$1:.(1<.R14.)(=.$1:.(1<.R13.)(=.$1:.(1;.R12.)(=.$1:.(1;.R11.)(13.$1:.))))))P,(19.$2=.R8.VPAR,(=.$1:.(1<.R11.)(=.$1:.(1<.R10.)(=.$1:.(1;.(16.&40.=))(=.$1:.(1;.R?.)(13.$1:.))))))P,(1.$4.Lap,$4.(5.(6.(2.&40.)R14.(16.&40.R1.))(5.(18.VBUF,R1.)(18.(10.R1.(12.&40.R15.))R1:.))))P,(22.$2=.R:.VBUF,Vbs,)P,(1=.$2=.R;.Vlo,(10.(12.&40.Vsp,)-10.))P,(19.$2=.R<.(10.(12.&40.Vsp,)-10.)(=.$1:.(2>.#8.R=.)(=.$1:.(1;.Vra,)(13.$1:.))))P,(1>.$2=.VL,R=.)P,(<.(=.(>.$4.$4.)(?.$4.$4.VPP,(10.VPP,+8.))(=.(>.$4.$4.)(?.$4.$4.VALG,(10.VALG,+18.))(=.(>.$4.$4.)(?.$4.$4.VPAR,(10.VPAR,+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.Vsp,)+40.)(12.&40.Vsp,))(13.(>.$4.$4.))))))Vm,R>.)P,(14.$2=.Vm,R?.)P,(15.$2=.R10.)(2;.$2=.(2<.$2=.VL,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VALG,VPAR,VP,VEND,VBUF,Vlo,Vm,)(7.(8.Vra,(16.&40.(10.(12.&40.Vsp,)-10.))Vgp,Vtp,R17.R16.R15.Vs0,Vs1,(16.&40.VPP,)(16.&40.R21.)(16.&40.=)(16.&40.VPAR,)R1?.(16.&40.R20.)R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+1>9=<.)Vfc,(:.(2.&40.))R11.(;.$2=.)))")
(* [comment removed for export] *).
  Proof.
    intros nn cur e2 stopw atag apad alen apw ptag ppad ppw x5 x6 x7 x16 x17 jk mm HN Hcur He He2 -> HPP HALG HPAR HA HBUF ST FR SOK MU WM MI.
    eapply loop3_walk with (k := Z.to_nat nn) (cur := cur) (stop := cur + nn) (e2 := e2); try eassumption; plia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.
