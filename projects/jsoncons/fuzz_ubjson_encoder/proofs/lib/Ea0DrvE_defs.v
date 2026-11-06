(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Ea0DrvEntry Ea0Drv_defs Ea0DrvRead Ea0DrvG_defs Ea0DrvC_defs Ea0DrvD_defs Ea0DrvLibL.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Ea0DrvE_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond05C13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5summEC13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7DrvKitA:kentry_eqbC13~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:sr_vars_ltC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:kn_vars_ltC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26s_regsC13~~~C47Corelib5Lists7ListDef3nthC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0Drv_defs8kn_afterC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init5Logic3and01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs4srPAC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes4bool02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs3rPAC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvD_defs5rLB1AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs4knPAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs4rQtAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs4rQfAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5knQ0AC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7DrvKitA7ksubl_bC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs6knLH2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5knQ2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5rLB2AC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvD_defs5srLBAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs6knLc2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs4rP2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5knP2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5rSt2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5rSf2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs6srSf2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs6srSt2AC13~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib5Lists7ListDef3mapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymDrive?sr_after_call_jC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0Drv_defs;keep_allocAC13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs4rT1AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5srM1AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5rT2fAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5rT2tAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24ridxC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0Drv_defs6c_keptC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5srF2AC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Ea0Drv_defs3MSOC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5knM1AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs5knF2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Ea0DrvE_defs4rT3AC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition IMG_PF_A : list (Z * Z) :=
  [(0x10000, 0x13a000); (0x13d8d8, 0x13dab0); (0x13db98, 0x13e340); (0x664050, 0x675a28); (0x675a30, 0x675a78); (0x675a94, 0x675aa8);
   (0x675ab0, 0x696298); (0x6966a8, 0x696f38); (0x696f40, 0x698000)].
Definition keep_pfA (so : Z) (bls : list (nat * Z)) (kn : list kentry) : list kentry := kn_keep 0 so 3232 bls [] [] IMG_PF_A IMG_RW_A kn.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition PSO : Z := -288.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition knLr0A : list kentry := Eval vm_compute in keep_libA TSO LIBSTK [(48%nat, 65536)] [] knLc1A.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition rPA := Eval vm_compute in runTA scr0 (SS 0xa8824 srLr0A [] knLr0A 134).
Definition srPA : list expr := Eval vm_compute in s_regs (fst (fst rPA)).
Definition knPA : list kentry := Eval vm_compute in kn_after rPA knLr0A.
(* [comment removed for export] *)
Definition srQ0A : list expr := Eval vm_compute in sr_after_call_j srPA (map ridx c_kept) 134.
Definition knQ0A : list kentry := Eval vm_compute in keep_pfA PSO [(48%nat, 65536)] knPA.
(* [comment removed for export] *)
Definition rQtA := Eval vm_compute in runTA (SCR [true] [] []) (SS 0xa891c srQ0A [] knQ0A 166).
Definition rQfA := Eval vm_compute in runTA (SCR [false] [] []) (SS 0xa891c srQ0A [] knQ0A 166).

Definition summE (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), length (s_log (fst (fst r)))).

Lemma loop_itinerary_okA :
  summE rPA = (0x63d30, [SCStoreOk (SA (ELit 0) 0x674054) 1], 134%nat, 10%nat)      (* [comment removed for export] *)
  /\ snd (fst rLB1A) = [SCStoreOk (SA (ELit 0) 0x674054) 1]                              (* [comment removed for export] *)
  /\ (nth 1 srPA (ELit 0), nth 2 srPA (ELit 0), nth 10 srPA (ELit 0), nth 11 srPA (ELit 0), nth 19 srPA (ELit 0))
     = (ELit 0xa891c, EAlu ALU_ADD (EVar 0) (ELit (-288)), ELit 85943, EAlu ALU_ADD (EVar 0) (ELit (-264)), ELit 0)
  (* [comment removed for export] *)
  /\ forallb (fun K => existsb (kentry_eqb K) knPA)
       [KWr (SA (EVar 0) (-8388608)) 8388608; KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1286144; KWord (SA (ELit 0) 6904512) 8 (EVar 3)] = true
  /\ sr_vars_lt 134 srPA = true /\ kn_vars_lt 134 knPA = true
  /\ (s_pc (fst (fst rQtA)), snd (fst rQtA), s_log (fst (fst rQtA))) = (0xa8810, [SCBr true BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst rQfA)), snd (fst rQfA), s_log (fst (fst rQfA))) = (0x7a198, [SCBr false BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (nth 1 (s_regs (fst (fst rQfA))) (ELit 0), nth 10 (s_regs (fst (fst rQfA))) (ELit 0)) = (ELit 0xa8850, EVar 83)
  /\ kn_after rQtA knQ0A = knQ0A /\ kn_after rQfA knQ0A = knQ0A.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0DrvE_defs ()) ["FPX_1"] "h01Kp%0p;1p;2p;3p;4g0000j1bTg000Pj2FTg0010j11Tg001Uj10Tg002:j1BTg003Hj2?Tg004Wj12Tg0056j2yTg006Hj1cTg006hj3ATg007Hj4=Tg007hj3<Tg008Bj15Tg009Pj1YTg009nj3oTg00;<j4eTg00<Nj18Tg00<lj2mTg00><j2lTg00?Lj4kTg00@\j3jTg00Alj2QTg00C<j2@Tg00CWj2ITg00D1j1wTg00E>j3TTg00E[j3aTg00F8j1vTg00GEj3uTg00Gaj3tTg00H=j2sTg00IIj2rTg00JUj1iTg00Kaj1hTg00Lnj1qTg00N<j4_Tg00NXj2gTg00Ogj3pTg00Q5j3PTg00REj4fTf0R0#1#1p=3%10#0p=7%00#1p=4%00#0#0#8p=9%00#0p=:%00#0#0#0p=;%00#8p=n%20#2#2#2p=S%20#2p=L%20#2#2#2#2#2#2#2p=E%10#0#0#0p=>%10#0#0p=N%10#1#0#0p=\%80#Bp=C%00#Yp=[g00R`R1f1R2;p0p=Gg00SLR3P3P2P0C=p=Z%10#1#1#1p=Kf2R4P3P2P0C=p=O%Y0,?2p=^f3R5/?4?P20p=]%00#1#0#0p=X%80,?2p=d%00#0#0#0#0#0#0#0p=Jg00TZR6f4R7%85'??P42;A0p=MAA6209A64p=DAj542=A60p=Hf6R8f5R9;P7AP542=A605A6p=W%Y5,?7?P42=A60p=6AP542=A60p=xP8P9P7P5P4P2P0CfCfp=VP3P2g00UjR5P0C_p=Ug00W6R7g00WVR97<0p=`1@20,@4p=Rg00X6R4g00XTR2#bR8'FR:g00YfR;'FR</F;R=P<P;P:P;P4P8g00ZER;#1R<#0R>#0R?#0R@#1#3#7#7#4#7#9g00ZjRA#BRB%1?R?#1RC#7#7RD#:#;#7#7RE#7#nRF'?RGg00[HRH#2RI'y%c2RJ5A2RKC=%2IRL#2RM#2RN#SRO#LRP#2RQ#ERR#L#ERS#2#L#E#ERT#L#S#E#ERU#2RV#2RW#2RX#2RY#2#SRZ#2R[#2R\#LR]#2#L#S#E#E#ER^#2R_#2R`#2Ra#2Rb#2Rc#2#L#S#ERdC=PPC=Re;<eA<8KKS001F33Rf/F3Rg/F3Rh/F3Ri%0;Rj#1Rk#0Rl#>Rm#NRn#N#4#\#C%5HRH%0jRo#1Rp#0#:S01#0Rq#[Rr#B'G'Z%0lRl#K#7#3#4#3#C5Of%0oRo#0Rs#N#[Rt#B,GHRu5Og=OhBRv;<vS02A<799Rwg00[gRx#bRy,F:RzP:PyP4P8%:nRn#0R{#0#7#9P9g00]7R|%5\%Y;#B5o1R1PBCe=A2JC=%cxRxC=R\;<\S03P:PyP4P8%1<R<#1R}#0R~#1#;#\#3#9g00]iP|P1PBCe=A2JC=PxC=Rx=<zxRJ%1n#4#;#C%5]'ZR]=<f]Rn%b6R21?HrPOPu%:~R~#0,^HPO%5`PH%1}R}#0#:PO%5_PH%0sR_#0R`#:RuPO%5^PHPtPOPBC]RtPH%1>R^#N#[PO%5cC]PH%0<R<#:Rc#0Rr#0PO%5bPH%><PO%5aPH%1oRa#NR<#0PO%3{#X#CPGPIPB%:ERE#0,dBPI%8;R;#BPH%0?#:PO%5SPH%:@R@#0PO%0C#X#;#4#4#;#CPH%1kRk#>PO%5YPH%0k#:Rk#0PO%5ZRZPHPmPO%5TRT%5XRX'G%8>R>#B'G%:lRl#[RY,?HPOPX%1pRp#0#:,^HPOPTPHPqPO%8jRj#BRq,GTPH%0a#:PO%0m#7Rm#1#K#\#CPXPA%1}#3R}#1#3#KRX#8PZPA%1XRX#3#KRZ#1Ra#0RC#4#81?TjPI%5[R[P[PA%8}R}1?TAR[PI%5VRV1?T;PI%5WRWPVPAP}PWPAP}%5UP>%1a#3#8PT%;uRu#8%3C#K#7#;#J#9%8sRs,mT%;uRu#8RT,l[%0u#:#;Ru,^HRC%0uRa#8P[PTCk1?BT%:^R^#0R>#1#;#J#9P[PTCkPHP~POPBPHPrPOPBPHP>POPBPHP@POPBPHPkPO%C_,GHPHPlPO%0m#>#>#CPHQ01POPqPHP`PO%Co,GHPHPcPO%1<#3#;#3#X#C1mHs%;X#J#J#J#9%;a#J#J#95jH%8u,lCRC%1pRp#X#J#9,QTRT%1E#8/QF%1pRp#4#7RF#0RE#3Ru#>#9%1FRF#4#4#7#9'Q%\F#3#9%Np#4#7#>#9'QPB%1^#4R^#0#3Rp#4#4#>#9PO%5MRMC]RF%1D#7RD#0#3RH#4#3#9Ra,?BPO%Ba%1H#4#>,dBPN%5NRHPHP;%8ZPB%7D#4RD#3#;POPMPB%4D#;PO%7pRp#1RD#0RM#1RZ#0#4#9R;#BPB%0M#4RM#>PO%5I%BY'G%4E#3#7#9%:u#3#9'Q%1Z#3#9,Q;PB%0p#K#;PNPBPB%:M#3PIPBPB%>^#7#>#>POPBPB%KD#;PNPB%c6RNDMDMDMDM3DDMDMDMCHFW3D3D3D3DD6D6D6D6D6D6D6D6D63D3DCHCHCHCHFWCHCxCHCHD6D6FWD6D6D6D6D6FWD6D6D63DD6D6FWRD;<DRO/@OR^'@RM'@Rp'@R;,@wRZ,@wRu'@RE'@RY'@1I=eQ00PY1I8KQ02PE1IivPwPu1I79R9PwPZP9PwP;P9Q03Pp1Iz\PJPM1IzxPnP^1If]POPO1I2DRDPDFVFVFVFVFVg00^I#w=<=eg00_TRe1Fe8R=g00`gRDg00b83T7a8=<8K1UIB1ULB'Z1UPB5Of1UQB5Og1URB5Oh=<iv%v0g00cER05u6X06ADTFN9DCt5t6#`1sd5#`1rd0#`P:PyP4P8g00dQR09T=DRd9Te8R5#iAae8dC=%h5C==<z\P:PyP4P8g00e]R49T=DRD9Te8R=#iAae8DC=%h=C==<zxP3PI%q=R=PBC_P3PPP=PBC_'Z=<f]g00fiR],g0=<2]1g4]=<2]3R3R3R3R3Rdo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knLH2A : list kentry := Eval vm_compute in filter (kentry_vars_lt 81) knQ0A.
Definition rLB2A := Eval vm_compute in runTA scr0 (SS 0xa8810 srLHA [] knLH2A 102).
Definition knLc2A : list kentry := Eval vm_compute in kn_after rLB2A knLH2A.      (* [comment removed for export] *)
Definition knLr2A : list kentry := Eval vm_compute in keep_libA TSO LIBSTK [(48%nat, 65536)] [] knLc2A.
Definition rP2A := Eval vm_compute in runTA scr0 (SS 0xa8824 srLr0A [] knLr2A 134).
Definition knP2A : list kentry := Eval vm_compute in kn_after rP2A knLr2A.
Definition knQ2A : list kentry := Eval vm_compute in keep_pfA PSO [(48%nat, 65536)] knP2A.
(* [comment removed for export] *)
Definition rSt2A := Eval vm_compute in runTA (SCR [true] [] []) (SS 0xa891c srQ0A [] knLH2A 166).
Definition rSf2A := Eval vm_compute in runTA (SCR [false] [] []) (SS 0xa891c srQ0A [] knLH2A 166).
Definition srSt2A : list expr := Eval vm_compute in s_regs (fst (fst rSt2A)).
Definition srSf2A : list expr := Eval vm_compute in s_regs (fst (fst rSf2A)).
(* [comment removed for export] *)
Definition srF1A : list expr := Eval vm_compute in sr_after_call_j srSf2A (map ridx c_kept) 166.
Definition knF1A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knLH2A.
Definition rT1A := Eval vm_compute in runTA scr0 (SS 0xa8850 srF1A [] knF1A 198).
Definition srM1A : list expr := Eval vm_compute in s_regs (fst (fst rT1A)).
Definition knM1A : list kentry := Eval vm_compute in kn_after rT1A knF1A.
(* [comment removed for export] *)
Definition rT2fA := Eval vm_compute in runA (SCR [false] [] []) (SS 0xa85fc srM1A [] knM1A 198).
Definition rT2tA := Eval vm_compute in runA (SCR [true] [] []) (SS 0xa85fc srM1A [] knM1A 198).
Definition srF2A : list expr := Eval vm_compute in sr_after_call_j (s_regs (fst (fst rT2fA))) (map ridx c_kept) 198.
Definition knF2A : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] (kn_after rT2fA knM1A).
(* [comment removed for export] *)
Definition rT3A := Eval vm_compute in runA scr0 (SS 0xa8684 srF2A [] knF2A 230).

Lemma loop2_itinerary_okA :
  ksubl_b knQ0A knLH2A = true /\ ksubl_b knQ2A knLH2A = true /\ kn_vars_lt 81 knLH2A = true
  /\ summE rLB2A = summE rLB1A /\ s_regs (fst (fst rLB2A)) = srLBA /\ kn_after rLB2A knLH2A = knLc2A
  /\ summE rP2A = (0x63d30, [SCStoreOk (SA (ELit 0) 0x674054) 1], 134%nat, 10%nat) /\ s_regs (fst (fst rP2A)) = srPA
  /\ forallb (fun K => existsb (kentry_eqb K) knP2A)
       [KWr (SA (EVar 0) (-8388608)) 8388608; KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1286144; KWord (SA (ELit 0) 6904512) 8 (EVar 3)] = true
  /\ (s_pc (fst (fst rSt2A)), snd (fst rSt2A), s_log (fst (fst rSt2A))) = (0xa8810, [SCBr true BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst rSf2A)), snd (fst rSf2A), s_log (fst (fst rSf2A))) = (0x7a198, [SCBr false BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (nth 1 srSf2A (ELit 0), nth 10 srSf2A (ELit 0), nth 21 srSt2A (ELit 0)) = (ELit 0xa8850, EVar 83, EAluw ALU_ADD (EVar 81) (ELit (-1)))
  /\ kn_after rSt2A knLH2A = knLH2A /\ kn_after rSf2A knLH2A = knLH2A.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0DrvE_defs ()) ["FPX_1"] "h01Kp%0p&0p;3p;1p;2p;4g007hj3=Tg0000j1`Tg000Pj2PTg001Uj10Tg0010j12Tg002:j1?Tg003Hj2ATg004Wj11Tg0056k200Tg006Hj1_Tg006hj38Tg007Hj4@Tg008Bj13Tg00<Nj19Tg009Pj1VTg00<lj2vTg00><j2uTg00?Lj4tTg00@\j3sTg00Alj2UTg009nj3|Tg00;<j4oTg00Q5j3NTg00C<j2>Tg00CWj2WTg00REj4]Tg00h6j2nTg00IIj2{Tg00D1j1fTg00E>j3KTg00Lnj1mTg00NXj2eTg00F8j1zTg00GEj3yTg00Gaj3xTg00JUj1jTg00E[j3lTg00Kaj1kTg00N<j4dTg00Ogj3wTf0R0#2#0#0#0p=D%00#0p=7%00#2p=4%00#0#0#9p=:%20#0p=5%00#0#0#0p=;%00#9p=ig00X6R1f2R2f1R3P0C@p=R%10#1p=H%10#1#1#1p=T%10#1#1#1#1#1#1#1p=S%00#0#9#?p=E%00#Vp=ag00R`S00?w30p=G%20#2#2#2p=F%20#2p=6%20#2#2#2#2#2#2#2p=[%90#?p=Zg00SLR4%32%33=84038p=BA84309842p=cf4R5f3R6A84309842584584p=J1A62?N30p=Y%V0,A3p=b%00#2#0#0p=X%00#0#0#0#0#0#0#0p=I%20#2#0#0p=r%90,A3p=~g00TZR7%96,A5?N23;80p=OA87309872p=CAs623=870p=Lf6R8f5R9;N5AN623=870587p=^%V6,A5?N23=870p=<AN623=870p=qA8730p=}%33=840p=pP5P61W23P0C]p=QP8P9P5P6P2P3P0C]C]p=gg00W6R5g00WVR97=0p=\A=623/>0p=M1>30,>2p=hA=599R2g00XTR3#`R6,P1R1g00YfR8'PS01/P8R:Q01P8P1P8g00ZER;#0R<#2R=#0R>#DR?#2#7R@#2#7S02#2#4#:g00ZjRA#?RB%2;RC#0RD#0RE#2RF#2RG#5#5RH#7#;#5#5RI#5#iRJ'ARKg00[HRL#1RM+00%_3RN583S035R6%HMRO#1RP#TRQ#HS04#1#H#SS05#SRR#1RS#1RT#1RU#1RV#1#H#T#SRW#H#T#S#SRX#1RY#1RZ#1R[#1R\#1#TR]#1R^#1R_#1R`#1Ra#1Rb#HRc#1Rd#1Re#1#HRf#1Rg#1Rh#1Ri#1Rj#1Rk#1Rl#1Rm#1Rn#1Ro#HRpC@PMC@Rq;=qS06%`4RrPB%7@S07#0S08#2R@#0#4#E%3LRL%2D#7Rs#0Rt#a#?'G%0<Ru#0Rv#0Rw#DRx#7#;#ES09%2H#5RH#5Ry#5#;#ES0:%3c%3]R]%3`S0;Q0;P]%3aS0<%3b%7IRI#iRb#?S0=%3_RaPB%2CRC#2R`#FRc#2#6#FRz#2R{#6#FR|#2R}#2#6R~#F#[#[#[#[#5#ZS0>%3SS0?%3TRT%3URU%3VRV%_4RS9Bno9Blm3cDJDJ9Bjk9Bhi9BfgDJ9Bde3cDJRe;=eRd%`7RgPKPM%9;Rf#?RiPL%2uRu#0#7Rh#0Rk#aRjPQ%VxRx#?,GLRmCYRlPLPxPQPBCYRxPL%2vRo#2#7Rn#aPQ%2@#4#ECYR@1ABbPMPi%0F#7,bLPQ%3RPL%0ERE#7RR#0PQ%0G#X#;#4#X#EPL%2=R=#DPQ%3\PL%0=#7R=#0PQP]PLP?PQ%3WRW%3[R['G%9DRD#?'G%0>R>#7R\#aRG,ALPQP[%2uRu#0#7,bLPQPWPLPkPQ%9<R<#?Rk,GWPL%0o#7PQ%0?#5R?#2#6#F#EP[PA%9zP]PA%0}R}#4#91AW<PM%3^R^P^PA%9cRc1AWAR^PM%3YRY1AWfPM%3ZRZPYPAPcPZPAPc%3XPD%9~PW%0wR~#0RD#7#;RX#9%6}#F#5#;#I#:%9wRw,vW%;XRX#9RW,u^%0X#7#;RX,bLR}%0XRc#9P^PWCt1ABW%2t#;#I#:P^PWCtPL%0`R`#7PQPBPL%0C#7RC#0PQPBPLPtPQPBPLPRPQPBPLP=PQ%Z~,GLPLP\PQ%0?#D#5#EPLPhPQPkPLPDPQ%Zv,GLPLPCPQ%2n#6#;#6#4#E1vLw%;{#I#I#I#:%;c#I#I#:5sL%9X,u}R}%2uRu#X#I#:,UWRW%2I#9/UJ%2uRu#4#5RJ#0RI#6RX#D#:%2JRJ#4#4#5#:'U%rJ#6#:%2u#7#4#5#D#:'UPB%2s#4Rs#0#6Ru#4#4#D#:PQ%3OROCYRJ%0H#6RH#4#6#:Rc,ABPQ%?c%2H#4#D,~BPP%3PRHPHPf%9|PB%4yRy#6#;PQPOPB%4y#;PQ%5uRu#2Ry#0RO#2R|#0#4#:Rf#?PB%0O#4RO#DPQ%3M%?G'G%4I#6#5#:%7X#6#:'U%2|#6#:,UfPB%0u#F#;PPPBPB%7O#6PMPBPB%Ds#5#D#DPQPBPB%Fy#;PPPB%_7RPDODODODO3CDODODOCLF^3C3C3C3CD<D<D<D<D<D<D<D<D<3C3CCLCLCLCLF^CLCqCLCLD<D<F^D<D<D<D<F^Ry'}3CCqRQ;=QRsQ01P8P1P8%2E#6#5#5#4#5#:Q035R6%1p#TRE#1R8#1RO#1#TRu#1Rf#1R|#1RX#1RI#1RG#1#H#SRH#1Rc#1R{#1Rw#1C@Q04C@Rn==:nRCQ02#4#6#E%?j,GLQ09Q0:P]Q0;%F>#5#6#4#6#ZPmQ0<PBQ0=PaPBQ0>Q0?PTAB{wS9BHc9cUVDJDJ9BIG9B|X9BufDJ,pO9BE8DJ,ppRp==rpR8g00[gRE#`RO,P1RfP1POQ08#0#5#:P9g00]7RuQ00%V;#?7|aRaPBCo=83N5R6%_EREC@R;;=;RXP1PO%2`#;#r#6#:g00]iPuPaPBCo=83N5R6PEC@RE==fERN1P44R3/P4RuP3P4P4P4Q07#2#X#EQ0<C@PaC@Ra;=aR`ANKMB=C@y9ClxRl==glRy/>yR@'>RK'>R|'>RG,>2RI'>RV'>RU'>Rc'>RH'>Rw,>2R{,>21W59R9P2P{P9P2PwP9Q06PH1W:qPdPcPrPePsPUPgPQPCPVP:PnP8PIPrPpP2PGP9PXP|1Wf;PNPKPfPEP`P@PuPaPyPy1WglRlPlC]DQDQFgDQDQDQDQFgFgg00fig00i@Rl'n#\g00jN/nl#\1{_l#\g00k[R_#fg00b8#f5=:Prg00_TRy1Py6R@g00`gR`;K_7K6#mg00lhPg1e_lg00n5P:g00oCR:#fPnPrAK@`:9Ky6#mg00Uj%z0g010O5y7X07ACWJP9C}x5x7#\P1POg011\R79K@`R}9Ky6Rx#jAly6}5R6%kxC@==f;PfP1POg012iRO9K@`R`9Ky6R@#jAly6`5R6%k@C@PEPuP3P4P4P4P4PMg0146RMPBCdP4Q04PMPBCdC@P4Q05g015DPBCdC@PaPg1e7lPl1eOl==glCMCMCM3hCMCMCMCM3h3hdo"). Qed.

Lemma tail_itinerary_okA :
  summE rT1A = (0xa85fc, [], 198%nat, 0%nat) /\ nth 2 srM1A (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit (-128))
  /\ (s_pc (fst (fst rT2fA)), snd (fst rT2fA), s_log (fst (fst rT2fA))) = (0x7a198, [SCBr false BC_LT (EVar 74) (ELit 0)], [])
  /\ (s_pc (fst (fst rT2tA)), snd (fst rT2tA), s_log (fst (fst rT2tA))) = (0x7a198, [SCBr true BC_LT (EVar 74) (ELit 0)], [])
  /\ (nth 1 (s_regs (fst (fst rT2fA))) (ELit 0), nth 10 (s_regs (fst (fst rT2fA))) (ELit 0)) = (ELit 0xa8684, EVar 48)
  /\ (nth 1 (s_regs (fst (fst rT2tA))) (ELit 0), nth 10 (s_regs (fst (fst rT2tA))) (ELit 0)) = (ELit 0xa8684, EVar 48)
  /\ sr_after_call_j (s_regs (fst (fst rT2tA))) (map ridx c_kept) 198 = srF2A
  /\ ksubl_b (keep_allocA MSO 4096 [] [] (kn_after rT2tA knM1A)) knF2A = true
  /\ summE rT3A = (0x11a3fc, [], 230%nat, 0%nat)
  /\ (nth 1 (s_regs (fst (fst rT3A))) (ELit 0), nth 2 (s_regs (fst (fst rT3A))) (ELit 0), nth 4 (s_regs (fst (fst rT3A))) (ELit 0), nth 10 (s_regs (fst (fst rT3A))) (ELit 0))
     = (ELit 1154104, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 6773376, ELit 0).
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0DrvE_defs ()) ["FPX_1"] "p;1p;2p;4p;3p;5g0000j1PTg000Pj2:Tg001Uj11Tg0010j19Tg006Hj1KTg004Wj10Tg007Hj42Tg007hj35Tg008Bj1@Tg009Pj1ZTg002:j1<Tg00Ogj3LTg00;<j4YTg006hj3BTg00<Nj1XTg00C<j26Tg00CWj2;Tg00REj4NTg00D1j1VTg00N<j4UTg00E>j3ETg00JUj1RTg00E[j3STg00Kaj1TTg00Lnj1QTg016Rj1bTg0170j1aTg017Sj4`Tg017oj3_Tg00NXj2^Tg019Bj5]Tg00h6j2\Tf0R0#9#1p=7%10#1p=3%10#9p=D%90#9p=4%10#Xp==g00X6R1f2R2f1R3P0C2p=F%00#0p=A%00#0#0#0p=I%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=>%00#0#0#0#0#0#0#0p=O%10#1#1#1p=Cg00SLR4P4P3P0C2p=H%@3=B40p=W%@2%@3=B405B4p=8AB4309B42p=Gf6R5f5R6f4R7f3R8P2P3P0CNCNp=JP4P2P3P0CUp=?A5823/60p=[A5567A5823/60'6p=Mg00XTR0#PR8,:1R3g00YfR2':R7/:2R6P7P2P3P2g00ZER5#1R9#9R:#1#7#3#DR;#1#4#4#4#7#=%K0R<5F8g00[HR=#0R>#0R?#AR@#A#IRA#0#A#>RB#0RC#0RD#0RE#0RF#0#A#I#ORG#0#O#>RH#0RI#0#IRJ#0#A#I#>#>#>#>#>#>#>RKC2P=C2RL;5Lg00R`RM%@=RN%39R9#1RO#1#3RP#Z#<3LRQ=54QRRg00[gRS#PRT,:3RUP3PT%95R5#4#D#C#4#3#4#3#=RVg00]ig01:TRW%@IRIg00Zj#<RXCY=B0<5F8%KSRSC2RY;5YRZP3PTg00WVR[PWPIPXCY=B0<9F8VPSC2RS=5USRV1:44R0%9;#D#C#7#=#<%@GRG'HR;;5;RW%P4R\%0KR]%9O#3#C#C#=#<%15R5#1RO#4R^#7#7#4#D#D#3#C#=#<R_%I]R]#@%0]R]%0]R]%0]#AR]%0]R]%0]R]%0]R]%0]R]%0]R]%0]R]%0]R]%@HRHALMGH%X5#<5LM%3^#7#3#C#7#7#3#=#<%0]#A#OR]%0]R]%0]R]%0]R]%K4'W3858F98DE98BC5GI,WJ3G383838389GXG383G5GQ58KRG;5GRJg00W6RI?5[[RCP7P2P3P2%99#7R9#9#3#D#4#4#4#7#==F8<%0]C2P=C2R==56=R]1:04R</:4R7P<P4P0P4%19#4#7#3#D#4#3#=#<%3O#Z#<9LMN'HP_C2PXC2R_;5_RN'6RM'6RO'6R9,6WRB'6RE'6RD'6RF'61;6LPRPF1;4QPZPD1;UYPVPE1;USPWPB1;0;RBPWP9PBPJPO1;\GPCPM1;I[P]PN1;6=1;7_CNFJFJFJFJP6g01;F#VPLP4P4P?g01<RPXCUPQPUP3PTg00_TRQ1:Q8RLg00`gRNg01=_3ER]7E8RM#RASQ8]5F8%TMC2PYPUP3PTg01>lRT9ELNR39EQ8RU#RASQ835F8%TUC2PSP0%QMRM=?>XA?AMX'HP;P0%QURU=?>XA?AUX'HP;P\%b:#aP2g01@9g01AEC`=_UKg01BRPIg01C_%CP#=1:21#KR2P2g01Di,^TD]g01F6'\P[P6g01GCR6#VP=P<P4P0P4AELN69EQ8#QRQ=?>XA??QX'HA?@QXC2A?AQXC2=57_C[FMFMFMFMdo"). Qed.
End FPX_1.
