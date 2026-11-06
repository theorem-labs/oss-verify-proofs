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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Eb0DrvEntry Eb0Drv_defs Eb0DrvRead Eb0DrvG_defs Eb0DrvC_defs Eb0DrvD_defs Eb0DrvLibL.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eb0DrvE_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond05C13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5summEC13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7DrvKitA:kentry_eqbC13~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:sr_vars_ltC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:kn_vars_ltC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26s_regsC13~~~C47Corelib5Lists7ListDef3nthC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0Drv_defs8kn_afterC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init5Logic3and01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs4srPAC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes4bool02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs3rPAC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvD_defs5rLB1AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs4knPAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs4rQtAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs4rQfAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5knQ0AC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7DrvKitA7ksubl_bC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs6knLH2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5knQ2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5rLB2AC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvD_defs5srLBAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs6knLc2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs4rP2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5knP2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5rSt2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5rSf2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs6srSf2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs6srSt2AC13~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib5Lists7ListDef3mapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymDrive?sr_after_call_jC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0Drv_defs;keep_allocAC13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs4rT1AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5srM1AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5rT2fAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5rT2tAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24ridxC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0Drv_defs6c_keptC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5srF2AC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eb0Drv_defs3MSOC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5knM1AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs5knF2AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eb0DrvE_defs4rT3AC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition IMG_PF_A : list (Z * Z) :=
  [(0x10000, 0x13f000); (0x141fe8, 0x1421c0); (0x1422a8, 0x142a10); (0x668750, 0x67a128); (0x67a130, 0x67a178); (0x67a194, 0x67a1a8);
   (0x67a1b0, 0x69a998); (0x69ada8, 0x69b638); (0x69b640, 0x69c000)].
Definition keep_pfA (so : Z) (bls : list (nat * Z)) (kn : list kentry) : list kentry := kn_keep 0 so 3232 bls [] [] IMG_PF_A IMG_RW_A kn.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition PSO : Z := -288.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition knLr0A : list kentry := Eval vm_compute in keep_libA TSO LIBSTK [(48%nat, 65536)] [] knLc1A.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition rPA := Eval vm_compute in runTA scr0 (SS 0xa904c srLr0A [] knLr0A 134).
Definition srPA : list expr := Eval vm_compute in s_regs (fst (fst rPA)).
Definition knPA : list kentry := Eval vm_compute in kn_after rPA knLr0A.
(* [comment removed for export] *)
Definition srQ0A : list expr := Eval vm_compute in sr_after_call_j srPA (map ridx c_kept) 134.
Definition knQ0A : list kentry := Eval vm_compute in keep_pfA PSO [(48%nat, 65536)] knPA.
(* [comment removed for export] *)
Definition rQtA := Eval vm_compute in runTA (SCR [true] [] []) (SS 0xa9144 srQ0A [] knQ0A 166).
Definition rQfA := Eval vm_compute in runTA (SCR [false] [] []) (SS 0xa9144 srQ0A [] knQ0A 166).

Definition summE (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), length (s_log (fst (fst r)))).

Lemma loop_itinerary_okA :
  summE rPA = (0x64558, [SCStoreOk (SA (ELit 0) 0x678754) 1], 134%nat, 10%nat)      (* [comment removed for export] *)
  /\ snd (fst rLB1A) = [SCStoreOk (SA (ELit 0) 0x678754) 1]                              (* [comment removed for export] *)
  /\ (nth 1 srPA (ELit 0), nth 2 srPA (ELit 0), nth 10 srPA (ELit 0), nth 11 srPA (ELit 0), nth 19 srPA (ELit 0))
     = (ELit 0xa9144, EAlu ALU_ADD (EVar 0) (ELit (-288)), ELit 85823, EAlu ALU_ADD (EVar 0) (ELit (-264)), ELit 0)
  (* [comment removed for export] *)
  /\ forallb (fun K => existsb (kentry_eqb K) knPA)
       [KWr (SA (EVar 0) (-8388608)) 8388608; KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1306624; KWord (SA (ELit 0) 6922688) 8 (EVar 3)] = true
  /\ sr_vars_lt 134 srPA = true /\ kn_vars_lt 134 knPA = true
  /\ (s_pc (fst (fst rQtA)), snd (fst rQtA), s_log (fst (fst rQtA))) = (0xa9038, [SCBr true BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst rQfA)), snd (fst rQfA), s_log (fst (fst rQfA))) = (0x7a9c0, [SCBr false BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (nth 1 (s_regs (fst (fst rQfA))) (ELit 0), nth 10 (s_regs (fst (fst rQfA))) (ELit 0)) = (ELit 0xa9078, EVar 83)
  /\ kn_after rQtA knQ0A = knQ0A /\ kn_after rQfA knQ0A = knQ0A.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0DrvE_defs ()) ["FPX_1"] "h01Kp%0p;1p;2p;3p;4g0000j1aTg000Pj2GTg0010j11Tg001Uj10Tg002:j1@Tg003Hj2?Tg004Wj12Tg0056j2nTg006Hj1cTg006hj3ATg007Hj4>Tg007hj3:Tg008Bj15Tg009Pj1XTg009nj3oTg00;<j4eTg00<Nj18Tg00<lj2mTg00><j2lTg00?Lj4kTg00@\j3jTg00Alj2QTg00C<j2BTg00CWj2HTg00D1j1xTg00E>j3STg00E[j3`Tg00F8j1wTg00GEj3vTg00Gaj3uTg00H=j2tTg00IIj2sTg00JUj1iTg00Kaj1hTg00Lnj1rTg00N<j4bTg00NXj2gTg00Ogj3qTg00Q5j3OTg00REj4fTf0R0#0#0#0p=D%10#0p=7%10#1p=3%00#0#0#8p=9%00#8p=p%20#2#2#2p=U%20#2p=L%20#2#2#2#2#2#2#2p=C%00#0p==%10#0#0#0p=<%00#1#0#0p=[%80#@p=F%00#Xp=Zg00R`R1f1R2;q0p=Ig00SLR3P3P2P0C>p=Y%10#1#0#0p=^%10#1#1#1p=Mf2R4P3P2P0C>p=P%00#1p=6%X0,?2p=]f3R5/?4?O20p=\%80,?2p=d%00#0#0#0p=;%00#0#0#0#0#0#0#0p=Kg00TZR6f4R7%85'??O42;A0p=NAA6209A64p=EAj542=A60p=Jf6R8f5R9;O7AO542=A605A6p=W%X5,?7?O42=A60p=4AO542=A60p=yP8P9P7P5P4P2P0CfCfp=VP3P2g00UjR5P0Cbp=Tg00W6R7g00WVR97:0p=_1B20,B4p=Rg00X6R4g00XTR2#aR8'GR:g00YfR;'GR</G;R=P<P;P:P;P4P8g00ZER;#1R<#0R>#0R?#1R@#DRA#7#7#7#3#9g00ZjRB#@RC%1@R@#1#7RD#D#3#7#7#7RE#7#pRF'?RGg00[HRH#2RI'n%c2RJ5A2RKC>%2IRL#2RM#2RN#URO#LRP#2RQ#CRR#L#CRS#2#L#C#CRT#L#U#C#CRU#2RV#2RW#2RX#2RY#2#URZ#2R[#2R\#LR]#2#L#U#C#C#CR^#2R_#2R`#2Ra#2Rb#2Rc#2#L#U#CRdC>PPC>Re;:eA:8KKS001G33Rf/G3Rg/G3Rh/G3Ri%0;Rj#1Rk#0Rl#1#=Rm#<Rn#1#[#[#F%5HRH%0jRo#1Rp#DRq#0Rr#ZRs#@'I'Y%0lRl#3#^#3#M#F5Pf%0oRo#0Rt#1#=#ZRu#@,IHRv5Pg=PhCRw;:wS01A:799Rxg00[gRy#aRz,G:R{P:PzP4P8%=nRn#6#3#9P9g00]7R|%5\%X;#@5o1R1PCCe=A2JC>%cyRyC>R\;:\S02P:PzP4P8%1<R<#1R}#0R~#1#[#3#<#9g00]iP|P1PCCe=A2JC>PyC>Ry=:{yRJ%1nRn#3#<#F%5]'YR]=:f]R2%a6R11?HsPOPv%=~R~#0,]HPO%5`PH%1}R}#DPO%5_PH%0tR_#0R`#=RvPO%5^PHPuPOPCC\RuPH%1>R^#1#=#ZPO%5cC\PH%0<R<#=Rc#0Rs#0PO%5bPH%<<PO%5aPH%1oRa#1R<#DPO%6n#^#FPGPIPC%=ERE#0,dCPI%8;R;#@PHPAPO%5SPH%D?R?#0PO%0@#<#6#3#6#6#;#FPH%1kRk#<PO%5YPH%DkRk#0PO%5ZRZPH%0mRmPO%5TRT%5XRX'I%8>R>#@'I%=lRl#ZRY,?HPOPX%1pRp#D,]HPOPTPHPrPO%8jRj#@Rr,ITPH%DaPO%3mRm#<#7#[#FPXPB%1}#3R}#1#3#MRX#8PZPB%1XRX#3#MRZ#1Ra#0R@#6#81?TjPI%5[R[P[PB%8}R}1?TBR[PI%5VRV1?T;PI%5WRWPVPBP}PWPBP}%5UP>%1a#3#8PT%;vRv#8%3@#M#7#;#K#9%8tRt,mT%;vRv#8RT,l[%Dv#;Rv,]HR@%0vRa#8P[PTCk1?CT%=^R^#0R>#1#<#K#9P[PTCkPHP~POPCPHPsPOPCPHP>POPCPHP?POPCPHPkPO%F_,IHPHPlPO%=m#7#3#;#FPHPqPOPrPHP`PO%Fo,IHPHPcPO%1<#<#M#6#^#F1mHt%;X#K#K#K#9%;a#K#K#95jH%8v,l@R@%1p#3#7#K#9,QTRT%1E#8/QF%7lRl#=RF#0RE#0Rp#1Rv#7#7#9%3E#<#9'Q%1F#6#6#6#9%1l#6#;#7#9'QPC%1^#7#7R^#0Rl#0RF#0#3#<#9PO%5MRMC\RE%1D#;RD#6RH#6#3#9Ra,?CPO%@a%1H#6#<,dCPN%5NRHPHP;%8ZPC%1D#6RD#3#;POPMPC%6D#;PO%1l#=Rl#0RD#1RM#0#6#9RZ#@PC%0D#6RD#<PO%5I%@Y'I%0p#;#9%6v#6#9'Q%1M#3#9,QZPC%3F#M#;PNPCPC%=D#3PIPCPC%7^#6#<#<POPCPC%Ml#;PNPC%c6RNDNDNDNDN3EDNDNDNCJFW3E3E3E3ED4D4D4D4D4D4D4D4D43E3ECJCJCJCJFWCJCyCJCJD4D4FWD4D4D4D4D4FWD4D4D43ED4D4FWRl;:lRO/BOR^'BRD'BRF'BRZ,BxRM,BxRv'BRp'BRY'B1H=eQ00PY1H8KQ01Pp1HiwPxPv1H79R9PxPMP9PxPZP9Q02PF1H{\PJPD1H{yP2P^1Hf]POPO1H1lRlPlFVFVFVFVFVg00^I#x=:=eg00_TRe1Ge8R=g00`gRlg00b83S7`8=:8K1TIC1TLC'Y1TPC5Pf1TQC5Pg1TRC5Ph=:iw%w0g00cER05v6X06AETEN9E@u5u6#_1td5#_1sd0#_P:PzP4P8g00dQR09S=lRd9Se8R5#iA`e8dC>%h5C>=:{\P:PzP4P8g00e]R49S=lRl9Se8R=#iA`e8lC>%h=C>=:{yP3PI%r=R=PCCbP3PPP=PCCb'Y=:f]g00fiR],g0=:1]1g4]=:1]3R3R3R3R3Rdo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knLH2A : list kentry := Eval vm_compute in filter (kentry_vars_lt 81) knQ0A.
Definition rLB2A := Eval vm_compute in runTA scr0 (SS 0xa9038 srLHA [] knLH2A 102).
Definition knLc2A : list kentry := Eval vm_compute in kn_after rLB2A knLH2A.      (* [comment removed for export] *)
Definition knLr2A : list kentry := Eval vm_compute in keep_libA TSO LIBSTK [(48%nat, 65536)] [] knLc2A.
Definition rP2A := Eval vm_compute in runTA scr0 (SS 0xa904c srLr0A [] knLr2A 134).
Definition knP2A : list kentry := Eval vm_compute in kn_after rP2A knLr2A.
Definition knQ2A : list kentry := Eval vm_compute in keep_pfA PSO [(48%nat, 65536)] knP2A.
(* [comment removed for export] *)
Definition rSt2A := Eval vm_compute in runTA (SCR [true] [] []) (SS 0xa9144 srQ0A [] knLH2A 166).
Definition rSf2A := Eval vm_compute in runTA (SCR [false] [] []) (SS 0xa9144 srQ0A [] knLH2A 166).
Definition srSt2A : list expr := Eval vm_compute in s_regs (fst (fst rSt2A)).
Definition srSf2A : list expr := Eval vm_compute in s_regs (fst (fst rSf2A)).
(* [comment removed for export] *)
Definition srF1A : list expr := Eval vm_compute in sr_after_call_j srSf2A (map ridx c_kept) 166.
Definition knF1A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knLH2A.
Definition rT1A := Eval vm_compute in runTA scr0 (SS 0xa9078 srF1A [] knF1A 198).
Definition srM1A : list expr := Eval vm_compute in s_regs (fst (fst rT1A)).
Definition knM1A : list kentry := Eval vm_compute in kn_after rT1A knF1A.
(* [comment removed for export] *)
Definition rT2fA := Eval vm_compute in runA (SCR [false] [] []) (SS 0xa8e24 srM1A [] knM1A 198).
Definition rT2tA := Eval vm_compute in runA (SCR [true] [] []) (SS 0xa8e24 srM1A [] knM1A 198).
Definition srF2A : list expr := Eval vm_compute in sr_after_call_j (s_regs (fst (fst rT2fA))) (map ridx c_kept) 198.
Definition knF2A : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] (kn_after rT2fA knM1A).
(* [comment removed for export] *)
Definition rT3A := Eval vm_compute in runA scr0 (SS 0xa8eac srF2A [] knF2A 230).

Lemma loop2_itinerary_okA :
  ksubl_b knQ0A knLH2A = true /\ ksubl_b knQ2A knLH2A = true /\ kn_vars_lt 81 knLH2A = true
  /\ summE rLB2A = summE rLB1A /\ s_regs (fst (fst rLB2A)) = srLBA /\ kn_after rLB2A knLH2A = knLc2A
  /\ summE rP2A = (0x64558, [SCStoreOk (SA (ELit 0) 0x678754) 1], 134%nat, 10%nat) /\ s_regs (fst (fst rP2A)) = srPA
  /\ forallb (fun K => existsb (kentry_eqb K) knP2A)
       [KWr (SA (EVar 0) (-8388608)) 8388608; KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1306624; KWord (SA (ELit 0) 6922688) 8 (EVar 3)] = true
  /\ (s_pc (fst (fst rSt2A)), snd (fst rSt2A), s_log (fst (fst rSt2A))) = (0xa9038, [SCBr true BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst rSf2A)), snd (fst rSf2A), s_log (fst (fst rSf2A))) = (0x7a9c0, [SCBr false BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
  /\ (nth 1 srSf2A (ELit 0), nth 10 srSf2A (ELit 0), nth 21 srSt2A (ELit 0)) = (ELit 0xa9078, EVar 83, EAluw ALU_ADD (EVar 81) (ELit (-1)))
  /\ kn_after rSt2A knLH2A = knLH2A /\ kn_after rSf2A knLH2A = knLH2A.
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0DrvE_defs ()) ["FPX_1"] "h01Kp%0p&0p;3p;1p;2p;4g007hj3>Tg0000j1aTg000Pj2QTg001Uj10Tg0010j12Tg002:j1?Tg003Hj2ATg004Wj11Tg0056k201Tg006Hj1`Tg006hj35Tg007Hj4CTg008Bj13Tg00<Nj18Tg009Pj1XTg00<lj2wTg00><j2vTg00?Lj4uTg00@\j3sTg00Alj2VTg009nj3}Tg00;<j4pTg00Q5j3NTg00C<j2;Tg00CWj2YTg00REj4]Tg00h6j2oTg00IIj2|Tg00D1j1fTg00E>j3KTg00Lnj1nTg00NXj2eTg00F8j1{Tg00GEj3zTg00Gaj3yTg00JUj1lTg00E[j3mTg00Kaj1kTg00N<j4hTg00Ogj3xTf0R0#0#0p=B%20#0#0#0p=@%20#0p=7%00#0#0#8p=9%00#0#0p=H%20#2#2#0p=W%00#8p=jg00X6R1f2R2f1R3P0CCp=U%10#1p=I%10#1#1#1p=S%10#1#1#1#1#1#1#1p=R%20#2p=4%00#0#8#?p=F%00#Xp=^g00R`S00?x30p=G%00#0#0#0p==%20#2#2#2p=:%80#?p=[g00SLR4%32%33=54035p=DA54309542p=cf4R5f3R6A54309542554554p=J1A62?N30p=Z%X0,A3p=b%00#2p=6%00#2#0#0p=i%00#0#0#0#0#0#0#0p=M%20#2#0#0p=t%80,A3p>00g00TZR7%86,A5?N23;50p=PA57309572p=EAs623=570p=Lf6R8f5R9;N5AN623=570557p=_%X6,A5?N23=570p=<AN623=570p=rA5730p=~%33=540p=qP5P61Y23P0C]p=TP8P9P5P6P2P3P0C]C]p=gg00W6R5g00WVR97>0p=\A>623/;0p=O1;30,;2p=dA>599R2g00XTR3#aR6,Q1R1g00YfR8'QS01/Q8R:Q01P8P1P8g00ZER;#0R<#2R=#0R>#2#BR?#@R@#7#7S02#7#9g00ZjRA#?RB%2;RC#0RD#0RE#2RF#2RG#2#7RH#H#W#7#7RI#7#jRJ'ARKg00[HRL#1RM+01%`3RN553S035U6%IMRO#1RP#SRQ#IS04#1#I#RS05#RRR#1RS#1RT#1RU#1RV#1#I#S#RRW#I#S#R#RRX#1RY#1RZ#1R[#1R\#1#SR]#1R^#1R_#1R`#1Ra#1Rb#IRc#1Rd#1Re#1#IRf#1Rg#1Rh#1Ri#1Rj#1Rk#1Rl#1Rm#1Rn#1Ro#IRpCCPMCCRq;>qS06%a4RrPB%B@S07#2S08#0R@#0#4#F%3LRL%2D#BRs#0Rt#^#?'G%0<Ru#0Rv#0Rw#@Rx#B#=#FS09%2H#=RH#2Ry#7#=#FS0:%3c%3]R]%3`S0;Q0;P]%3aS0<%3b%BIRI#jRb#?S0=%3_RaPB%2CRC#2R`#:Rc#2#4#:Rz#2R{#4#:R|#2R}#2#4R~#4#:#:#:#:#:#:#:#:#W#[S0>%3SS0?%3TRT%3URU%3VRV%`4RS9Dno9Dlm3cDJDJ9Djk9Dhi9DfgDJ9Dde3cDJRe;>eRd%a7RgPKPM%8;Rf#?RiPL%2uRu#HRh#0Rk#^RjPQ%XxRx#?,GLRmCZRlPLPxPQPBCZRxPL%2vRo#2Rn#B#^PQ%2@#4#FCZR@1ABbPMPi%HFRF,bLPQ%3RPL%HERE#0PQ%0G#@#6#4#6#i#FPL%2=R=#@PQ%3\PL%H=R=#0PQP]PL%0?R?PQ%3WRW%3[R['G%8DRD#?'G%0>R>#BR\#^RG,ALPQP[%2uRu#H,bLPQPWPLPkPQ%8<R<#?Rk,GWPL%HoPQ%4?R?#@#7#6#FP[PA%8zP]PA%0}R}#6#81AW<PM%3^R^P^PA%8cRc1AWAR^PM%3YRY1AWfPM%3ZRZPYPAPcPZPAPc%3XPD%8~PW%0wR~#0RD#B#=RX#8%:}#W#=#M#9%8wRw,wW%=XRX#8RW,v^%HX#=RX,bLR}%0XRc#8P^PWCu1ABW%2t#@#M#9P^PWCuPL%0`R`#BPQPBPL%HCRC#0PQPBPLPtPQPBPLPEPQPBPLP=PQ%[~,GLPLP\PQ%B?#7#t#FPLPhPQPkPLPDPQ%[v,GLPLPCPQ%2n#@#:#6#4#F1wLw%={#M#M#M#9%=c#M#M#95sL%8X,v}R}%2u#W#M#9,VWRW%2I#8/VJ%7\R\#BRJ#0RI#0Ru#2RX#7#7#9%4I#@#9'V%2J#6#6#6#9%2\#6#=#7#9'VPB%2s#7#7Rs#0R\#0RJ#0#4#@#9PQ%3OROCZRI%6HRH#6#4#9Rc,ABPQ%?c%2H#6#@-00BPP%3PRHPHPf%8|PB%6yRy#4#=PQPOPB%6y#=PQ%2\#BR\#0Ry#2RO#0#6#9R|#?PB%0y#6Ry#@PQ%3M%?G'G%0u#=#9%6X#6#9'V%2O#4#9,V|PB%4J#:#=PPPBPB%By#4PMPBPB%7s#6#@#@PQPBPB%:\#=PPPB%`7RPDPDPDPDP3EDPDPDPCLF_3E3E3E3ED<D<D<D<D<D<D<D<D<3E3ECLCLCLCLF_CLCrCLCLD<D<F_D<D<D<D<F_R\'~3ECrRQ;>QRsQ01P8P1P8%7F#7#7#4#9Q035U6%1p#SRF#1R8#1Ry#1#SRJ#1R|#1RO#1RX#1Ru#1RG#1#I#RRf#1RH#1Rc#1R{#1CCQ04CCRw=>:wRnQ02#0#6#F%?j,GLQ09Q0:P]Q0;%4>#t#4#:#[PmQ0<PBQ0=PaPBQ0>Q0?PTADc{S9DfH9cUVDJDJ9DuG9DOX9DJ|DJ,qy9DF8DJ,qpRp=>rpR8g00[gRF#aRy,Q1R|P1PyQ07#6#4#9P9g00]7RJQ00%X;#?7}aRaPBCp=53N5U6%`FRFCCR;;>;RXP1Py%2`#i#4#@#9g00]iPJPaPBCp=53N5U6PFCCRF=>|FRN1Q44R3/Q4RJP3P4P4P4Q08#W#FQ0<CCPaCCRa;>aR`ANKMB=E@\9ElxRl=>glR\/;\R@';RK';RO';RG,;2Ru';RV';RU';RH';Rf';R{,;2Rc,;21Y59R9P2PcP9P2P{P9Q06Pf1Y:qPdPHPrPePsPUPgPQPnPVP:PwP8PuPrPpP2PGP9PXPO1Y|;PNPKP|PFP`P@PJPaP\P\1YglRlPlC]DTDTFgDTDTDTDTFgFgg00fig00i@Rl'o#\g00jN/ol#\1|_l#\g00k[R_#fg00b8#f5>:Prg00_TR\1Q\6R@g00`gR`;K_7K6#ng00lhPg1e_lg00n5P:g00oCR:#fPwPrAK@`:9K\6#ng00Uj%{0g010O5z7X07AEWIP9E}x5y7#\P1Pyg011\R79K@`R}9K\6Rx#lAm\6}5U6%kxCC=>|;P|P1Pyg012iRy9K@`R`9K\6R@#lAm\6`5U6%k@CCPFPJP3P4P4P4P4PMg0146RMPBChP4Q04PMPBChCCP4Q05g015DPBChCCPaPg1e7lPl1eyl=>glCOCOCO3dCOCOCOCO3d3ddo"). Qed.

Lemma tail_itinerary_okA :
  summE rT1A = (0xa8e24, [], 198%nat, 0%nat) /\ nth 2 srM1A (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit (-128))
  /\ (s_pc (fst (fst rT2fA)), snd (fst rT2fA), s_log (fst (fst rT2fA))) = (0x7a9c0, [SCBr false BC_LT (EVar 74) (ELit 0)], [])
  /\ (s_pc (fst (fst rT2tA)), snd (fst rT2tA), s_log (fst (fst rT2tA))) = (0x7a9c0, [SCBr true BC_LT (EVar 74) (ELit 0)], [])
  /\ (nth 1 (s_regs (fst (fst rT2fA))) (ELit 0), nth 10 (s_regs (fst (fst rT2fA))) (ELit 0)) = (ELit 0xa8eac, EVar 48)
  /\ (nth 1 (s_regs (fst (fst rT2tA))) (ELit 0), nth 10 (s_regs (fst (fst rT2tA))) (ELit 0)) = (ELit 0xa8eac, EVar 48)
  /\ sr_after_call_j (s_regs (fst (fst rT2tA))) (map ridx c_kept) 198 = srF2A
  /\ ksubl_b (keep_allocA MSO 4096 [] [] (kn_after rT2tA knM1A)) knF2A = true
  /\ summE rT3A = (0x11eba4, [], 230%nat, 0%nat)
  /\ (nth 1 (s_regs (fst (fst rT3A))) (ELit 0), nth 2 (s_regs (fst (fst rT3A))) (ELit 0), nth 4 (s_regs (fst (fst rT3A))) (ELit 0), nth 10 (s_regs (fst (fst rT3A))) (ELit 0))
     = (ELit 1172448, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 6791552, ELit 0).
Proof.
ltac2:(KReplay.run1 (kr_t_Eb0DrvE_defs ()) ["FPX_1"] "p;1p;2p;4p;3p;5g0000j1PTg000Pj2<Tg001Uj11Tg0010j1:Tg006Hj1KTg004Wj10Tg007Hj42Tg007hj33Tg008Bj1BTg009Pj1ZTg002:j1=Tg00Ogj3LTg00;<j4YTg006hj3DTg00<Nj1XTg00C<j24Tg00CWj2;Tg00REj4NTg00D1j1VTg00N<j4UTg00E>j3ETg00JUj1RTg00E[j3STg00Kaj1TTg00Lnj1QTg016Rj1bTg0170j1aTg017Sj4`Tg017oj3_Tg00NXj2^Tg019Bj5]Tg00h6j2\Tf0R0#:#1p=9%10#1p=8%:0#:p=5%10#:p=6%10#Xp=>g00X6R1f2R2f1R3P0C2p=F%00#0p=C%00#0#0#0p=I%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=?%00#0#0#0#0#0#0#0p=O%10#1#1#1p=Ag00SLR4P4P3P0C2p=H%B3=D40p=W%B2%B3=D405D4p=7AD4309D42p=Gf6R5f5R6f4R7f3R8P2P3P0CNCNp=JP4P2P3P0CUp=@A3823/40p=[A3567A3823/40'4p=Mg00XTR0#PR8,<1R3g00YfR2'<R7/<2R6P7P2P3P2g00ZER5#1R9#:R:#1#9#8#5#9R;#1#6#8#9#>%K0R<5F8g00[HR=#0R>#0R?#CR@#C#IRA#0#C#?RB#0RC#0RD#0RE#0RF#0#C#I#ORG#0#O#?RH#0RI#0#IRJ#0#C#I#?#?#?#?#?#?#?RKC2P=C2RL;3Lg00R`RM%B=RN%89R9#1RO#1#8RP#Z#=3LRQ=34QRRg00[gRS#PRT,<3RUP3PT%:5R5#5#6#6#8#5#9#A#>RVg00]ig01:TRW%BIRIg00Zj#=RXCY=D0<5F8%KSRSC2RY;3YRZP3PTg00WVR[PWPIPXCY=D0<9F8VPSC2RS=3USRV1<44R0%:;#6#6#9#>#=%BGRG'HR;;3;RW%P4R\%0KR]%:O#8#A#A#>#=%15R5#1RO#5R^#5#6#A#5#8#A#>#=R_%I]R]#B%0]R]%0]R]%0]#CR]%0]R]%0]R]%0]R]%0]R]%0]R]%0]R]%0]R]%BHRHALMGH%X5#=5LM%6^#A#5#9#9#9#8#>#=%0]#C#OR]%0]R]%0]R]%0]R]%K4'W3757F97DE97BC5GI,WJ3G373737379GXG373G5GQ57KRG;3GRJg00W6RI?3[[RCP7P2P3P2%:9#5#9R9#:#6#5#6#8#9#>=F8<%0]C2P=C2R==36=R]1<04R</<4R7P<P4P0P4%19#6#5#5#A#>#=%8O#Z#=9LMN'HP_C2PXC2R_;3_RN'4RM'4RO'4R9,4WRB'4RE'4RD'4RF'41;6LPRPF1;4QPZPD1;UYPVPE1;USPWPB1;0;RBPWP9PBPJPO1;\GPCPM1;I[P]PN1;6=1;7_CNFJFJFJFJP6g01;F#VPLP4P4P?g01<RPXCUPQPUP3PTg00_TRQ1<Q8RLg00`gRNg01=_3ER]7E8RM#RASQ8]5F8%TMC2PYPUP3PTg01>lRT9ELNR39EQ8RU#RASQ835F8%TUC2PSP0%QMRM=@>XA@AMX'HP;P0%QURU=@>XA@AUX'HP;P\%b:#aP2g01@9g01AEC`=_UKg01BRPIg01C_%AP#>1<21#KR2P2g01Di,^TD]g01F6'\P[P6g01GCR6#VP=P<P4P0P4AELN69EQ8#QRQ=@>XA@?QX'HA@@QXC2A@AQXC2=37_C[FMFMFMFMdo"). Qed.
End FPX_1.
