(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HImage HZBridge HSysStep HSFModel CellsX HArr TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit AW_LargeAlloc1 AS_Refill1 AllocTacX AllocPerfKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AllocPerfKit2 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I69OSSVerify5KrLib3bpA2Rt:AS_Refill14RENV00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt<AllocPerfKit7out_imgC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01C69OSSVerify5KrLib3bpA2Rt<AllocPerfKit@out_img_disjointC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib3bpA2Rt:AS_Refill1>renv_transportC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpA2Rt8AsShadow3memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame3ivlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt5ASegs5asegsC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma rrenv_transport_img : forall tp TSD CTX TH sb ARI m m' W,
    AS_Refill1.RENV tp TSD CTX TH sb ARI m -> munch W m m' -> wmono asegs m m' -> out_img W ->
    65536 <= bv_unsigned tp + -88 -> bv_unsigned tp + -88 + 8 <= 7233536 ->
    65536 <= TSD -> TSD + 8 <= 7233536 ->
    disjoint_from W (CTX + 152) 8 ->
    AS_Refill1.RENV tp TSD CTX TH sb ARI m'.
Proof.
ltac2:(KReplay.run1 (kr_t_AllocPerfKit2 ()) ["HCW"] "h07__arithh14__ffh28__varmaph35__with44__x1h53ARIh63CTXh72D1h82D2h92DCh:1Eh;2HWh<2MUh=2T1h>2T2h?2THh@3TSDhA1WhB2WMhC1mhD2m'hE2sbhF2tpp;1p;7p;3p;2p;4p;Mp;8g0000j11Tg000Uj1ETg0013j1DTg001Vj1aTg0028j1GTg002Xj7ZTg003Uj3YTg004Rj3VTg005Oj1RTg006Oj2@Tg0079j1;Tg007^j1\Tg008<j2=Tg008Yj20Tg0095j1?Tg009Sj3XTg00:Xj1WTg00;8j1UTg00;Vj1TTg00<4j1STg00<_j2QTg00=Aj2NTg00=[j2MTg00>Gj3OTg00>aj3LTg00?@j4PTg00@2j2CTg00@Uj78Tg00A^j2KTg00B<j2`Tg00B_j1^Tg00CAlM]Tg00DFj4HTg00E1j7FTg00EUj3ITg00F8j8[Tf0R0#1#1p=<%10#1#1#1p=>%10#1#1#?p=6%;0#1p=:%10#;p=9%;0#;#1#1p=Bf2R1f1R2'=/00p=4%;0#;p=5g00F\R3/C0p=2P1g00G:R4g00GYR5P5g00H9R6P3P2g00HYR7P0CHg00I@R8FFp=3f3R9P4P5P5P6P3AI312P7P0CHP8FFp=7AI320p=_P9P4P5P5P6P1P2P0G[p=A%10#?p=Jg00I`R4#1R8#1R7#1R:#1R;#<R<#ER=#DR>g00JE%E:#D#a\>g00K=#Gf8R>f7R?f6R@f5RAf4RBP9P1FZAY291g00L8?VB9%R9%1<#<#>#6R<f<RC,@=%;8#:#<#\R8'='0f=RD,@=/=8%?:RE%;4#9#B#B#>#>#6RF3410<Df>RG?4EF%57#6,=G=X>EfAR7f@RHf?PGPDPCf;f:f9RCP>P?P@PC%;4R@#<R?#1R>#5RD#;RG#1#5#5#9RI#;#<#6RJPEPAg00LoRK#WRL%GKRK%U3RM%T3RN%S3RO%2<RP%2JRQ331QO6R6P0P1g00M[RRg00N;RS'N1M01=ORSdg00N[RS=L32CPRRb1b2b310<JP0b0PLPKPMPNPOPQ%2ERQ%2FRTC7P6PRb1b2b3A4JEFP0b0PLPKPMPN1C3SRJ=3OQP6PRb1b2b310SEP0b0RUF8PC1@=7/=8PEPAPLPK1K32RVPNPO1`34RW%28'_RX93OPRY%^5R5PYCAP6PRb1b2b3X431=08RY,0<1=28R8,0<[^43P0fB,@=R=PAO2b0PLPKPVPNPOPOPXPQPTC7RXP5PXCAP6PRb1b2b3X43A4YEFA48EF[^43P0P=PBO2b0PUF8PCPHPEPAPLPKPVPNPOA3OPWRHP5PHCAP6PRb1b2b3X4310<010<2[^43P0P7P9O2b0PLPKPVPNPOPOPWPQPTC7RWP5PWCAP6PRb1b2b3X43A40EFA42EF[^43P0P7P1O2b0PUF8P0PC%1I#5#:#JRI%?4R4PAPLPKPMPN%2IR193OPP6PRb1b2b310<IP0b0PLPKPMPNPOP1%24R1PTC7P6PRb1b2b3A4I4FP0b0PLPKPMPNA3OJ1P6PRb1b2b310S4P0b0RIF8PC%1>R7#9#:#5#9#:#<#6R2%5@#6R@PAPLPKPMPN%22RW93OPP6PRb1b2b310<2P0b0PLPKPMPNPOPW%2@RWPTC7P6PRb1b2b3A42@FP0b0PLPKPMPNA3OJWP6PRb1b2b310S@P0b0F8PC%:G#5#9#5#5#6RGPEPAPLPKPMPN%2GR@93OPP6PRb1b2b310<GP0b0PLPKPMPNPOP@PQPTC7P6PRb1b2b3A4GEFP0b0PUF8PC%:?#>#9#5#B#6R?%?>R>PAPLPKPMPN%2?RG93OPP6PRb1b2b310<?P0b0PLPKPMPNPOPG%2>RGPTC7P6PRb1b2b3A4?>FP0b0PLPKPMPNA3OJGP6PRb1b2b310S>P0b0F8PC%;:#>#:#9R:#9#9R>#<#6RGPEPAPLPKPMPN%2GR?93OPP6PRb1b2b310<GP0b0PLPKPMPNPOP?PQPTC7P6PRb1b2b3A4GEFP0b0PUF8PC%5>#6R>PEPAPLPKPMPN%2>RG93OPP6PRb1b2b310<>P0b0PLPKPMPNPOPGPQPTC7P6PRb1b2b3A4>EFP0b0PUF8PC%::#9#9#:#JR:P4PAPLPKPMPN%2:R>93OPP6PRb1b2b310<:P0b0PLPKPMPNPOP>P1PTC7P6PRb1b2b3A4:4FP0b0PIF8PC%:7#:#5#5R7#<#9#6RIPEPAPLPKPMPN%2IR:93OPP6PRb1b2b310<IP0b0PLPKPMPNPOP:PQPTC7P6PRb1b2b3A4IEFP0b0PUF8PC%5;#5#:#<#5#9#<#6RIPEPAPLPKPMPN%2IR:93OPP6PRb1b2b310<IP0b0PLPKPMPNPOP:PQPTC7P6PRb1b2b3A4IEFP0b0PUF8PC%:7#<#6R7PEPAPLPKPMPN%27RI93OPP6PRb1b2b310<7P0b0PLPKPMPNPOPIPQPTC7P6PRb1b2b3A47EFP0b0PUF8PC%1D#>#9RD#9#5#6R7%?;R;PAPLPKPMPN%27RI93OPP6PRb1b2b310<7P0b0PLPKPMPNPOPI%2;RIPTC7P6PRb1b2b3A47;FP0b0PLPKPMPNA3OJIP6PRb1b2b310S;P0b0F8PC%:DRD#9#6R;PEPAPLPKPMPN%2;RS93OPP6PRb1b2b310<;P0b0PLPKPMPNPOPSPQPTC7P6PRb1b2b3A4;EFP0b0PUF8PC%:D#6RDPEPAPLPKPMPN%2DRA93OPP6PRb1b2b310<DP0b0PLPKPMPNPOPAPQPTC7P6PRb1b2b3A4DEFP0b0PUF8MM]W9W8W7W>W=W;WBW<W:WAWDWCX53XE3X?3X63X@3WFo"). Qed.
End HCW.

Ltac rrenv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with AS_Refill1.RENV ?tp ?TSD ?CTX ?TH ?sb ?ARI m =>
      assert (E' : AS_Refill1.RENV tp TSD CTX TH sb ARI m');
      [ apply (rrenv_transport_img tp TSD CTX TH sb ARI m m' W E MU WM);
        [ out_img_tac ltac:(cbn [fst snd]; region_decide) | .. ]; cbn [disjoint_from]; region_decide | ]
    end end.
