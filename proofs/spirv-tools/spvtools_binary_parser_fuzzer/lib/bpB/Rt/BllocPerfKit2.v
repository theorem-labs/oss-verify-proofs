(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BllocWalkKit BW_LargeAlloc1 BS_Refill1 BllocTacX BllocPerfKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BllocPerfKit2 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I6ARocqVerifyHarness?AgentSubmission3bpB2Rt:BS_Refill14RENV00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC6ARocqVerifyHarness?AgentSubmission3bpB2Rt<BllocPerfKit7out_imgC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt<BllocPerfKit@out_img_disjointK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt:BS_Refill1>renv_transportK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3ivlC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma rrenv_transport_img : forall tp TSD CTX TH sb ARI m m' W,
    BS_Refill1.RENV tp TSD CTX TH sb ARI m -> munch W m m' -> wmono asegs m m' -> out_img W ->
    65536 <= bv_unsigned tp + -88 -> bv_unsigned tp + -88 + 8 <= 7241728 ->
    65536 <= TSD -> TSD + 8 <= 7241728 ->
    disjoint_from W (CTX + 152) 8 ->
    BS_Refill1.RENV tp TSD CTX TH sb ARI m'.
Proof.
ltac2:(KReplay.run1 (kr_t_BllocPerfKit2 ()) ["HCW"] "h07__arithh14__ffh28__varmaph35__with44__x1h53ARIh63CTXh72D1h82D2h92DCh:1Eh;2HWh<2MUh=2T1h>2T2h?2THh@3TSDhA1WhB2WMhC1mhD2m'hE2sbhF2tpp;1p;7p;3p;2p;4p;Mp;8g0000j10Tg000Uj1KTg0013j1JTg001Vj1gTg0028j1MTg002Xj7_Tg003Uj3^Tg004Rj3\Tg005Oj1YTg006Oj2ATg0079j12Tg007^j1bTg008<j2?Tg008Yj21Tg0095j1@Tg009Sj3]Tg00:Xj1[Tg00;8j1ZTg00;Vj1XTg00<4j1WTg00<_j2VTg00=Aj2UTg00=[j2TTg00>Gj3STg00>aj3RTg00?@j4QTg00@2j2ITg00@Uj79Tg00A^j2fTg00B<j2eTg00B_j1cTg00CAlMaTg00DFj4LTg00E1j7NTg00EUj3PTg00F8j8`Tf0R0#0#0p=G%00#0#0#0p==%00#0#0#@p=7%20#0#0#0p=>%00#2p=E%20#2p=6f2R1f1R2'?/10p=5%00#0#2#0p=C%00#0#0#2p=:%00#2#0#0p=<g00F\R3/I0p=3P1g00G:R4g00GYR5P5g00H9R6P3P2g00HYR7P0CLg00I@R8FNp=4f3R9P4P5P5P6P3AP312P7P0CLP8FNp=8AP320p=dP9P4P5P5P6P1P2P0G`p=F%20#0#0p=B%20#0p=;%00#@p=O%00#2#0#2p=D%20#2#0#0p=Hg00I`R4#0R8#0R7#0R:#0R;#GR<#KR=#JR>g00JE%K:#J#g\>g00K=#Mf8R>f7R?f6R@f5RAf4RBP9P1F_A^291g00L8?\B9%Y9%0<#G#=#7R<f<RC,A=%28#>#bR8'?'1f=RD,A=/?8%@:R:%24#E#6#E#=#=#=#7RE3511<Df>RF?5:E%67#7,?F=]>:fAR7f@RGf?PFPDPCf;f:f9RCP>P?P@PC%24#C#:#:#<#7R@P:PAg00LoR?#[R>%M?R?%Z3RD%X3RF%W3RH%3<RI%3@RJ341VH6R6P0P1g00M[RKg00N;RL'U1T01=SKLdg00N[RL=R32CQRKb1b2b311<@P0b0P>P?PDPFPHPJ%3:RJ%3ERMC8P6PKb1b2b3A5@:EP0b0P>P?PDPF1I3LR@=4HJP6PKb1b2b311L:P0b0RNF9PC1A=7/?8P:PAP>P?1f32ROPFPH1e34RP%38'dRQ94HIRR%c5R5PRCFP6PKb1b2b3X431?08RR,1<1?28R8,1<[^43P0fB,A=R=PAO2b0P>P?POPFPHPHPQPJPMC8RQP5PQCFP6PKb1b2b3X43A5R:EA58:E[^43P0P=PBO2b0PNF9PCPGP:PAP>P?POPFPHA4HIPRGP5PGCFP6PKb1b2b3X4311<011<2[^43P0P7P9O2b0P>P?POPFPHPHPPPJPMC8RPP5PPCFP6PKb1b2b3X43A50:EA52:E[^43P0P7P1O2b0PNF9P0PC%B4#>#<#<#6#;#OR1%@4R7PAP>P?PDPF%31R294HIP6PKb1b2b311<1P0b0P>P?PDPFPHP2%37R2PMC8P6PKb1b2b3A517EP0b0P>P?PDPFA4H@2P6PKb1b2b311L7P0b0R1F9PC%B4#C#;#:#=#7RP%24R5#6#7ROPAP>P?PDPF%3PR994HIP6PKb1b2b311<PP0b0P>P?PDPFPHP9%3OR9PMC8P6PKb1b2b3A5POEP0b0P>P?PDPFA4H@9P6PKb1b2b311LOP0b0F9PC%B4#>#>#:#6#7ROP:PAP>P?PDPF%3OR994HIP6PKb1b2b311<OP0b0P>P?PDPFPHP9PJPMC8P6PKb1b2b3A5O:EP0b0PNF9PC%B4#>#6#;#;#<#7RO%75R5PAP>P?PDPF%3OR994HIP6PKb1b2b311<OP0b0P>P?PDPFPHP9%35R9PMC8P6PKb1b2b3A5O5EP0b0P>P?PDPFA4H@9P6PKb1b2b311L5P0b0F9PC%:4#:#D#6#H#7R5P:PAP>P?PDPF%35R994HIP6PKb1b2b311<5P0b0P>P?PDPFPHP9PJPMC8P6PKb1b2b3A55:EP0b0PNF9PC%:4#:#D#6#6#6#7R5P:PAP>P?PDPF%35R994HIP6PKb1b2b311<5P0b0P>P?PDPFPHP9PJPMC8P6PKb1b2b3A55:EP0b0PNF9PC%G4#<#D#>#6#E#;#OR5P7PAP>P?PDPF%35R994HIP6PKb1b2b311<5P0b0P>P?PDPFPHP9P2PMC8P6PKb1b2b3A557EP0b0P1F9PC%24#=#6#;#C#;#E#7R1P:PAP>P?PDPF%31R594HIP6PKb1b2b311<1P0b0P>P?PDPFPHP5PJPMC8P6PKb1b2b3A51:EP0b0PNF9PC%G4#<#:#D#H#7R1P:PAP>P?PDPF%31R594HIP6PKb1b2b311<1P0b0P>P?PDPFPHP5PJPMC8P6PKb1b2b3A51:EP0b0PNF9PC%24#=#6#>#6#=#7R1P:PAP>P?PDPF%31R594HIP6PKb1b2b311<1P0b0P>P?PDPFPHP5PJPMC8P6PKb1b2b3A51:EP0b0PNF9PC%24#:#;#H#6#6#6#7R1%@;R;PAP>P?PDPF%31R594HIP6PKb1b2b311<1P0b0P>P?PDPFPHP5%3;R5PMC8P6PKb1b2b3A51;EP0b0P>P?PDPFA4H@5P6PKb1b2b311L;P0b0F9PC%24#:#;#6#<#:#7R;P:PAP>P?PDPF%3;RL94HIP6PKb1b2b311<;P0b0P>P?PDPFPHPLPJPMC8P6PKb1b2b3A5;:EP0b0PNF9PC%24#:#;#6#<#C#7R4P:PAP>P?PDPF%34RA94HIP6PKb1b2b311<4P0b0P>P?PDPFPHPAPJPMC8P6PKb1b2b3A54:EP0b0PNF9MMaW9W8W7W>W=W;WBW<W:WAWDWCX53XE3X?3X63X@3WFo"). Qed.
End HCW.

Ltac rrenv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with BS_Refill1.RENV ?tp ?TSD ?CTX ?TH ?sb ?ARI m =>
      assert (E' : BS_Refill1.RENV tp TSD CTX TH sb ARI m');
      [ apply (rrenv_transport_img tp TSD CTX TH sb ARI m m' W E MU WM);
        [ out_img_tac ltac:(cbn [fst snd]; region_decide) | .. ]; cbn [disjoint_from]; region_decide | ]
    end end.
