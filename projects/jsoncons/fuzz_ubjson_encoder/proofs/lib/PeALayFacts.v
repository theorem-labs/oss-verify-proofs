(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceAB EarInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeALayFacts () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4prod01K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:IcptIfaceA?as0_icpt_layout01C13~~~K47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;PeALayFacts5PEALF6art_ILC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv7PRIMCAPC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;PeALayFacts5PEALF7BUDGET0C13~~~C56Stdlib6ZArith6BinInt1Z3sub".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEALF.
Definition art_IL : icpt_layout :=
  ICL 0x63cf0
      2304
      0x103b8
      0x103d8
      [(0x231e0, 13); (0x232e0, 16); (0x23300, 23); (0x23340, 13); (0x23360, 60); (0x233c0, 77); (0x23440, 73); (0x234c0, 13); (0x234e0, 38); (0x23540, 70); (0x235c0, 69); (0x23640, 37); (0x236a0, 43); (0x23700, 34); (0x23760, 71); (0x237e0, 28); (0x23820, 7); (0x23880, 1); (0x238a0, 3); (0x238c0, 10); (0x238e0, 13); (0x23900, 14); (0x23920, 45); (0x23ae0, 54); (0x23b40, 52); (0x133920, 104)]
      [(0x231e0, 0x23ba0); (0x133920, 0x1339c0); (0x13dcc0, 0x13e340)]
      0x78614
      0x78610
      0x696f38
      0x63d68
      4320
      [(0x675a50, 8, 0x695d48); (0x695d70, 8, 0)]
      0x10000
      0x13a000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof.
ltac2:(KReplay.run1 (kr_t_PeALayFacts ()) [] "p;1p;2p;4p;?p;3g0000j11Tg000Uj10Tg001:j2ETg001Zj1DTg002:j13Tg002Xj1HTg0038j2?Tg003Rj46Tg0042l?ITg005Ij37Tf0R0#0#1p=2%10#1p=5%10#0p=4%10#1#0#0p=@g005iR1%00#0#3'?p=8%00#0#0#0p=9%00#0p=;%00#0#0#3p=:%10#0#0p=C%00#3p=Bf3R2P1P1f2R3f1R4C6;70p=Lf6R5P1P1f5R6#0#0#0#0#0#3f4R7C6P1P1%03#0#0#0#0#3P4C6=72037p=<P1P1%03#0#0#0#0#3%34C6=720p=AP1P1%06#0#0#0#0#3%37C6P1P1%03#0#0#0#0#3%34C6=720575p==P1P1P6P7C6P1P1P3P4C6=720575p=G%10#0#0#0p=>P1P1%03#0#0#0#0#3P4C6=720p=KP1P1%34P0C6p=FA73409772p=Jg006Gg007ZR7#1R2#0R4#0R3#2#5#4R0#0#5#@#8%07R5#0R6#1R8#0R9#0R:#9#8%06R6#0R;#;R<#1#5R=#0#5#4#8%1=#2#4#81E11R=#DR>P=%16R?#1R@#0RA#0RB#0#5#@#:RC%14R4#3RDP=%1BRB#2#@#:%3;P=%1BRB#0RE#;%15R5#1RF#1P=%1ERE#0PDP=%1E%12RE#CRG#3P=%1B#4%18R8#0RB#1P=%1ARH#0RI#0RJ#0#4%1:P=%5JRJ#0PDP=%1J%3BP=%1IRI#0#4PAP=%1I#4%0?R?#1P=%1HRH#0RI#0#4%19P=%1I#2%05R5#5P=%1HRH#0RI#;P?P=%5I%1@R@P=%1H#5%0ERH#BP=%0@R@#0RI#0R?#0#2%3EP=%1?R?#0RE#0P7P=%1EP2P=%1?R?#0P5P=%1?PDP=%CIRI#0%3HP=%1I%2FP=%1@R@#2#5%14#BP=%1@R@#0#4%;4R4#3P=%0B#5#4#2RB#0#2#;#:RF%B4%H=RICLF<CAF<CAF=F<F=F=F=F<F=F<CAFG'?P=PC%1@#2#;#:P=PF%1B#>#:P=%18R8#1RB#0#5#4#2#4%CB#2#4#>#:PICKFG,?>%;G#5#9#4RG#1#8%0G#8%14#2R4#4#5#@#5#4#8%10#2#4#4#8%5;#>#81E=1R;#DP;P=P1%13#5#2#2#4#4#2#2#9%36R6'F%24#5#2#2R4#0#2#:C6P;P=P1%54#9/F6g008?C6%H;DJ'?%9<#9#8%08#>#9#9#8M?Io"). Qed.

(* [comment removed for export] *)
Definition BUDGET0 : Z := 2 ^ 38.
Lemma BUDGET0_lo : 2 ^ 36 + 2 ^ 20 + EarInv.PRIMCAP <= BUDGET0.
Proof.
ltac2:(KReplay.run1 (kr_t_PeALayFacts ()) [] "p'0h01Hh11eh21xi001cp;3p;6p;2p;1g008]j38Tg0097j67Tg009Sj25Tg000Uj10Tg002:j11Tg0000j14Tg00:2j22Tg00:Oj23Tg00:lj26Tg00;HR0g00;nR1g00<TR238P0P1P0p-0f0R1g00=:R3g00=WP3n011000003000000X10g00>3P2P1E7P31531b0W2g007Z#0R3#1R1%03#4#0#0#1'2%43#0#0#1,21'3g00>O'3g00?X'6do"). Qed.
Lemma BUDGET0_lo37 : 2 ^ 37 + 2 ^ 20 + EarInv.PRIMCAP <= BUDGET0.
Proof.
ltac2:(KReplay.run1 (kr_t_PeALayFacts ()) [] "p'0h01Hh11eh21xi001cp;3p;6p;2p;1g008]j38Tg0097j67Tg009Sj25Tg000Uj10Tg002:j12Tg0000j11Tg00:2j24Tg00:Oj23Tg00:lj26Tg00;HR0g00;nR1g00<TR238P0P1P0p-0f0R1g00=:R3g00=WP3n011000003000000X10g00>3P2P1E7P31531b0W2g007Z#0R3#2R1%03#1#0#1#2'4%13#0#0#2,41'3g00>O'3g00?X'6do"). Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35.
Proof.
ltac2:(KReplay.run1 (kr_t_PeALayFacts ()) [] "p'0h01Hh11eh21xi001cp;3p;6p;2p;1g008]j38Tg0097j67Tg009Sj24Tg000Uj11Tg002:j12Tg0000j10Tg00:2j23Tg00@lj25Tg00:lj26Tg00;HR0g00;nR1g00<TR238P0P1P0p-0f0R1g00=:R3g00=WP3n011000003000000X10g00>3P2P1E7P31431b0W2g00?Xg007Z#1R3#2R1%13R3#0#0#0#2'3%13#0#0#2,31'5'6do"). Qed.
End PEALF.
