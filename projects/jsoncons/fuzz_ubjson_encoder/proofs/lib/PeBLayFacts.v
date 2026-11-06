(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceAB EbrInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeBLayFacts () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4prod01K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB0?as0_icpt_layout01C13~~~K47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;PeBLayFacts5PEBLF6art_ILC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv7PRIMCAPC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;PeBLayFacts5PEBLF7BUDGET0C13~~~C56Stdlib6ZArith6BinInt1Z3sub".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEBLF.
Definition art_IL : icpt_layout :=
  ICL 0x64518
      2304
      0x103c0
      0x103e0
      [(0x232e0, 13); (0x233e0, 16); (0x23400, 23); (0x23440, 13); (0x23460, 60); (0x234c0, 77); (0x23540, 73); (0x235c0, 13); (0x235e0, 38); (0x23640, 70); (0x236c0, 69); (0x23740, 37); (0x237a0, 43); (0x23800, 34); (0x23860, 71); (0x238e0, 28); (0x23920, 7); (0x23980, 1); (0x239a0, 3); (0x239c0, 10); (0x239e0, 13); (0x23a00, 14); (0x23a20, 45); (0x23be0, 54); (0x23c40, 52)]
      [(0x232e0, 0x23ca0); (0x1423d0, 0x142a10)]
      0x78e3c
      0x78e38
      0x69b638
      0x64590
      4320
      [(0x67a150, 8, 0x69a448); (0x69a470, 8, 0)]
      0x10000
      0x13f000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof.
ltac2:(KReplay.run1 (kr_t_PeBLayFacts ()) [] "p;1p;2p;4p;?p;3g0000j11Tg000Uj10Tg001:j2DTg001Zj1CTg002:j12Tg002Xj1GTg0038j2?Tg003Rj47Tg0042l?KTg005Kj38Tf0R0#0#1p=3%00#0p=;%10#0p=5g005kR1%00#0#2'?p=6%00#0#0#0p=9%10#1p=4%10#0#0#0p=@%10#1#0#0p=>%00#0#0#2p=:%10#0#0p=J%00#2p=I%00#0#0p=Hf6R2P1P1f5R3#0#0#0#0#0#2f4R4C7f3R5P1P1f2R6#0#0#0#0#0#2f1R7C7;8038p==P1P1%06#0#0#0#0#2%27C7=850p=BP1P1%03#0#0#0#0#2%24C7P1P1%06#0#0#0#0#2%27C7=850582p=<P1P1P3P4C7P1P1P6P7C7=850582p=F%00#1#0#0p=AP1P1%27P0C7p=EA86709845p=Lg006Ig007\R5#1R4#0R7#3R6#;#3#3R0#;#3#5#6%05R2#0R3#1R8#0R9#0R:#9#6%03R3#0R;#;R<#4#4R=#9#6%@=#61D11R=#CR>P=%13R?#1R@#0RA#3RB#3#>#:RC%17R7#2RDP=%4B#>#:%2;P=%1ARB#0RE#0RF#0RG#;%12R2#1RH#1P=%1GRG#0PDP=%1G%14RG#JRI#2P=%1F#5%18R8#0RF#1P=%1ERE#0#5%1:P=%4ERE#0PDP=%1E%2FP=%1BRB#0RF#0#5PAP=%1F#5%0?R?#1P=%1BRB#0#5%19P=%1B#3%02R2#4P=%1@R@#0RB#0R9#0RF#0RA#;P?P=%4AP@P=%1F#4%0GRF#IP=%19R9#0#3%2GP=%19R9#0RG#0P5P=%1GP4P=%19R9#0P2P=%19PDP=%1BRB#HRD#0%2FP=%1D%3HP=%4B#4%17#IP=%J@R@#0#5%;7R7#2%G=RBF=CBF=CBF<F=F<F<F<F=F<F=CBFF'?P=PC%1@#A#:P=%H2#5R2#0#3#4#5#5#:%12#3#9#5#:PBFF,?>%3I#>#3#4RI#1#6%0I#6%47#3R7#1#3#@#4#5#6%50#A#6%4;#@#61D=1R;#CP;P=P1%46#5#@#3#3#3#9%23R3'E%07#A#3R7#0#3#:C7P;P=P1%47#9/E3g008AC7%G;DL'?%9<#9#6%48#>#9#9#6M?Ko"). Qed.

(* [comment removed for export] *)
Definition BUDGET0 : Z := 2 ^ 38.
Lemma BUDGET0_lo : 2 ^ 36 + 2 ^ 20 + EbrInv.PRIMCAP <= BUDGET0.
Proof.
ltac2:(KReplay.run1 (kr_t_PeBLayFacts ()) [] "p'0h01Hh11eh21xi001cp;3p;6p;2p;1g008_j38Tg0099j67Tg009Uj25Tg000Uj10Tg002:j11Tg0000j14Tg00:4j22Tg00:Qj23Tg00:nj26Tg00;JR0g00<0R1g00<VR238P0P1P0p-0f0R1g00=<R3g00=YP3n011000003000000X10g00>5P2P1E7P31531b0W2g007\#0R3#1R1%03#4#0#0#1'2%43#0#0#1,21'3g00>Q'3g00?Z'6do"). Qed.
Lemma BUDGET0_lo37 : 2 ^ 37 + 2 ^ 20 + EbrInv.PRIMCAP <= BUDGET0.
Proof.
ltac2:(KReplay.run1 (kr_t_PeBLayFacts ()) [] "p'0h01Hh11eh21xi001cp;3p;6p;2p;1g008_j38Tg0099j67Tg009Uj25Tg000Uj10Tg002:j12Tg0000j11Tg00:4j24Tg00:Qj23Tg00:nj26Tg00;JR0g00<0R1g00<VR238P0P1P0p-0f0R1g00=<R3g00=YP3n011000003000000X10g00>5P2P1E7P31531b0W2g007\#0R3#2R1%03#1#0#1#2'4%13#0#0#2,41'3g00>Q'3g00?Z'6do"). Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35.
Proof.
ltac2:(KReplay.run1 (kr_t_PeBLayFacts ()) [] "p'0h01Hh11eh21xi001cp;3p;6p;2p;1g008_j38Tg0099j67Tg009Uj24Tg000Uj11Tg002:j12Tg0000j10Tg00:4j23Tg00@nj25Tg00:nj26Tg00;JR0g00<0R1g00<VR238P0P1P0p-0f0R1g00=<R3g00=YP3n011000003000000X10g00>5P2P1E7P31431b0W2g00?Zg007\#1R3#2R1%13R3#0#0#0#2'3%13#0#0#2,31'5'6do"). Qed.
End PEBLF.
