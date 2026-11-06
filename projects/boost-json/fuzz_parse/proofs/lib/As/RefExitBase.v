(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SegRead.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Export SumWalkTac RefNodes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefExitBase () := KReplay.lz_vm "##EsK47Corelib7Numbers7BinNums8positive02!sK=1N!sD?!si,1!si>Z!si#5stdpp9bitvector;definitions2bv!sg/4Init5Logic2eq01C!sc@;bv_unsignedC89OSSVerify6Proofs:boost_json:fuzz_parse3!tv#SegRead7SEGREAD>range_writableC13~~~I!td;0C!s@76eq_ind!sB89False!sE$56Stdlib6ZArith6BinInt1Z6of_nat!sF<3ad!sc=3pow!sC<2le!v;`=wseg_ok_!vC$!v:%!wx29Datatypes3nat02C7!t>,!t796images4Asan1M?loaded_segments!t33!z;=3!yR84True!yn4!tt21I!sE;4bool00K!sFA!sf=:comparison!sl>!sL/2!sLH3!zQ85!ys$00I!v$=!tS37Decimal4uint04!sD@;!sD@3!sD@:!sD26!x6%!sC%1!|923Nat;!{l#um_!sG#!t$@1!sD@2!sD@7!sD@6I!#4_C0!xh<6op!sL#!wS:2or00C4ELinuxProcessSemantics?!s<2>Riscv!sE+8store_ok!~F<>pow_pos_nonneg!~n>!#3l<:!sj#!sf%!{d=lis!|L@!sF$0K4!t2&9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr!yA#!sIC7C!sI55Tauto8B!t8&!sH6:Z!t^+=Z!sT$CheckerC!uS<4f!#8q#!sq?C!sq0_sound!#6N-!#7fE!y@#Ok?!yH'_window!#:t=3and!vi8!w<:!vq7!vN&G!sJ'4!t8,!#>U5!t;E3Op203!w_<5eKind!zC=uni!zC9!se%4kind!#8p=!sf%!{K=!#98#!#6U,!uY6!{J7!xV-;!}1%!x<$00c!#=8N2As;RefExitBase>ref_!#=;#file!#<'%!sw_<!sw+crt!sue=!su+tail!sv%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos37Corelib4Init9Datatypeshf4boolhf4true37Corelib4Init5Logick51Ik52eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~m27wseg_ok69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~q8floaded_segments35stdpp9bitvectorbdefinitionsuf2BVuf4BvWfuf2bv37Corelib4Init7Decimalhhd2D1hhd2D2hhd2D8hhd2D9hhd3Nil37Corelib4Init3Nathl2bof_num_uint37Corelib4Init6Numberhn3bUIntDecimalhhd2D446Stdlib6ZArith6BinInt1Zhpd2leufbbv_unsignedk53andhpd3addhpd6of_natk52orhf3nathf6option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshv48store_ok01Zhf4listuf7Z_to_bvhf4Somehv4h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~im73rdnhf4conshf3nilhhd2D0hhd2D5" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma ref_wseg_files : ltac2:(zQ "a0!h9!j7!je!l9!ld!pe!td!hgc!hh1!hh8@3$4$1@3$5$6Kd@3$7@1$0#k0+hrpvg8Kv$3@2$8@1$0#k0+hrpvg8@1$9@1$0#k0Nhu0$2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##+sp'0h01Hh11eh21xi001cp;1p;3p;2p;6p;5g0000j13Tg000Uj1<Tg0013j12!s/$Xj15Tg0026j3?!s/$Yj2;Tg0033j2:!s/$]j38Tg004oj36Tg005Ij67!s/$ej29Tg006Dj1B!s/$dj2ATg007Aj2@!s/$^j2>Tg008:j5=Tg009Kj10Tf0R0#3#3p=4%00#!s$`p=1g009jR1g00;0R2#3R3#3#4#4R4#<R5%22#3#2!s$$4!s-&!s2%4#2!sO$5g00;UR23?R6g00<1#!s$@R7g00<PR8g00=0R9';1:56R6=817=689dg00=PR9g00>6!sL$>\R136P9P8P9p-0P0g00?B!sA$?_P8n011000003!s+$0X19P2P1P0E7P81980b0W2%B7,A6%53%54'@'>dD=o"). Qed.   (* [comment removed for export] *)
Lemma ref_wseg_crt : ltac2:(zQ "h10!h9!j7!je!hj3!hj9!hjf!hk5!hkb!l9!ld!hm4!ho8!pe!td!hgc!hh1!hh8@3$9$1@3$c$dKd@3$e@1$0#k0+hrsgg0Kv$8@2$f@1$0#k0+hrsgg0@1$h0@1$0#k0@1$a@1$b@1$5@1$3@1$6@1$4$7$2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##+Dp'0h01Hh11eh21xi001cp;1p;3p;2p;6p;5g0000j12Tg000Uj1;Tg0013j11!s/$Xj13Tg0026j3DTg00@;j1<!s/$Yj1:Tg00A7j17!s/$Uj16Tg00B3j15!s/$Pj18!se$Yj29Tg0033j2F!s/$]j3ETg004oj34Tg005Ij6C!s/$ej2=Tg006Dj1>!s/$dj2?Tg007Aj2@!s/$^j2ATg008:j5BTf0R0#2#2p=0g009jR1g00;0R2#2R3#2#0#0R4#;R5%12#2#1!s$&0!s$03g00;UR23DR6g00Bo#<#:#7#6#5#8R7g00<PR8g00=0R9'91F56R6=E17=489dg00=PR9g00>6!sL$>\R134P9P8P9p-0P0g00?B!sA$?_P8n011000003!s+$0X19P2P1P0ECP81=80b0W2%>7,?6%33%34'@'AdDBo"). Qed.   (* [comment removed for export] *)
Lemma ref_wseg_tail : ltac2:(zQ "h30!hp7!h9!hj3!j7!je!hkb!l9!ld!hm4!ho8!pe!td!hgc!hh1!hh8!ir6!hjf!hj9!irc@3$7$3@3$a$bKd@3$c@1$1#k0+mvioo0Kv$6@2$d@1$1#k0+mvioo0@1$e@1$1#k0@1$8@1$9@1$2@1$0@1$h2@1$h1@1$h0@1$f$5$4").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##+bp'0h01Hh11eh21xi001cp;1p;3p;2p;6p;5g0000j11Tg000Uj1;Tg0013j10!s/$Xj13Tg0026j3>Tg00CMj1<Tg00AUj1:Tg00@;j17!sA$kj16Tg00DIj15!sJ$7j18Tg00B3j19!s/$Pj1H!sw$Yj2GTg0033j2F!s/$]j3=Tg004oj34Tg005Ij6?!s/$ej2@Tg006Dj1A!s/$dj2BTg007Aj2C!s/$^j2DTg008:j5ETf0R0#1#1p=2g009jR1g00;0R2#1R3#1#2#2R4#;R5%02#1#0!s$&2#0!s4$1!s0&2!s$$3g00;UR23>R6g00Bo#<#:#7#6#5#8#9#HR7g00<PR8g00=0R9'G1F56R6==17=489dg00=PR9g00>6!sL$>\R134P9P8P9p-0P0g00?B!sA$?_P8n011000003!s+$0X19P2P1P0E?P81@80b0W2%A7,B6%33%34'C'DdDEo"). Qed.   (* [comment removed for export] *)

Lemma store_ok_data : ltac2:(zQ "f0!h9!hr5!hrb!hs9!hsf!ht6!hh8!hu0!j7!hu5!hub!je!ld!iib!td>1m>0@1$6@1$0#k0@1$a@1$6@1$0#8>1a@1$6@1$0#k0>1n$9>0@2$7@2$3@2$1+hrpvg8@2$2@1$0#k0^2@2$1@2$4@2$2@1$0#k0^2@1$5^1+hrqgu8@2$7@2$3@2$1+hrsgg0@2$2@1$0#k0^2@2$1@2$4@2$2@1$0#k0^2@1$5^1+hrugg0@2$3@2$1+mvioo0@2$2@1$0#k0^2@2$1@2$4@2$2@1$0#k0^2@1$5^1+nhmgg0@3$c$8@4$d$e^4^3^2$b").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##;{h01Hh13Hhih23Hloh37__arithh44__ffh56__sat0h6!s/%1h78__varmaph85__with92Hah:1ah;1mh<1np;1p;2p;4p;3p;>p;7g0000j15Tg000Uj1ITg00Dgj1HTg00EJj1gTg0013j1;!s/$Xj1:Tg0033j27!sJ$lR0j2=Tg00FFj4ETg007^j21Tg0026j3DTg00GFj2\!s/$nj2K!sJ$Aj2[Tg00HJj3Z!s/$nj1YTg00INj1X!s/$nj1WTg00JLj1V!s/$jj1UTg00KUj2ATg00L8j3S!s/$[j2R!tC$Yj2GTg00M=j2Q!s/$ij3PTg00NHj4TTg00O:l>CTg00@;j1O!s/$Yj1fTg00A7j1N!s/$Uj1LTg00B3j1J!s/$Pj1MTg00CMj1e!s/$kj1d!vR$Ij1cTg006Dj1a!s/$dj2`Tg00PER1j2_Tg004oj3^Tg009Kj10!sC$`j4bTg00QKj7]Tf0R2#5#5p=8%52#;p=?%;!s-$>%5!s@$#5p=4%;2#5p=6f1R3%a2'`p=9f3R4f2R5'11132'_p=3g00<PR6g00=0R77^2p=@%02#0!s$_p=2g00QoR8/G2p=<P8P3g00RMP2Cbp=B!s4$S4g00SSR9P9g00T3R9P2g00TSF]p=Fg00;0R:#5R;#8R<#5#8R=#IR>#HR?%I<#H#g[g00U3%;:R:#?#>R<#5R@#?#>#>#4#6#8#:RA17>3RB19B2RC%6@#4#>#6!sC&@C3%;<R<#8RD#4!s$$:REPBPC%6<!s7+<C3%6D!sY$6#8!s9$D!sJ$;:#8#?#?#6!sR+:C3'='=P0PA17>5RC19C3RBP@C3PEPCPBP<C3PD!s0$!sR$g009jRBf4RCP4P5CE#@P2!sc$4RF19F5RG!sc$117>CRH,1A19H4R4/1@PBf6RIf5RJPCCE#@RKP217>IRL,1Af7RM,7>/9I!sP%9RNg00;URO9D>Af8RPg00<1#2!s$?PMPAP@%<A%<@%:;R;%:=R='\RAg00URRQ/K;11Q=1[;=RR,KQ[[RS11Q;!|s$?_RUAZ;=3UW9R=11QR\U^9T!sB$V0RU#YRV%XURU%W8RW%V8RX%U8RY1A8@1A8;=S8>R;'B'F1RY9R9P2P51G671Q25#@dAP8Q3CTRQb4b7b811@RP2b3b5b6g00V\P3P2M>CW1W2P3P2O2n20010!s#$12!s/&W0P2O1PEPFPG!wa&FPG!wa%P0PEPHP4!s>&HP4P:C3PKP2PE17>JRK19KCRC!sF$111EL19LJRJ/1<PBPPPMPI!w]$I!w]$PRM,1E17>N/9PRP!sK$f;R4AD>EOf:RHg00BoR0#O#f#N#L#J#MPNPEP<%<E%<<PAPSP=PTPVPUPWPX1A8</B;,FYP9P!uz+<!uz/Wm!uzODPKPC!uX$111DL11J:PIP211DM11P:PBP4AD>DOPH%e0#L#O#d#c#N!tv&DP:%<D%<:!tv6:!tv5:!tv/Y<!tvN!s@-211000!s'$!sBAW<X:?W;o"). Qed.
End FPX1.

(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition file_clean : ltac2:(zQ "40!h9!hh8!hub!ij7>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1f$3>2wp@1$1@1$0#k0>2rp@1$1@1$0#k0P") := ltac2:(zQ "d2!h9!hh8!ija!hub!ik1!ikb!ld!il2!iq2!td!hsf!hs9!ij7&@2$5@1$2@1$1@1$0#8@2$7N8^2&@2$5@1$2@1$1@1$0#8@2$7N8^1\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\1f$c\2wp@1$1@1$0#k0\2rp@1$1@1$0#k0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+ocN4@2$5@1$2@1$1@1$0#8@2$7N4@2$4@1$0#k0+vvvvvvvf@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+i8N8~0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+j8N8~0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+8N8~1@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+h0N8~1").

(* [comment removed for export] *)
Definition stdio_globals : ltac2:(zQ "30!h9!hh8!hub>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "d0!h9!hh8!ija!ik1!hub!ikb!ld!iq2!td!hs9!il2!iq9!ir0\3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+nhkmmbN1@2$5@1$2@1$1@1$0#8@3$b@1$1@1$0#8@2$3@1$0#8Z@1$c@1$1@1$0#8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+nhkru0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0Z@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hrqht0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+hrqgu8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hrqgu0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+hrpvv8@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hrpvv0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+hrpvg8"). End FPX2.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
