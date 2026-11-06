(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SegRead.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Export SumWalkTac RefNodes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefExitBase () := KReplay.lz_vm "##EZK47Corelib7Numbers7BinNums8positive02!sK=1N!sD?!si,1!si>Z!si#5stdpp9bitvector;definitions2bv!sg/4Init5Logic2eq01C!sc@;bv_unsignedC89OSSVerify6Proofs:boost_json:fuzz_parse3!tv#SegRead7SEGREAD>range_writableC13~~~I!td;0C!s@76eq_ind!sB89False!sE$56Stdlib6ZArith6BinInt1Z6of_nat!sF<3ad!sc=3pow!sC<2le!v;`=wseg_ok_!vC$!v:%!wx29Datatypes3nat02C7!t>,!t796images9AsanUbsan1M?loaded_segments!t83!z@=3!yW84True!ys4!ty21I!sE;4bool00K!sFA!sf=:comparison!sl>!sL/2!sLH3!zV85!yx$00I!v$=!tS37Decimal4uint0:!sD@6!sD26!wR%!sC%1!{Z23Nat;!{5#um_!sG#!t$@1!sD@4!sD@9!sD@7!sD@3I!#4FC0!xJ<6op!sL#!w5:2or00C4ELinuxProcessSemantics?!s<2>Riscv!sE+8store_ok!~,<>pow_pos_nonneg!~U>!#3S<:!sj#!sf%!{F=lis!|-@!sF$0K4!t2&9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr!y_#!sIC7C!sI55Tauto8B!t8&!sH6:Z!t^+=Z!sT$CheckerC!uS<4f!#8X#!sq?C!sq0_sound!#65-!#7ME!y@#Ok?!yH'_window!#:[=3and!vi8!w<:!vq7!vN&G!sJ'4!t8,!#><5!t;E3Op203!w_<5eKind!zC=uni!zC9!se%4kind!#8R=!sf%!{K=!#8r#0K!uY?!{J7!xV-;!}1%!x<$00c!#<wN2Bs;RefExitBase>ref_!#<z#file!#;e%!sw_<!sw+crt!sue=!su+tail!sv%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos37Corelib4Init9Datatypeshf4boolhf4true37Corelib4Init5Logick51Ik52eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~m27wseg_ok69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~q8floaded_segments35stdpp9bitvectorbdefinitionsv42BVv44BvWfv42bv37Corelib4Init7Decimalhi22D1hi22D4hi22D6hi22D8hi23Nil37Corelib4Init3Nathl7bof_num_uint37Corelib4Init6Numberhn8bUIntDecimalhi22D046Stdlib6ZArith6BinInt1Zhq22lev4bbv_unsignedk53andhq23addhq26of_natk52orhf3nathf6option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshv98store_ok01Zhf4listv47Z_to_bvhf4Somehv9h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~imc3rdnhf4conshf3nilhi22D2hi22D5hi22D7" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma ref_wseg_files : ltac2:(zQ "a0!h9!j7!je!l9!ld!pe!u2!hh1!hh6!hhd@3$4$1@3$5$6Kd@3$7@1$0#k0+hrmti0Kv$3@2$8@1$0#k0+hrmti0@1$9@1$0#k0Nhu0$2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##+up'0h01Hh11eh21xi001cp;1p;3p;2p;6p;5g0000j13Tg000Uj1<Tg0013j12!s/$Xj15Tg0026j3?!s/$Yj2;Tg0033j2:!s/$]j38Tg004oj36Tg005Ij67!s/$ej29Tg006Dj1B!s/$dj2ATg007Aj2@!s/$^j2>Tg008:j5=Tg009Kj10Tf0R0#3#3p=4%00#!s$`p=1g009jR1g00;5R2#3R3#3#4#4R4#<R5%22#3#2#!s+54!s-$4#4#5g00;ZR23?R6g00<6#1!s$?R7g00<UR8g00=5R9';1:56R6=817=689dg00=UR9g00>;!sL$>aR136P9P8P9p-0P0g00?G!sA$?dP8n011000003!s+$0X19P2P1P0E7P81980b0W2%B7,A6%53%54'@'>dD=o"). Qed.   (* [comment removed for export] *)
Lemma ref_wseg_crt : ltac2:(zQ "h10!h9!j7!je!hj8!hje!hk4!hka!hl0!l9!ld!hm9!hod!pe!u2!hh1!hh6!hhd@3$9$1@3$c$dKd@3$e@1$0#k0+hroug0Kv$8@2$f@1$0#k0+hroug0@1$h0@1$0#k0@1$a@1$b@1$6@1$4@1$4@1$6$7$2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##+6p'0h01Hh11eh21xi001cp;1p;3p;2p;6p;5g0000j11Tg000Uj1<Tg0013j10!s/$Xj13Tg0026j3BTg00@@j15!s/$^j14Tg00A<j1;!s/$Yj1:!sS$Yj27Tg0033j28!s/$]j39Tg004oj36Tg005Ij6D!s/$ej2CTg006Dj1A!s/$dj2?Tg007Aj2>!s/$^j2=Tg008:j5@Tf0R0#1#1p=2g009jR1g00;5R2#1R3#1#2#2R4#<R5%02#1#0!s$$1#2!s0-!s$%3g00;ZR23BR6g00B8#5#4#4#5#;#:R7g00<UR8g00=5R9'71856R6=917=689dg00=UR9g00>;!sL$>aR136P9P8P9p-0P0g00?G!sA$?dP8n011000003!s+$0X19P2P1P0EDP81C80b0W2%A7,?6%33%34'>'=dD@o"). Qed.   (* [comment removed for export] *)
Lemma ref_wseg_tail : ltac2:(zQ "h30!h9!hpc!hje!j7!je!hj8!hl0!l9!ld!hm9!hod!pe!u2!hh1!hh6!hhd!irb!is7!is1@3$8$3@3$b$cKd@3$d@1$0#k0+muvns0Kv$7@2$e@1$0#k0+muvns0@1$f@1$0#k0@1$9@1$a@1$5@1$2@1$h2@1$2@1$h1@1$h0$6$4").
Proof.
ltac2:(KReplay.run1 (kr_t_RefExitBase ()) ["FPX1"] "p'0h01Hh11eh21xi001cp;1p;3p;2p;6p;5g0000j10Tg000Uj1<Tg0013j11Tg001Xj14Tg0026j3=Tg00BVj1;Tg00C4j1:Tg00@^j15Tg00CRj17Tg00D0j18Tg00A<j19Tg00AYj1HTg002Yj2GTg0033j2FTg003]j3>Tg004oj36Tg005Ij6?Tg005ej2@Tg006Dj1ATg006dj2BTg007Aj2CTg007^j2DTg008:j5ETf0R0#0#0p=2%10#1p=3g009jR1g00;5R2#0R3#0#2#2R4#<R5%12#0#1#3#0#3#3#0#1#3#3#2#2#2#4g00;ZR23=R6g00B8#;#:#5#7#5#8#9#HR7g00<UR8g00=5R9'G1F56R6=>17=689dg00=UR9g00>;R8g00>aR136P9P8P9p-0P0g00?GR8g00?dP8n011000003000000X19P2P1P0E?P81@80b0W2%A7,B6%43%44'C'DdDEo"). Qed.   (* [comment removed for export] *)

Lemma store_ok_data : ltac2:(zQ "f0!h9!hra!hs0!hse!ht4!htb!hhd!hu5!j7!hua!hv0!je!ld!ij0!u2>1m>0@1$6@1$0#k0@1$a@1$6@1$0#8>1a@1$6@1$0#k0>1n$9>0@2$7@2$3@2$1+hrmti0@2$2@1$0#k0^2@2$1@2$4@2$2@1$0#k0^2@1$5^1+hrmvg0@2$7@2$3@2$1+hroug0@2$2@1$0#k0^2@2$1@2$4@2$2@1$0#k0^2@1$5^1+hrqvg0@2$3@2$1+muvns0@2$2@1$0#k0^2@2$1@2$4@2$2@1$0#k0^2@1$5^1+nhjgg0@3$c$8@4$d$e^4^3^2$b").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##;th01Hh13Hhih23Hloh37__arithh44__ffh56__sat0h6!s/%1h78__varmaph85__with92Hah:1ah;1mh<1np;1p;2p;4p;3p;>p;7g0000j14Tg000Uj1JTg00DNj1HTg00E1j1fTg0013j19!s/$Xj18Tg0033j27!sJ$SR0j2@!s1$mj4GTg007^j21Tg0026j3FTg00Fmj2[Tg00GUj2K!sJ$Aj2ZTg00H1j3Y!s/$Uj1XTg00I5j1W!s/$Uj1VTg00J3j1U!s/$Qj1TTg00K<j2A!s/$_j3QTg00LBj2P!tC$Yj2I!s8$dj2RTg00MPj3O!s/$oj4STg00Nal>ETg00@@j1N!s/$^j1BTg00A<j1M!s/$Yj1LTg00BVj1eTg00C4j1d!s/$Rj1c!vI$0j1bTg006Dj1`!s/$dj2^Tg00OlR1j2]Tg004oj3_Tg009Kj10Tg00PGj4\Tg00Q2j7aTf0R2#4#4p=;%92#9p=6%4!s-$?%92#4p=>%4!sH$#4p=5f1R3%`2'^p=:f3R4f2R5'11132']p=3g00<UR6g00=5R77_2p==%02#0!s$_p=2g00QVR8/I2p=<P8P3g00R4P2C\p=D!s4%[g00S:R9P9g00SZR9P2g00T:Fap=Cg00;5R:#4R;#;R<#4#;R=#JR>#HR?%J<#H#f[g00TZ%9:R:#4#6R<#?#>#6R@#?#;#>#5#8RA17>3RB1:B2RC%6@#5!s=$@C3%><R<#;#6!sP$5#8RDPBPC%9<!t=$6#6!s=&EC3%9<#6#?!s;$;!s;$<!sR%:#;!t;$!sR%5#8R:C3'@'@P0PA17>5RC1:C3RBP@C3PDPCPBPEC3P<!s0$!sR$g009jRBf4RCP4P5CG#=P2!sc$4RF1:F5RG!sc$117>CRH,1A1:H4R4/1@PBf6RIf5RJPCCG#=RKP217>IRL,1Af7RM,7>/:I!sP%9RNg00;ZRO9F>Af8RPg00<6#2!s$?PMPAP@%<A%<@%8;R;%8=R='[RAg00U9RQ/K;11Q=1Z;=RR,KQ[[RS11Q;!|Z$?dRUAY;=3UW9R=11QR\U^9T!sB$UWRU#XRV%WURU%V8RW%U8RX%T8RY1A8@1A8;=Q8>R;'D'C1PY9R9P2P51I671R25#=dAO8Q3CSRQb4b7b811@RP2b3b5b6g00VCP3P2M>EW1W2P3P2O2n20010!s#$12!s/&W0P2O1PDPFPG!wa&FPG!wa%P0PDPHP4!s>&HP4P:C3PKP2PD17>JRK1:KCRC!sF$111DL1:LJRJ/1EPBPPPMPI!w]$I!w]$PRM,1D17>N/:PRP!sK$f;R4AF>DOf:RHg00B8R0#N#B#B#N#M#LPNPDPE%<D%<EPAPSP=PTPVPUPWPX1A8E/D;,CYP9P!uz+E!uz/WT!uzO<PKPC!uX$111<L11J:PIP211<M11P:PBP4AF><OPH%e0#d#B#c#B#b!tv&<P:%<<%<:!tv6:!tv5:!tv/Xc!tvN!s@-211000!s'$!sBAW<X:?W;o"). Qed.
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
Definition file_clean : ltac2:(zQ "40!h9!hhd!hv0!ijc>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1f$3>2wp@1$1@1$0#k0>2rp@1$1@1$0#k0P") := ltac2:(zQ "d2!h9!hhd!ijf!hv0!ik6!il0!ld!il7!iq7!u2!ht4!hse!ijc&@2$5@1$2@1$1@1$0#8@2$7N8^2&@2$5@1$2@1$1@1$0#8@2$7N8^1\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\1f$c\2wp@1$1@1$0#k0\2rp@1$1@1$0#k0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+ocN4@2$5@1$2@1$1@1$0#8@2$7N4@2$4@1$0#k0+vvvvvvvf@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+i8N8~0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+j8N8~0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+8N8~1@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+h0N8~1").

(* [comment removed for export] *)
Definition stdio_globals : ltac2:(zQ "30!h9!hhd!hv0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "d0!h9!hhd!ijf!ik6!hv0!il0!ld!iq7!u2!hse!il7!iqe!ir5\3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+nhhlqbN1@2$5@1$2@1$1@1$0#8@3$b@1$1@1$0#8@2$3@1$0#8Z@1$c@1$1@1$0#8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+nhhri0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0Z@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hrngg8N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+hrmvg0@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hrmuv8N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+hrmuh0@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hrmug8N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+hrmti0"). End FPX2.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
