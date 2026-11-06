(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SegRead.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Export SumWalkTac RefNodes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefExitBase () := KReplay.lz_vm "##@\K47Corelib7Numbers7BinNums8positive02!sK=1N!sD?!si,1!si>Z!si#5stdpp9bitvector;definitions2bv!sg/4Init7Decimal4uint04!sD@;!sD@3!sD26!tn%!sC%1C!sC13Nat;of_num_!sG#!sb25Logic2eq!s_#!uI?;bv_unsignedC89OSSVerify6Proofs:boost_json:fuzz_parse3!v\#SegRead7SEGREAD>range_writableC13~~~I!td;0C!s@76eq_ind!sB89False!sE$56Stdlib6ZArith6BinInt1Z6!v-#at!sF<3ad!sc=3pow!sC<2le!v;`=wseg_ok_!vC$!v:%C7!sw,!sp96images5Plain1M?loaded_segments!sm%!{[G3!y484True!{6B1!x029Datatypes4bool00K!sFA!sf=:comparison!sl>!sL/2!sLH3!z285!yT$00I!v#=0I!~ZD0!uD<6op!sL#00!yY<>pow_pos_nonneg!z%>!{#=:!sj#!sf%!w>=lis!w~@!sF$0K4!t2&9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr!z>#!sIC7K!t?L!st75Tauto8G!sJ'4C!sJ<B!sJ&!sH6:Z!t<+=Z!sT$CheckerC!vJ<4f!#4{#!sq?C!sq0_sound!~w/!#3pEtoreOk?s!s-#_ok_window!#6~7!xt,3nat!{5/!#;R50!#;p?!y97!uN-;!zx%!u4$00!w7<5eKind!zj=uni!zj9!se%4kind!xb8!y513Op2!#5[3!t531c!w>O;RefExitBase;ref_!#80#1c!w>%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos37Corelib4Init9Datatypeshf4boolhf4true37Corelib4Init7Decimalk52D0k52D1k52D2k52D8k52D9k53Nil37Corelib4Init5Logicna1Ina2eq37Corelib4Init3Natp7bof_num_uint37Corelib4Init6Numberr7bUIntDecimal69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~ta7wseg_ok69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hi0floaded_segments35stdpp9bitvectorbdefinitionshm92BVhm94BvWfhm92bv46Stdlib6ZArith6BinInt1Zhpa2lehm9bbv_unsignedhf3nathf6option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsht68store_okhpa3addhpa6of_nat01Zhf4listhm97Z_to_bvhf4Someht6h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ilb3rdnna3andhf4conshf3nil" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma ref_wseg_1c : ltac2:(zQ "h20!h9!j7!je!lb!m0!m5!ma!mf!n4!oe!p2!q9!sc!hh6!hl6!ho6!hoc!hp4@3$a$1@3$d$eKd@3$f@1$0#k0+vpgg0Kv$9@2$h0@1$0#k0+vpgg0@1$h1@1$0#k0@1$b@1$c@1$5@1$4@1$5@1$7@1$7@1$5$8$2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##+=p'0h01Hh11eh21xi001cp;1p;3p;2p;6p;5g0000j12Tg000Uj1<Tg0013j11!s/$Xj14Tg0026j3C!s/$Yj13Tg0037j15!s/$Uj1;Tg0043j1:!s/$Pj17!s/$oj28Tg005Ij29Tg0063j3ETg007Ej36!s/$_j6DTg008;j2B!s/$Zj1?Tg009:j2>!s/$Wj2=Tg00:4j2@!s/$Pj5ATf0R0#2#2p=0g00;aR1g00<hR2#2R3#2#0#0R4#<R5%12#1!s$$0!s&$!s$,4g00=MR23CR6g00=i#3#5#5#3#;#3#:#7R7g00>GR8g00>gR9'81956R6=E17=689dg00?GR9g00?m!sL$@SR136P9P8P9p-0P0g00A9!sA$AVP8n011000003!s+$0X19P2P1P0EDP81B80b0W2%?7,>6%43%44'='@dDAo"). Qed.   (* [comment removed for export] *)

Lemma store_ok_data : ltac2:(zQ "d0!h9!hp4!hr2!hr8!j7!hs7!hsd!je!p2!igd!hl6!ih9!ii0>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1a@1$1@1$0#k0>1n$5>0@2$2+vpgg0@2$3@1$0#k0^2>0@2$2@2$b@2$3@1$0#k0^3@1$c^2+hitgg0@3$8$4@4$9$a^5^4^3$7").
Proof.
ltac2:(KReplay.run1 (kr_t_RefExitBase ()) ["FPX1"] "h02Hah13Hhih23Hloh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91ah:1mh;1np;1p;2p;3p;4p;7p;>g0000j10Tg000Uj17Tg00B2j1;Tg00BUj1UTg0013j11Tg001Xj14Tg005Ij28Tg00:4j23Tg008Zj1ATg009:j2?Tg0026j3>Tg002Yj16Tg0037j1=Tg003Uj1TTg0043j1STg004Pj1RTg004oj25Tg00C7j2JTg00C_j2:Tg009Wj2ITg00D;j3ETg00D_j1DTg00E?j1FTg00E_j1CTg00F=j1GTg00F[j1HTg00GFj29Tg00Gij3BTg00HLj4KTg00I7j7@Tg00I[j2LTg00J=j2MTg007Ej3NTg00Jij3OTg00KHj4PTg00L:l>QTf0R0#0#0p=<%00#0#0#0p=2g00<hR1#0R2#0R3#0R4#0#<R5#7R6#;R7%74#;#U[g00ME%11#1#1#1#<#1#2#2#2#4R1f1R4,86'3f2R8,86%A4'?%13#0#1#1#0#1#2#2#2#4R3'3g00;af4g00=M9>61f3g00=i#6#=#=#6#T#6#S#RP8P1P3g00MdR9/511593%42R2%45R5'Jg00NBR1/:213151I25R:,:1[[1312R;g00AVR<AE254UW0131:\<^0;g00N`R;#D%F;%C9%G9%H9R;g00OLg00OkR<P<g00PKR<P91993g00Pk1992=B96CKg00QRF@1L;<P0P8g00>GR<g00>gR;'51M08=N<;dAO914CPb4b7b8133:P0b3b5b6g00R2P4P0M>QW1W2W;X97W:o"). Qed.
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
Definition file_clean : ltac2:(zQ "40!h9!hp4!hsd!iia>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1f$3>2wp@1$1@1$0#k0>2rp@1$1@1$0#k0P") := ltac2:(zQ "d2!h9!hp4!iid!hsd!ij4!ijf!p2!ik6!ip6!hl6!ih9!ipd!iia&@2$5@1$2@1$1@1$0#8@2$7N8^2&@2$5@1$2@1$1@1$0#8@2$7N8^1\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\1f$c\2wp@1$1@1$0#k0\2rp@1$1@1$0#k0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+ocN4@2$5@1$2@1$1@1$0#8@2$7N4@2$4@1$0#k0+vvvvvvvf@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+i8N8~0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+j8N8~0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+8N8~1@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+h0N8~1").

(* [comment removed for export] *)
Definition stdio_globals : ltac2:(zQ "30!h9!hp4!hsd>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "d1!h9!hp4!iid!ij4!hsd!ijf!p2!ip6!hl6!ipd!ik6!iq3!iqa&@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0Z\3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hirpkbN1@2$5@1$2@1$1@1$0#8@3$b@1$1@1$0#8@2$3@1$0#8Z@1$c@1$1@1$0#8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hirup0N8~0@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hiruo0N8~0@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+vpro0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+vpqp8@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+vpqp0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+vppq8"). End FPX2.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
