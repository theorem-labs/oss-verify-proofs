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
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SegRead.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Export SumWalkTac RefNodes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefExitBase () := KReplay.lz_vm "##ABK47Corelib7Numbers7BinNums8positive02!sK=1N!sD?!si,1!si>Z!si#5stdpp9bitvector;definitions2bv!sg/4Init7Decimal4uint0:!sD@2!sD@9!sD@3!sD@4!sD26!uR%!sC%1C!sC13Nat;of_num_!sG#!sb25Logic2eq!s_#!v,?;bv_unsignedC89OSSVerify6Proofs:boost_json:fuzz_parse3!w@#SegRead7SEGREAD>range_writableC13~~~I!td;0C!s@76eq_ind!sB89False!sE$56Stdlib6ZArith6BinInt1Z6!v-#at!sF<3ad!sc=3pow!sC<2le!v;`=wseg_ok_!vC$!v:%C7!sw,!sp96images5Ubsan1M?loaded_segments!sm%!|?G3!y484True!{rB1!x029Datatypes4bool00K!sFA!sf=:comparison!sl>!sL/2!sLH3!z285!yT$00I!v#=0I!#3>C0!uD<6op!sL#00!yY<>pow_pos_nonneg!z%>!{#=:!sj#!sf%!w>=lis!w~@!sF$0K4!t2&9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr!z>#!sIC7K!t?L!st75Tauto8G!sJ'4C!sJ<B!sJ&!sH6:Z!t<+=Z!sT$CheckerC!vJ<4f!#4{#!sq?C!sq0_sound!~w/!#3pEtoreOk?s!s-#_ok_window!#6~7!xt,3nat!{5/!#<650!#<T?!y97!uN-;!zx%!u4$00!w7<5eKind!zj=uni!zj9!se%4kind!xb8!y513Op2!#5[3!t531c!#80N1U;RefExitBase;ref_!#82#1c!w@%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos37Corelib4Init7Decimalhf2D637Corelib4Init9Datatypesja4boolja4truehf2D0hf2D1hf2D8hf3Nil37Corelib4Init5Logicn51In52eq37Corelib4Init3Natp2bof_num_uint37Corelib4Init6Numberr2bUIntDecimal69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~t57wseg_ok69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hhbfloaded_segments35stdpp9bitvectorbdefinitionshm42BVhm44BvWfhm42bv46Stdlib6ZArith6BinInt1Zhp52lehm4bbv_unsignedja3natja6option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsht18store_okhp53addhp56of_nat01Zja4listhm47Z_to_bvja4Someht1h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~il63rdnn53andja4consja3nilhf2D2hf2D7" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma ref_wseg_1c : ltac2:(zQ "h30!h9!j5!l2!l9!m0!m5!ma!mf!o9!od!q4!s7!hh1!hl1!ho1!ho7!hof!ir0!iqb@3$9$2@3$c$dKd@3$e@1$0#k0+vsgg0Kv$8@2$f@1$0#k0+vsgg0@1$h0@1$0#k0@1$a@1$b@1$h2@1$5@1$h1@1$4@1$6@1$6$7$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefExitBase ()) ["FPX1"] "##+Op'0h01Hh11eh21xi001cp;1p;3p;2p;6p;5g0000j12Tg000Uj1<Tg0013j11!s/$Xj13Tg0026j3@!s/$Yj15Tg0037j1;!s/$Uj1:Tg0043j17!s/$Qj16!s/$oj18Tg005Lj19!s/$kj2GTg006Ej2F!s/$oj3ETg008Aj34!s/$[j6?Tg0097j2>!s/$Vj1=Tg00:6j2A!s/$Sj2BTg00;0j2C!s/$Lj5DTf0R0#2#2p=0g00<]R1g00=dR2#2R3#2#0#0R4#<R5%12#1!s$&0!s$03g00>IR23@R6g00>e#5#5#;#:#7#6#8#9R7g00?CR8g00?cR9'G1F56R6=E17=489dg00@CR9g00@i!sL$AOR134P9P8P9p-0P0g00B5!sA$BRP8n011000003!s+$0X19P2P1P0E?P81>80b0W2%=7,A6%33%34'B'CdDDo"). Qed.   (* [comment removed for export] *)

Lemma store_ok_data : ltac2:(zQ "d0!h9!hof!hqd!hr3!l2!hs2!hs8!l9!od!ig8!hl1!ih4!ihb>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1a@1$1@1$0#k0>1n$5>0@2$2+vsgg0@2$3@1$0#k0^2>0@2$2@2$b@2$3@1$0#k0^3@1$c^2+hjhgg0@3$8$4@4$9$a^5^4^3$7").
Proof.
ltac2:(KReplay.run1 (kr_t_RefExitBase ()) ["FPX1"] "h02Hah13Hhih23Hloh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91ah:1mh;1np;1p;2p;3p;4p;7p;>g0000j10Tg000Uj18Tg00Bnj1;Tg00CQj1WTg0013j11Tg001Xj14Tg006Ej27Tg00;0j22Tg009Vj1@Tg00:6j2>Tg0026j3=Tg002Yj1<Tg0037j1VTg003Uj1UTg0043j1LTg004Qj1KTg004oj1JTg005Lj1FTg005kj25Tg00D3j2ETg00D[j2:Tg00:Sj2DTg00E7j3CTg00E[j1BTg00F;j1GTg00F[j1HTg00G9j1ATg00GWj1ITg00HBj29Tg00Hej3?Tg00IHj4MTg00J3j7NTg00JWj2OTg00K9j2PTg008Aj3QTg00Kej3RTg00LDj4STg00M6l>TTf0R0#0#0p=6%00#0#0#0p=3g00=dR1#0R2#0R3#0R4#0#6R5#8R6#;R7%84#;#W[g00NA%11#1#1#1#1#6#3#3#3#4R1f1R4,76'2f2R8,76%@4'>%13#1#0#6#1#3#3#3#4R3'2g00<]f4g00>I9=61f3g00>e#<#<#V#U#L#K#J#FP8P1P3g00N`R9/511593%42R2%45R5'Eg00O>R1/:212151D25R:,:1[[1212R;g00BRR<AC254UW0121:\<^0;g00O\R;#B%G;%H9%A9%I9R;g00PHg00PgR<P<g00QGR<P91993g00Qg1992=?96CMg00RNFN1O;<P0P8g00?CR<g00?cR;'51P08=Q<;dAR914CSb4b7b8123:P0b3b5b6g00RnP4P0M>TW1W2W;X97W:o"). Qed.
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
Definition file_clean : ltac2:(zQ "40!h9!hof!hs8!ii5>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>1f$3>2wp@1$1@1$0#k0>2rp@1$1@1$0#k0P") := ltac2:(zQ "d2!h9!hof!ii8!hs8!iif!ija!od!ik1!ip1!hl1!ih4!ip8!ii5&@2$5@1$2@1$1@1$0#8@2$7N8^2&@2$5@1$2@1$1@1$0#8@2$7N8^1\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\1f$c\2wp@1$1@1$0#k0\2rp@1$1@1$0#k0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+ocN4@2$5@1$2@1$1@1$0#8@2$7N4@2$4@1$0#k0+vvvvvvvf@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+i8N8~0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+j8N8~0@2$b@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+8N8~1@3$6@1$3@1$2@1$1@1$0#8@4$8$9^4@2$4@1$0#k0@2$a^3+h0N8~1").

(* [comment removed for export] *)
Definition stdio_globals : ltac2:(zQ "30!h9!hof!hs8>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "d1!h9!hof!ii8!iif!hs8!ija!od!ip1!hl1!ip8!ik1!ipe!iq5&@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0Z\3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hiuuobN1@2$5@1$2@1$1@1$0#8@3$b@1$1@1$0#8@2$3@1$0#8Z@1$c@1$1@1$0#8@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hivjt0N8~0@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+hivjs0N8~0@2$9@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+vtgs0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+vsvt8@3$6@1$4@1$2@1$1@1$0#8@4$7$8^1@2$3@1$0#k0+vsvt0N8@2$5@1$2@1$1@1$0#8@2$aN8@2$3@1$0#k0+vsuu8"). End FPX2.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
