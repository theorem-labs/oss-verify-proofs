(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr ZBridge CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsAtomics.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsDepotLock () := KReplay.lz_vm "#$t_C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib6MState5Wrd64C13~~~C4ELinuxProcessSemantics5Riscv7Prelude4tget!sQKs!sQK5bvmapC47Corelib4Init5Logic8eq_ind_rK!sD+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00!t4G1I!tw19Datatypes6op!sq#00!wWT4TacX2wz!wR%I!v$72eq!tn?1Z02C56Stdlib6ZArith6BinInt1Z6modulo!sF<3powK!uL;4list01C!v\@;bv_unsignedc!utO2Bs;AsDepotLock9lock_post!zU&!vhS5Frame3mkR!{>'!u,?7Z_to_bvK!xAC2!tWT8PropExec7seg_rom!t^GD!ve-_in_range!sYA:bv_!xM$us!xN<2lt!zs<4prod!zqV!w/%:munch_refl!ww`5!sn$!si`:wmono!tY-!xC<3nat!|<?of_nat!|<=sub!w1>e!#4w8iff!tj%!s`;>pow!{`#_nonneg!sN<:!sN#!sJ&4!sJ&9micromega9SatDivModCZ!y-#!sP&!s{C7compareK!#4%:!#5L<!~~%0K!tZ56VarMap1t02!sD@1I!sD?0!sD6=RingM!s4'7Formula!tS87Env!sT#5PExpr!tX8!sI24!vu65Tauto8B!t8&!sH6:Z!t^+=Z!sT$CheckerC!uS<4find!sqAC!sq0_sou!sX8;ZifyClasses;rew_!z+%v!|YZ9stk_carve!#:/?x!wb#!s@63and!#:JA3!|l=addK!u,TCells4cell05!~\'!#?a>5Instr5i!s+#08K!#@`Iree01!#BLZ2MS!#BIOsex!#AvA3Sem5alu64!#:<\8alu_addi!#6zY8StepFast8sf_congT!wET7!tCT3Mem3le8!#<AF6bv!uV#!vh;?!s<26BvBase=!#>W#le_bytes!v}]9b!tK#!x9$!tz%!{];9add_assoc!wI]6sf_ad1!x8c=!sm$dr_ztobv!stc@sf_store8_direct!swc7sf!#?V^!tg0!z?#all!to%!#?dZ!#4&#;cb_split_ok!so`8!so'!|V&!#5a^1!tX`5csiz!v4[4!w,#Arw_!tW#s!w#%!v9c6c!}D%!v}aell_upd!slZ3TacA!uD%lb_of_b!#=%#!ssdu!ssh5dfa!|p'!#LBC1K!t1W4ibnd!yp'K!#>=;1!u6Yib!y;]!sg#?!vl%ctx_intro!sq^9!sq+!sk%!#A;8or00!#BoA8or_morph!sNB7!#C?%!sMB6eq!sL%!xM;length!#9`24Znat5Nat2Z9i!#K'&K!#H%B5Psatz!#G\7!sO86K!#FM?;!tZ%!wI$!#ZM-!#Jq7!#SzT3Mem2wa!xc&!veA9and!w]&!#3PS!#GK#6inside!yx^=!#SC$write_!#R[&!#@6I>!#A~#!sE+<!sk%to_mem!y1,5Lists7!s+#Def6firstn!#Ok<add_0_r!#_p;trans!#BM@9bv_!#Wf$!#=0T!#Ak&6v!#Eh^!#9p#D!#Y<'!#[$%!#D2#!sw%!#UN;shiftl!u-]5v_lu!u,'!vDDconcat!t<^b!t<,!#H<M1!#G0Q@!#G'&!vf#word!#\}Dextract!}uX4sx32!uK&!#=xX!#A1$2!}N[!#Jy$4!se^@sext!u{'_!sr]!{/$=wa_of!{+'!yr'!}V66eq_sym!t4Y@!#C/'read_a!#Hsc<sf_load_goal!zbT6!#S%H9!#mN#_set!t&N5!t&I6bv_lts!#<T;4negb!v>abranch_pc!w3c!#T%&1!#57A3le!u%U7ZBridge=!v/%_zero_r!zGB!#]n-4Bool!s'$=!vR#_true!#@O5!sc%5proj1!#7I<leb_g!#63]4v_or!w6[!#:>'alu!sm+!z9N:!#=sY>ms_svc_pendingI!sl[achine_result00!t\Z4step!ulNDK!#][C4core!#:8<!sO-exe!#XoT!#_g%;interp_eff0!xqZ!sp'lift!vf&!xtA!wZR3!snj2!xJZ8!#TV&!wzE3!ve#6!sNJ1!sNJ7!xqE;amo_al!#E9$!sTD9!sT#!#@M#!#lfD7!sIE!#R4P2Bs9AsAtom!w@#!u--_!#Z}'!wnZ:fetch!#Bm%!xXYis_ecall!#;UADecodeC:d!s-$_any!|C[8step_gen!upA!#<u4eq!#vm<3!sC#!#W'7no!#wh<7eqb_neq!sG=di!#|D#!tF=div!sC=mu!#x5<=mod!#x5#!#[2$!sM@neg!sM25!zT$8PreO!s/#1Z;!tx#0_r_ext!sL>!st#!sL'!x-S9LiaTuning9zify_done!#>>=9False!#>A9>!#>A#f!sH%ff!#>#<!wh#eq!#9]ME!#p:Elow32!#49I8C3!#LV$7tac!sF#<f_equal_help!#H5XD!#d>3!#H9\!sw$>!sn%!#N^$4'!#D-A8!vs#!#jY#!t;Y!u4+!#Vk#!u-Z3Mem:!#]9$!#M2+!#bhW5wdesc!#i[[!si#6wds!#bO`>!#Zb-wd!#IAb?!#MN%!#p;a!#]8$;stk_releas!}g+!#;$3!#^R-5mkre!y4Z@!#Y_&lit_self!t@'!#wCBnot!#whEnd!#9nZ6ret!#M{\!#Cx&!sk%_fold!#Cx@!#4I54!#NP=or!ta[<!#]y'!#?4+!#@+[!$;~$!~<#!#4=Z!$#3#evt!#8m-!sk]step!sk[TacX7sx32_!$AG&!#P^@le!{XY8!#5f&!}[`3stk!#6I]7mem_inv!w8_3ev!#s:B!$=|$1!uZZ5!$<I#!#41G3inj!#4TDapp!#p4B!sK$!$9-@3!#IgD3!#o_C!$93'1!sQ6!$8E%G!sJ'4!sJF8!$CiA!#6f&obliga!s:#_1K!$KaC1!$4RN2!#Q=i1!#nH:5skipn!},Y!$#;+!$%`0!#Ec77!#C;%!t9Y!#A$+!#}/^!#he$:!#D#%!$&1\!sn%7!$$O#!#De`D!#3;%!#E]%!$&5-!z_F3!sJF6!#4{W!#DF+8!#5iZTac!#iC+fram!#vX'!u+F5!#56Y;!$JY$!#G=_Tac!#C6#!#x\f=ov!#l7$!$9tY!#Ed-!$59&load!vgL7!$I~9x!#99U7CodeTab;!#>V&_!#G=&!$&p+!$DP5!$Dn@!#ZgS5ASegs5aseg!|8&I!}vY!#tM$0!#;S;8ZifyInst7Inj_Z_Z!$MO;!$Q=#0!$K3;5eKind!$N5<uni!$N58!se%4kind!#:s7!#;F03Op2!~q#!t5@!$Od=bool!ws/!sF8!tUJ1I!#HcL0!#jeY=!#;&&state!sm=!#iT20!{y84Tru!$aI4!#or%!#Y?#!v:D2!v:I5!$Wu@1!#L>Gmsize04!|KY7ct!#3T#!#EA2!$dY<3!$aA^:DEPOT_LOCK!#352!wG40!z^<:!$X#$ison!$VH7!$4K:0!vnHaluop!#5j]8ct_entry!#7@;!tn;!#p{E2w!$`dT!#Sz&w0!#QL+!#7/=N!z6P3!sRG;!#|E%cond04!wLN9!sRG6awidth!#3pB!#a|'0I!us?!sD>!{k,0!ulT2!xJG1I!#@1V!#_Z%0!xH'!thR1!yg]1!yg,".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv37Corelib4Init9Datatypesk46option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm5dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeqc5bvmap37Corelib4Init5Logicta2exta3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~v95asegsk44consk44prodk43nilk44pairta2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hlc4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hq02wz46Stdlib6ZArith6BinInt1Zhu13addi2bbv_unsignedk44Nonehlc2C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ihb3mkRihb5munchihb3stkihb5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~in72MSin76ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~is47mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jg97seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jl38rw_cellshu13powhu12le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsDepotLock~~~~~~jq7aDEPOT_LOCKjq79lock_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~kg33evthu12lthu16moduloi27Z_to_bv" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition DEPOT_LOCK : Z := 0x0b1510.

Definition lock_post : ltac2:(zQ "60!hc!jf!h9!lc!pc!t2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1P$2>1v$2>2lo$2>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>0$4P") := ltac2:(zQ "he1!hc!jf!ue!h9!v3!hj4!hjc!lc!hk3!hka!hl0!hl7!pc!hp8!htb!hv9!ig0!ige!t2!ih5!il7!ile!im7!ime!ir4!ira!ive!jk8!joe!jpa&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h2@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1P$3\1v$3\2lo$3\1m~0\3ms'$c@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$4@3$b$c^h1@7$h8@hf$h4^i7^i6^i5^i4^h0^f^e^i3^i2^d^c^b^a^9^8^7^6^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^5^4^3^2^h7@1$h9^i7^h6@1$h1@1$1@1$0#k0^1@1$hb$5@2$4@3$h5@3$6@2$8$3$3@4$a$3$3^h3@2$h0@1$0#k0^i6@3$6@2$8$3$3@4$a$3$3^h5@2$f^h5+4@1$9@2$8$3$3^h2^1@2$4@3$h7$5^h2^1@2$4@2$ha$5^1@2$4@4$hc$5^1^h5@3$6$d@1$h3@1$e@2$f^h4@2$hd+2+hf@1$9$d@2$4@3$b@1$1@1$0#k0^d@1$e^h4@4$h6$5^1^h3@2$h0@1$0#k0^i6").

Theorem lock_spec : ltac2:(zQ "he0!hc!jf!hj4!h9!jq1!hl7!hp8!htb!hv9!ig0!ige!hjc!hka!lc!v3!t2!ju8!jv6!ih5!kje!il7!im7!ir4!ive!jk8!joe!kk5!kkb!jpa!kl5>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$f@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$d@1$1@1$0#8>1P$3>1v$3>2lo$3>0@3$5@1$1@1$0#k0^hc@1$7^3>0@3$5$3@2$hb^4+4Z>0@2$e@2$4Z^4@2$ha^4@2$hc+2+hf>0@2$4Z^6>0@2$4@2$8^7+4^5>0@4$h9$2^9^8@3$b$6@1$h2@1$7^7@1$c$6>0@4$h5$2^a^7@2$9@1$0#k0^ia>0@2$4@2$8^8+j0@2$9@1$0#k0^ib>0@2$h7$2^c@3$h3$2@h6$h1^ie^id^ic^ib^i7^i6^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^f^e^c^b^a^d@7$h6@hf$h4^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f@2$hd@1$0#k0$h0^e@1$a@1$1@1$0#k0^d@1$h8$2").
Proof.
  intros until lo. intros -> AL VB P0 PLO C ST LO MI. unfold wz, DEPOT_LOCK.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 4)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  do 10 step.
  (* [comment removed for export] *)
  zstep. rewrite sx32_wz by lia.
  step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  zstep.
  (* [comment removed for export] *)
  astep. rewrite ?sx32_wz by lia.
  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso; lia. }
  (* [comment removed for export] *)
  astep.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso; revert K3; rewrite ?unsigned_lit by lia; lia. }
  step. if_cases K4; zify_cond K4. 2:{ exfalso; lia. }
  do 5 step. release_frame FR ST (bv_unsigned sp). step. step.
  rewrite unsigned_lit in C by lia. apply lock_cell in C; [|lia].
  finish. all: try reflexivity.
Qed.
