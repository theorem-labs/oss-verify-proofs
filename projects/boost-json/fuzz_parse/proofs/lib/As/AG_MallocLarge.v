(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes RefNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX AsAtomics AsDepotInv AsDepotHash AsDepotPut AsUnwind AllocWalkKit F_memset AG_Frame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AW_Leaves AW_PoisonShadow AW_DepotFrame AW_AllocBase AW_MallocBase AW_LargeAlloc1 AW_SysconfPg
     AW_AllocSec1 AW_AllocSec2 SecLazy SecLazy2 SecGap AS_LargeAlloc AS_AllocSec1 AS_AllocSec AS_MallocLarge1 AS_MallocLarge
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_LargeModel AG_MallocLarge1 AG_MallocLarge2 AG_MallocLarge3 AllocTacX AG_WriteSet.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_MallocLarge () := KReplay.lz_vm "#&80c89OSSVerify6Proofs:boost_json:fuzz_parse3lib2As>AG_MallocLargeBm!s2$_l!s3#_gpostC13~~~K4ELinuxProcessSemantics?!s<23Run6config01C!t[R8A!tK#Rep4AREP!tG%I47Corelib4Init9Datatypes4prod00I46Stdlib5Lists4!s+#5NoDup00C!sB62In!te\3alb!td%C!td15Logic3iffI!s?8and!t\#!sA65proj!vG]6ast_ok!tc&!sl[8inst_rep!snb9flags!sof:thread!spf7sec!smf6ia!uMgregion!spgpclas!w1gA!tb&shadow!swf?!sw&junk!suf4a_!#42&C7!sjN>Asan!sk$Model:ch!t^#li!ss+!{K\!sp%!uP,!td^5as_tq!sne7qc!uQg;batches!uSmgq!w4cplaced!#5:[7!so$Wf2WF!zGf!#8L%K!#7p'7Numbers7BinNums8positive02!sK=1Z02C5!#:9%6ZArith6BinInt1Z6modulo!sF<2le!sB<3add!uVUsS!~Y$5aceil!vCepa!sj[!tW&4aap!#3<b5a_thr!skdkobj!tXectx!yNM!#Ak]dis!t|ff!{L'!~Z_6as_sec!soe:sc_map_beg!sse;!ss&size!st&!|Y<mul!#Ck8not!zU`op!tICpow!t0_bot!t0B2l!u9T:AsDepotInv4d_nb!y~Y!sl1!#6M4!#IY2list01!xa_=as_n_reserved!yYe4zlen!usV3Lib4TacX2wz!se`b8!vS&!seS5Cells4cell04!#3,bw!#?TY!tW#3Arr6u64ar!#7GY?!#Qj01<senv_of_a!#@F'I!syR>AW_!ss$!uX$14SENV00!tmY9!vD'X8awin_vis!soc:!#Mo#x!#Gu\9!vQ+<i!vKd=AW!ss&Base4I!vJ-!#A'=N02I45stdpp9bitvector;definitions2bv!#S'98eq_ind_r!zo\6AMODEL!wNc7akernel!snc;ak_hsm_ful!#BP[!#Ad%2sh!sh&!v{@;bv_unsignedC!#ZjI5State8m_vmmaps!s]Q7vm_!s\$!#6kN<LazyRestrict:in_rangesb!#4]a?a!tX#_in_ledger!sud!#S3%visible!sub7ABUDGET!sm&!#Om^as!w:%!spemp_kin!#;w%!#]k72eq00K!#P-^m!t0#03!#3@%!spe4!unibase!|aG7Z_to_bv!t>c!#Ed+K!#cr@1!wN9or00!wh:x00!}lQ;vm_noac!s;#!{7\3a_L!wQV:!~[#L!}W$9nooverlap!sna>entries_nowra!#\yeA!uOW!#5+0eager_us!#Ed'!w,^S!t\c;pages_tota!#UQdPhi!|F'!#9WOvm_limi!#KZS=AG!#C;$!|Y$9!#nr$re!#_6e;comput!stj7rq!#Q%-!#5?^rq_rz!sne:!sn#ound!#M%f8!sp$_u!#aie9rq_nee!te,!#TM<ax!uwcprimary!u+e4!u+#!sme<!y:#_too_big!uvB7div_mod!v?=div!sC<=mod_pos_b!x$#!sMAneg!sM25omega8PreO!s/#1Z;!t[#0_r_ext!sL>!st#!sL3!tA38max_spec!sH<>pow!u2$nonneg!sN<:!sN#!sJ%!#<E;3nat!#f#A3K!#y:&9micr!uK$7EnvRing3Pol01!sG6=!sD#M!s4'5Psatz!t6#!sOI7I!#X^@0!so66VarMap1t01I!sD?0I!tSC7Formula!t5#!tU:6option!uH8!v:'5PExpr!v<8!sI22C!sI55Tauto8B!tZ&K!#EV:1!sb6:Z!uB+=Z!sn$CheckerC!v7<4find!sqAC!sq0_s!|G@3sub!#<6[9!#hD#_env!#=#a8aapp!sn-!#4IN8HeapCeil5h!#m+^!#QZ%;!#mq#_fact!#XYc@sh_!st#ing!#P+$!sw%!y98!$&V#!#au_<as_space!#hO,!y>59SatDivModCZ_!#63#!#3~#!#4,'!{iC7!v,P3Lib9LiaTuning9zify_don!#Q=b4a_Z!#Rx%K!sjR<!sj$WalkKit6hidden01!t^V!uQ#6M!#DD#<!#WT&_li!#bH&!xR76!#[b$!#;p<ad!#9m#!w}Cdiv!w}3!#Mi91C!#5o;length!tZ<6of_nat!$3]6:!sa%_map!x0S;!wD$Budget6pusage!|sc7ak_a!#nh+!#IEO9!$8P$!sd#!#3xW;!#3x#!~:/!u>S6SecGapCgap_witness_fit!#q1,!v7`imgr!snc9ak_shland!spc8ak_zrsh2!sogt!#\+,!so`c!sokp!sog!w4$b!sp,K!#Y>:1!s@<2!yJapamc!|[W<map_contains!tQaresf!tQW;vm!#v>+!s`Q!$7p%free!{Gc!$,,[!#nk0:icpt_chain!suY8AsUnwind6utrac!#4PY>AS!#tp-A!$G\/!$G[+!#E7<eqb!wRQ=!#ix#sub!u+#t!#:`;3app!#|}A2I!#7}N6LazySR4lzok!#vO'!#]E[8r!s/&!w=V!#{J#Frame3mkR!sgZ!#@'%6ret_pc!skZ8PropExec7seg_rom!t[a2MS!zDY<AS_!|u$Sec18as_mod!#u2Z!{824ml_W!wk`5munc!#u1%I!uOTW!uO%!#z>#A!#z>-!t[T!$%l,1!sjf3!sjf!#>%Y;!$0K%Hash:d!s0#_ha!#y4'!ssR!$1@,7d_putid!zC[!wr-5b1!$C0+!#45'!#GM$7!s+#Def6repeat!t6\Sec2:sec!$Kx%!uud5!uu$!smY!#TZ1!#LX,!#t#>D!#}b,_!#{k&!sYA:b!#ae#ulus!#9K24Znat5Nat2Z9i!#_='!u?R7SecLazy>free_v!#y}#pe!#F[c9ak_fs!#D1f:ak_sec!#{dY9!uR#NodesA!#@b,_!wz#r!suV8Ref!st$>!st/I!$8fZ2Nd:and_elimF5!vHY>!vH'Facts2;!#6|#_agree!tdZ!#7m$7outside!|-d!tX#_on!snb6ARHEAP!ydc7!$2m$X!snY!|;':nonvm_same!#44Z!$7<&2<!#7w$!$RL$!},d!ss%co!#ba[G_!xl%amfr!uU\;AG_WriteSet6acompl!soe4avm!$Me%!#ZF<to_nat!#=;_5!vY[!#db'ddressa!$3#'I!#kVB0!#{9_am_!#KM%!#<o%!#lnC!$PyS!#}G0;!#L]$stat!#M][!{f'!sw$?!|X#_but!#=q_!$DL137lg_co!$^ZZ!st22<arheap_afte!#91V!$+z0z!#><&!$mm8!#O>,orb!t6]?!$<8+_con!#<0&!#cM&4Bool!s'$<orb_true_iff!#5mZ5!uL#W!w5i:u8arr_app2!v@8!$DN%iff_refl!#gK5;ZifyClasses3inj!sIB;rew_!su%v!#ff6=!#F<$_!#gP%!t\7!$r1#!#\^P!$M,#Mem8bytes_a!$Mq[Mem5wr!sg,!tn13Nat!$aZ#!#i7=app!#}t<eqb!#}t#!#4y;7!wL#ect00!u2T!#Rl%C!$<D%_!$F/-!v+Y4Step8rw_cell!{[3!xm99and_morphK!#zt;G!#|P&1C!#9WX:!t^$!$2q-!snT!#=4#=disjoint_f!#W'\!sq%B!vD'_transpor!$q&V!#[s%7lzok_LM!sh];!sh$!#4a$!slV!#Ie+Flazy!so&_okb!$>G_!#9P2=a!#Yg#x!#8[/!szb4lg!$As&K!#?aS!#D-%3a!$^t#!{V&!#h}Ovm_m!$eE#ase!saQ6vm_brk!t>Ustart!sa$!#8zaB!#Gi-!wZ_=AW_!#Ut#!|%$8d_sb!#Uy\!ss4nb!#Vn^!#Hg%<bsep_!#NZa!sr&4!sr#!sjbCapriv_!wH%sta!xa#!syb5!sy$!sk%I!#\::Forall!#9dQ!t4/B!u//block!u-c;!sx%stack!xTc!sq%!%/3$!srdrng!$a-#!$v\]!sr&9!tf%!so,3!#]R$7tac!xh#<f_equal_help!utc!#J&^!sr3ptr!$hD[!sr+:!sr%in!%:z+!z\A1!sGC2!tZ\@!#TO%!xG#!#k7,!svP!#\q3!$mx%!#DT7in!#^t#iff!$ZO^6s!%/k#!$3&W!#Uf15awrit!sne6astatw!soe@!#X8$!wX+F!vl2!#N++:!#N+'r!t?_9avmx!#O>-!xk`3!uxY!#Uq0:!#Uq$nre!#6LY!#=r29new!#7E$!sv&!#Ki:4ones!sD=!$1$#!sD;9!sD#_!sg$!{B^!|1#!$Pi0!#|~;andb!y-6>!s>#_fals!#T6$!$#+;leb!sC>t!sC=6leb_gt!sF>tb_ge!xsa?!#]$+!x}$!z\];ex_introF16!sl^!{J,2!|8^ex!sk%18!{AY!#|X1C!$+j/srea!#7kh6!}/h1C!tf%!#P&$!$y+/!wIa11!slh3!slg2!vJ&!$/?PSR!wq#6!wx%!$~jW!#T,+3st!#{|A3map!$V?J4!sOK6!sO6!$RR,;!~t%!u=$!$UC7!sR;3!tOK5!$Wq?2!sD@!t3E!$Wq'1!#ZkE3!sJF4!sJF5!sJF7!$OyD5!sIE3!sIE!u#G8!sJF6!{>Z5wmono!|%Z3Mem7mem_i!$XYW3!%31%5!#gi#!#5dX!$+U-DEPO!$}:&!#X3I>Riscv!sE+5wview!#b`A5mkapp!sKB6!sK$2!sqErel!w>X2w!$BM&!tWBeq!#@1#!sLA8or!#e'$!#oF<fs!$?{=sn!%K]S5ASegs5aseg!#axV4Scfg=hunspell_scf!$[D%!$gS?!$}7,!sD6!#x,_9kPageS!$sLg@kPtrArrayR!$IN$!|'Y!$'c+AFS_SIZE!#<5U!#P#90!tab5AINS!}d&I!#4jS!#~E,!tW&!$kY<bool!$jJ=!sF%1!sFB!#<KN!$lO6!sR;0!#;jC3Op205C!#8Q:5eKind!ut=uni!$nO8!se%4!%0f#!ut>!sf$1!ttI!sMJ3I!#7DX=machin!$$_%00!{,`a!sk&!yTB!$t/#0!wD68ZifyInst@!$ai$_!$-P$_eq!#Nr'5!xV$8PeanoNa!#x&+!$=u<7inj_add!$uf@!%3+84True!#e>T!$3Z,ALIBCPGSZ!~9Y!$Ug,AGOT_SS!$7lc9ASSPGUARD!wm'!#nzN5!xX$!$1'akNum!#;k%!#6;d5!#6:/!#:H<!%[s+3!#6_T!$4M%6AHI_LO!#:'d:kSpac!#:xiAkC!uy#sB!#[p#oun!$Hfb3ATP!sib4ATSD!xKe7mapping!#3Z'!y?_!%@~$!y?'!spe2!spl6!spl!#i<'!$n{Opage!$&x$!tP^8kMax!{8,!#6O75False!#>x3!#6l-1!#FsX8AIMG_TO!zwZ!$sU/B_PRIM!{h[!#32%3mem!siY!$Us/>k!s1%egMagic!{me6eff!$3r$!tkX!w4%<ASHADOW_BASE!z1'!#=f<7Inj_Z_Z!#3U[7ACFLAGS!t92!#qZ,8nil!#l}$!t2]IAINIT!#5Pa!sm%!#HUW!#7&/as!wj+!skS!$ZF/!s/#!$hRW!#:Q3LowMemEn!%A4e;kHighMemB!%n`g!st'!tjh=kMaxNum!#<C$!sv%".
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Statek65Model37Corelib7Numbers7BinNumsnc4Npos35stdpp9bitvectorbdefinitionspc2bv37Corelib4Init5Logicre3andre2exnc1Z37Corelib4Init9Datatypesu14list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hg05asegsu14prod69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hkb6astatehkb6effectu14pairre2eqpcbbv_unsignedu14cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~hs13a_Lhs13a_S79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~igd3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~il24cellu14Noneu14Someu13nilu16option3h5LinuxProcessSemanticsfLinuxProcessSem3Runir35mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AG_Frame~~~~~~iu87amframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAG_LargeModel~~~~~~jj1blarge_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~jo3cdepot_placed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~jt3fsame_but_shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAG_WriteSet~~~~~~kia6acomplkia4avmx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAS_MallocLarge~~~~~~knd4ml_Whs16ARHEAPhs14a_Zr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~ktb7AMODELXktb8awin_visktb9depot_covktbaflagsx_rep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~lkc5DEPOTigd4aappigd5aceiligdbaddressable79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7SecLazy~~~~~~lr5anonvm_samehkbbam_malloc_k69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~mgf8restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~mla4lzokil22CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mq13mkRmq15munchmq13stkmq15wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mvd2MSmvd6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~nka7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~nof7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~nt98rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~oi02wz46Stdlib6ZArith6BinInt1Zom13addom12leom16moduloom16to_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~opa6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~otddhunspell_scfg89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocLargefMallocLargeGlue~~~~~~pi5h2malloc_large_gposths14a_sths15a_thrhs14a_pahkb3reqhkbbcompute_reqhkb9rq_neededhkb9kPageSizehkb8round_uphkb6as_sechkb6schunkhkb4zlenhkbdas_n_reserved79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAW_MallocBase~~~~~~qh2aicpt_chainhs15a_tophs15a_bot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsUnwind~~~~~~qn56utraceu16lengthom16of_natlkc5depot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsDepotHash~~~~~~qt9adepot_hashlkc5d_putigd2shom13div79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAG_MallocLarge3~~~~~~rje4lg_Lhs13astrje7lg_cosths14a_ALhs15a_ctxhs15a_fsbhs15mkAstom13subom13powom12lths13ATPlkc8d_frameslkc5d_idsu14boolu14trueqn59goodframeqn5bframe_chain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAllocBudget~~~~~~sha6B_PRIMsha6pusagektb4AGAPhkbh1kChunksBlockCountom13mulhs18AFS_SIZEhs14disjlkc4d_nblkc4d_sbpc7Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MallocLargeGlue.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).
  Let st : ltac2:(zQ "10!hoc$0") := ltac2:(zQ "10!pp0@1$0?1s").
  Let TH : ltac2:(zQ "10!td$0") := ltac2:(zQ "10!pp8@1$0?1s").
  Let sb := a_sb s.
  Let pa : ltac2:(zQ "10!td$0") := ltac2:(zQ "10!pq1@1$0?1s").
  Let CTX := a_ctx s.
  Let r : ltac2:(zQ "10!pq9$0") := ltac2:(zQ "10!pr0@1$0?4size").
  Let needed : ltac2:(zQ "10!td$0") := ltac2:(zQ "10!prf@1$0?1r").
  Let msz : ltac2:(zQ "10!td$0") := ltac2:(zQ "30!psc!pt9!on9@2$2@2$1?6needed$0$0").
  Let nch : ltac2:(zQ "10!td$0") := ltac2:(zQ "30!pu5!puf!pv9@2$2$1@1$0?2st").
  Let nres : ltac2:(zQ "10!td$0") := ltac2:(zQ "10!qg1@1$0?2st").
  Let CHI : ltac2:(zQ "30!td!v9!hk4@1$1@2$2$0$0") := ltac2:(zQ "40!p5!hqc!ql5!qm3@5$2@2$1@1$0#k0?2ra@2$1@1$0#k0?2s0@2$1@1$0#k0?2sp@1$3?1s?2CH").
  Let T : ltac2:(zQ "20!v9!td@1$0$1") := ltac2:(zQ "50!p5!qmc!qm3!qr3!hqc@6$3+pgug0@2$4@1$0#k0?2sp@1$2?1s@1$1?1s+he?3CHI").
  Let nT : ltac2:(zQ "10!td$0") := ltac2:(zQ "30!qrd!td!qs6@1$2@2$0$1?1T").
  Let d' : ltac2:(zQ "10!qt0$0") := ltac2:(zQ "20!rha!ri8@3$1?1d@1$0?1T?2nT").
  Let Wsh : ltac2:(zQ "40!p5!r9!hk4!td>1a$3@2$2@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!p5!olb!r9!hq0!td!rj1!rj7\1a$4@4$3@1$2@1$0#k0@1$2@1$0#k0@1$1@1$5^1@1$1@2$6?3msz+8").
  Let L2 : ltac2:(zQ "40!p5!r9!v9!hk4@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "20!ro3!hvf@4$0@1$1?1s?2pa?4nres?3nch").   (* [comment removed for export] *)
  Let sx : ltac2:(zQ "20!td!rob>1a$0$1") := ltac2:(zQ "h10!p5!r9!hra!hk4!td!jn4!rp2!rpd!ig6!kt3!qmc!rq5!rqe!pp8!qm3!rr7!rs0\1a$4@a$f@3$5?2st^1?4size@1$d?1s@1$b?1s@1$c?1s?2L2@3$2@2$3@1$1@1$0#k0@1$1@1$0#k0@1?3Wsh^1@1$8?1s@1$9?1s@2$h0@1$7?1s@1$6?3msz@1$e?1s@1$a?1s").
  Let U : ltac2:(zQ "10!td>1a$0$0") := ltac2:(zQ "30!on9!td!psc\1a$1@2$0@2$0^1$2+og0").

  Hypothesis HR : ltac2:(zQ "10!ks9@4$0?5HCEIL?1s?2LB?1m").
  Hypothesis AX : ltac2:(zQ "30!t2!li5!lje@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!lha@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!hjb!loc@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!js3@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!lj1@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!hjb!no4@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!p5!hjb!mud!hqc@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!lpd!oo0@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!p5!on9!oo0!hqc@2$2@2$1?2lo+rm0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "50!hq7!p5!td!oo6!hqc@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis SPT : ltac2:(zQ "50!p5!on9!oo0!rs7!hqc@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis SZ : ltac2:(zQ "30!rse!t2!rs7@2$1@2$0+vsg0?4size@2$0?4size@2$2+2+i0").
  Hypothesis TP : ltac2:(zQ "50!hq7!p5!rt4!olb!r9@3$0@1$4@1$1#k0?2tp@1$3$2").
  Hypothesis DCAP : ltac2:(zQ "60!on9!t2!rtb!ru7!oo0!rse@2$1@2$5@2$0@1$3?1d+1+hggg0@2$4@2$0@1$2?1d+hf+ogg0").
  Hypothesis FCH : ltac2:(zQ "d0!p5!hqc!qm3!rv0!rv7!hq7!rve!t2!hjb!qmc!sgb!on9!oo0>0@3$5$3@3$6@1$9?1s@2$1@1$0#k0?2sp@1$2?1s$4>0@3$5$3@3$6@2$1@1$0#k0?2sp@2$1@1$0#k0?2s0@1$2?1s$4@2$7@2$c@2$b@2$1@1$0#k0?2sp+h0@2$1@1$0#k0?2s0@5$a$8?1m@1$2?1s@2$1@1$0#k0?2s0?2CH").
  Hypothesis Ha0 : ltac2:(zQ "40!hq7!p5!olb!r9@3$0@1$3@1$1#k0?2a0@1$2?4size").
  (* [comment removed for export] *)
  Hypothesis ALLOW : ltac2:(zQ "30!rp2!rpd!oo0@2$2@1$0?3msz@1$1?1s").
  Hypothesis PNN : ltac2:(zQ "30!slb!sm5!oo0@2$2@1$1?2st$0").        (* [comment removed for export] *)
  Hypothesis AGP : ltac2:(zQ "10!smf@2$0?3msz?2mo").
  (* [comment removed for export] *)
  Hypothesis NSEC : ltac2:(zQ "30!sn7!rse!sod@2$1?3nch@2$2+jf$0").   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis DFS : ltac2:(zQ "70!sp4!rqe!sq0!sod!t2!sq8!sr0@2$4@4$2@1$1?1s$0@1$5?1d@2$3+h0+hggg0@4$2@1$1?1s$0@1$6?1d@2$3+8+ogg0").
  Hypothesis OK : ltac2:(zQ "60!itf!hjb!hvf!ig6!kt3!mp3@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "d0!p5!ip6!hq7!j7!hjb!hvf!ig6!mke!mtd!nja!nse!sr8!r9@3$2$3@3$7@1$5?1s@1$6?1s?3msF@7$9@hf$8?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$b@1$0#k0+pgtj8?2fc@1$1@1$c@1$0#k0?1m@1$a$4").

  (* [comment removed for export] *)
  Definition malloc_large_gpost : ltac2:(zQ "20!j7!n4>4msF'$0>3mo'$1P") := ltac2:(zQ "jd0!p5!r9!t2!t8!td!v9!hjb!hk4!hoc!hp6!hq0!hq7!hqc!hra!j7!hvf!ig6!ikb!ioe!ip6!ipd!iq4!iqa!itf!n4!ji6!jn4!js3!kh7!kmb!kn5!ks1!ks9!kt3!lha!li5!lj1!lje!loc!lp5!lpd!lq6!lv2!mg0!mke!mp3!mpb!mtd!mu4!mud!mv4!nja!nk0!no4!nse!oh4!olb!on9!oo0!oo6!op0\4msF'$e\3mo'$h8@2$3$4\1a$4@2$3@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$3@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$3@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$3$h1\2m'$h1@2$2@3$i7?5HCEIL^h0?3msz@2$2@2$ja@2$j9^h0?3msz@1$i8?5HCEIL@2$2@3$b$4@2$jb^h0+hgg0Z@2$2@5$id$6@1$f@1?2sx^h0@1$h0@1?2sx^h0@1$i1@1?2sx^h0@2$h7^h2^h1@2$2@3$b$e@3$ic@1$f@1?2sx^h0@1$h0@1?2sx^h0^h2@7$j3@hf$if?2ra?2sp?2gp?2tp^f^e^d?2s0?2s1@1$j8@1?1U^h0^c^b^a^9^8^7^6?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^5^4^3^2?1F@1$j4?2ra?2fc@1$h3@1$1@1$0#k0^1@1$j6$6@2$2@4$i0?5HCEIL@1?2sx^h0@3$d@2$7$4$4@4$a$4$4@1?1U^h0?4size?2LB^1@2$2@2$i3@1?2sx^h0^1@2$2@1$i5^1@2$2@3$i2?5HCEIL@1?2sx^h0^h1@2$2@2$ia?2mo^h1@2$2@3$i6$6?2d'^1@2$2@3$hb?5HCEIL@1?2sx^h0?2d'@2$2@2$i4?2d'^h1@2$2@2$j5$6^1@2$2@4$j1$6^1?2lo@2$c@1$0#k0?2sp@2$2@3$j0@9$hf?2lo?2sp^h0?3msz?2pa?3nch?4nres?2TH?1d?1m^1@2$2@3$j2$6?1m^1@2$2@6$h9?5HCEIL?1s?2LB@2$c@1$0#k0?2sp?1m^1@2$2@7$hd?1s@1?2sx^h0?1d?2lo@2$c@1$0#k0?2sp?1m^1@2$2@4$he?1s@1?2sx^h0?2mo^h1@2$2@2$3@1$5@1$1@1$0#8\4junk@1$5@1$1@1$0#8@4$j7$6^2@1?1U^h1@3$d$h2@2$ie@1$jc?4size^1@1$h5$h2@2$2@3$i9^1@1?1U^h0?4size@2$3$8\4st''$8@2$3@1$5$9\2ev@1$5$9@2$2@3$b@1$h6@2$7@2$7$4$8@1$5$9@3$ib?2st?4size^h2@2$h4@2$7@2$7$4$8@1$5$9@4$a@2$7$4$8@1$5$9@4$a$4$8@1?1U^h2^2^1@2$hc^2@3$ha?2st^h2?4size").

  Theorem malloc_arep_large : ltac2:(zQ "70!itf!hjb!ot3!ph4!j7!n4!pn9>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
  Proof.
    (* LPS revision repair (75d69e00, checker 2c6b6db8).  This proof was a KReplay replay that
       destructured amaps_in_ledger at its PRE-RESTATEMENT shape; its first error was As:90 /
       Bs:91 "Illegal application: and_elimF6" over the old six-conjunct body, whose first
       conjunct this series guards by a non-zero ledger-word size (As//Bs AllocRep.v).  Written
       out as plain text; the STATEMENT IS UNCHANGED (still the encoded one above).  Shape from
       a donor tree:projects/openssl/echconfiglist_parser/proofs/lib/As/
       AG_MallocLarge.v:99-295, the same theorem in a section of the same signature.
       RULE 17: the donor had exactly two tree-specific numbers and neither is carried.  Its
       7430144 is echconfig's AIMG_TOP and is written here as this tree's own aapp floor, the
       same number As//Bs AG_MallocLarge3, AG_CacheDealloc3 and AG_FreeMid BND already carry.
       Its 11571200 is AFS_SIZE unfolded; it is written as AFS_SIZE, which both trees define
       (As//Bs AllocRep.v:78) and which therefore needs no re-keying at all.  Everything else
       in the proof is symbolic or allocator geometry shared by both trees. *)
    intros K.
    pose proof (proj1 HR) as R. pose proof (proj1 R) as OKs. destruct OKs as [PL WFs].
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct (large_cells_of_arep s m R) as (INST64 & NRES & SST & MTX & GST & TST & UNW & PA & PAJ & NB1 & NB2).
    pose proof (senv_of_arep s m R) as SEN. destruct AX as [AWV FXR].   (* [comment removed for export] *)
    pose proof (ienv_of_arep s m R) as IEN. rewrite <- TP in IEN, SEN.
    destruct AMX as [AM AK]. pose proof (ak_hsm_full s mo AK) as HSMF. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB). destruct AIL as (_ & _ & _ & NOV & NW & NWA). destruct AB as [AB0 AB1].
    pose proof (large_req size SZ) as RQ. fold r in RQ. destruct RQ as (RS & RZ & RR & ND & RP & RN & TB & BIG). fold needed in ND, BIG.
    assert (MSZ : needed + 4096 <= msz /\ msz < needed + 8192 /\ msz mod 4096 = 0 /\ size + 8 <= needed - 4088 /\ needed <= size + 4104).
    { unfold msz. rewrite ND. unfold round_up, kPageSize. clear - SZ; try acb. Z.div_mod_to_equations. nia. }
    assert (BND : 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 7430144 <= CTX /\ CTX + 160 <= aceil /\ 7430144 <= pa /\ pa + 8388608 <= aceil /\ pa mod 4096 = 0
            /\ 7430144 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7430144 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
            /\ 4096 <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s /\ aceil <= lo).   (* [comment removed for export] *)
    { pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; clear; lia)) as T2e. pose proof (aapp_env _ _ P2 ltac:(unfold kPtrArrayReserve; clear; lia)) as P2e.
      pose proof (aapp_env _ _ X2 ltac:(clear; lia)) as X2e. pose proof (aapp_env _ _ G10 ltac:(clear; lia)) as G10e. pose proof (aapp_env _ _ G12 ltac:(clear; lia)) as G12e.
      clear - S1 S2 S3 P1 P2e P3 T1 T2e T3 X1 X2e X3 TCX G10e G11 G12e G13 LO; try acb. unfold TH, sb, pa, CTX. unfold a_sb in *.
      acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. repeat split; (first [clear - T2e T1 S2 S3 X2e P2e P1 G10e G12e TCX LO; lia | lia]). }
    (* [comment removed for export] *)
    eapply (malloc_large_sreach (a_L s) (a_S s) (a_Zr s) msF mo Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo size needed msz d ATSD CTX TH (a_top s) (a_bot s) sb pa nres nch CH (map sc_map_beg (as_sec st))).
    { constructor. split; [exact ND| reflexivity]. }
    { exact LO. } { exact HI. } { constructor. exact SPA. } { constructor. exact SPT. } { exact SZ. }
    { constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia. }
    { constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.   (* [comment removed for export] *)
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia]. }
    { constructor. unfold disj, kSpaceSize, kPageSize in *. clear - D2 D3 TCX; try acb. subst TH sb CTX. lia. }
    { constructor. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in *. clear - D4 D5 TCX; try acb. subst TH pa CTX. lia. }
    { constructor. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in *. clear - G1 G2 G3 G4 G5 G6 G10 G12 BND; try acb. subst TH sb CTX.
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
    { constructor. unfold disj, kPtrArrayReserve in *. clear - G7 G8; try acb. subst pa. lia. }
    { constructor. acb. unfold AHI_LO, kSpaceSize. clear - BND; try acb. lia. }
    { constructor. clear - BND; try acb. lia. }
    { all: (clear - G11 G13 BND; try acb; lia). }
    { exact DCAP. }
    { split; [exact P2| split; [exact P3| unfold kPageSize in P1; exact P1]]. }   (* [comment removed for export] *)
    { unfold kChunksBlockCount in NB2. clear - NB1 NB2; try acb. subst nch nres st. lia. }
    { (* this tree's NB2 is `nres mod kChunksBlockCount = 0 /\ bounds`, not the donor's
         two-way disjunction, so the witness is computed rather than case-split *)
      unfold kChunksBlockCount in NB2. clear - NB2; try acb. subst nres st. destruct NB2 as [EM NBd].
      first [ exists (as_n_reserved (a_st s) / 512); clear - EM; Z.div_mod_to_equations; lia
            | apply Z.mod_divide; [clear; lia|]; clear - EM; Z.div_mod_to_equations; lia
            | clear - EM; Z.div_mod_to_equations; lia ]. }
    { unfold nch, zlen. rewrite length_map. reflexivity. }
    { exact FCH. } { exact Ha0. } { exact IEN. } { exact SEN. } { exact MI. } { exact ST. } { exact UNW. }
    { exact INST64. } { exact NRES. } { exact SST. } { exact MTX. } { exact GST. } { exact TST. } { exact PA. } { exact PAJ. } { exact DEP. }
    { exact NW. } { exact NWA. } { exact NOV. }
    { unfold aPhi, lg_cost, page_size in *. clear - AB0 AB1 ALLOW PNN; try acb. subst st. lia. }
    { (* [comment removed for export] *)
      pose proof (ak_atop s mo AK) as AT.
      exact (gap_witness_fit_top _ AHI_LO msz ltac:(clear - MSZ SZ; lia) ltac:(unfold AHI_LO; clear; lia) ltac:(clear; reflexivity)
               ltac:(rewrite AT; hcb; clear - HCEILB; lia) AGP). }
    { exact (ak_imgr s mo AK). } { exact (ak_shland s mo AK). }   (* [comment removed for export] *)
    { exact (ak_atop s mo AK). }
    { exact (ak_zrsh2 s mo AK). } { exact AWV. }   (* [comment removed for export] *)
    { intros x Hx. apply (ak_tmaps s mo AK). unfold kPageSize. exact Hx. }
    { exact (ak_cmaps s mo AK). } { exact (ak_pmaps s mo AK). }
    { intros x Hx. apply (ak_sbmaps s mo AK). unfold kPageSize. clear - Hx; try acb. subst sb. lia. }
    { intros x Hx. apply DCOV. left. exact Hx. } { intros x Hx. apply DCOV. right. exact Hx. }
    { intros E. clear - AK BND NB1 NB2 E; try acb. subst nch nres pa st. unfold kChunksBlockCount, kPtrArrayReserve in *.
      apply (ak_pamc s mo AK); unfold wz, kPtrArrayReserve; rewrite ?unsigned_lit by lia; lia. }
    (* LPS 727298f3: the ptr-array window cannot be bounded below [ARESX_LO] ([ak_resf]'s new
       premise), but it is mapped ([ak_pamc], as in the bullet above), so it misses the ledger by
       [ak_resf_inside]. *)
    { intros E. clear - AK BND NB1 NB2 E; try acb. subst nch nres pa st. unfold kChunksBlockCount, kPtrArrayReserve in *.
      apply (ak_resf_inside s mo AK).
      apply (ak_pamc s mo AK); unfold wz, kPtrArrayReserve; rewrite ?unsigned_lit by lia; lia. }
    { intros E x Hx. clear - AK BND NB1 NB2 Hx E; try acb. subst nch nres pa st. unfold kChunksBlockCount in *. apply (ak_zr_pa s mo AK). unfold kPtrArrayReserve. lia. }
    { exact OK. } { exact VISE. }
    (* [comment removed for export] *)
    cbv beta. intros msF' mo' P.
    destruct P as (a & y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & b1 & rest & m' & AHI & CE & AL & FREE & OK' & VIS' & MO' & MU' & WM' & MI' & ST' & AEN'
                 & UNW' & INST' & NRES' & SST' & MTX' & GST' & PA' & PAJ' & LHDR' & LHJ' & CH' & B1 & MAG' & MAGJ' & FILL' & SLK' & SHA' & SHU' & TST' & DEP').
    fold CHI T nT d' in AEN', CH', DEP'. fold CHI in AEN', CH', DEP'. fold T in AEN', CH', DEP'. fold nT in DEP'. fold d' in DEP'.
    pose proof (aapp_env _ _ AHI ltac:(clear - MSZ SZ; lia)) as [AHI' _]. pose proof CE as CE'. acb.   (* [comment removed for export] *)
    pose proof (aapp_lit _ _ AHI) as ALIT.
    assert (AR3 : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0) by (exact (conj AHI (conj CE AL))).
    (* [comment removed for export] *)
    assert (PNEW : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz TH kPageSize /\ disj a msz CTX 160
                   /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 32768)
                   /\ (forall sc, In sc (as_sec st) -> disj a msz (sc_map_beg sc) (sc_map_size sc))).
    { unfold disj. pose proof (bv_unsigned_in_range _ sp) as SPR.
      assert (FS : 7430144 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil) by (exact (aapp_env _ _ F1 ltac:(unfold AFS_SIZE; clear; lia))).
      unfold kSpaceSize, kPageSize, kPtrArrayReserve, AFS_SIZE in *.
      split; [apply (free_vs_mapped _ _ a msz sb (137438953472 + 4096) FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_sbmaps s mo AK); unfold kSpaceSize, kPageSize; clear - Hx; try acb; subst sb; lia|].
      split; [apply (free_vs_mapped _ _ a msz pa 8388608 FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_pmaps s mo AK); unfold kPtrArrayReserve; clear - Hx; try acb; subst pa; lia|].
      split; [apply (free_vs_mapped _ _ a msz TH 4096 FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_tmaps s mo AK); unfold kPageSize; clear - Hx; try acb; subst TH; lia|].
      split; [apply (free_vs_mapped _ _ a msz CTX 160 FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply (ak_cmaps s mo AK); clear - Hx; try acb; subst CTX; lia|].
      split; [apply (free_vs_mapped _ _ a msz (a_fsb s) AFS_SIZE FREE ltac:(hci; try unfold AFS_SIZE in *; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; try unfold AFS_SIZE in *; lia) ltac:(hci; (first [clear - FS ACEILB; unfold AFS_SIZE in *; lia | unfold AFS_SIZE in *; lia | lia])) ltac:(hci; try unfold AFS_SIZE in *; lia)); intros x Hx; apply (ak_fsmaps s mo AK); unfold AFS_SIZE in *; clear - Hx; try acb; lia|].
      split; [apply (free_vs_mapped _ _ a msz (d_nb d) (16 * 65536) FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply DCOV; left; exact Hx|].
      split; [apply (free_vs_mapped _ _ a msz (d_sb d) (8 * 32768) FREE ltac:(hci; lia) ltac:(hci; (first [clear - MSZ SZ; lia | lia])) ltac:(hci; (first [clear - AR3 ACEILB; lia | lia])) ltac:(hci; lia) ltac:(hci; (first [clear - ACEILB BND; lia | lia])) ltac:(hci; lia)); intros x Hx; apply DCOV; right; exact Hx|].
      intros sc Hin. pose proof (ak_secmaps s mo AK sc Hin) as IN. pose proof (SEC sc Hin) as (Q1 & Q2 & Q3 & Q4 & _).
      acb. apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].
      pose proof (region_free_In _ _ _ _ _ (region_free_app_r _ _ _ _ FREE) IN) as D. unfold wz in D. rewrite !unsigned_lit in D by (clear - AHI' CE' MSZ SZ Q2 Q3 Q4; try acb; lia).
      clear - D; try acb. lia. }
    pose proof (munch_agree _ _ _ MU') as AG'. 
    (* this tree's arheap_after and new_block (As//Bs AG_MallocLarge2.v:63, Section
       ArepAfterLarge) take `nch < 63 * kChunksBlockCount` in this slot -- the glue's own
       NSEC -- not the donor's derived `nch = nres -> nres = 0`, which is not provable
       from this tree's NSEC and NB2 and was the donor's own section hypothesis
       `nch + 1 <= kChunksBlockCount` in disguise. *)
    pose proof NSEC as NSEC'.
    apply K. unfold malloc_large_gpost.
    exists a, y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m'.
    split; [exact AHI|]. split; [exact CE|]. split; [exact AL|]. split; [exact OK'|]. split; [unfold U, kPageSize; replace (a + 4096 + 2048) with (a + 6144) by (clear; lia); exact VIS'|].
    split.
    { (* [comment removed for export] *)
      eapply (arheap_after s m m' a size lo (bv_unsigned sp) d); [exact HR | exact DPL | exact SZ | exact AR3 | exact LO | exact PNEW | exact NSEC' | exact AG' | exact WM' | exact NRES' | exact SST' | exact MTX' | exact GST' | exact PA' | exact PAJ' | exact LHDR' | exact LHJ' | exact CH' | exact B1 | exact MAG' | exact MAGJ' | exact FILL' | exact SLK' | exact SHA' | exact SHU' | exact TST' | exact UNW']. }
    split.
    { (* [comment removed for export] *)
      intros x Hx. cbn [a_S] in Hx. rewrite in_rangesb_cons in Hx. apply orb_true_iff in Hx. destruct Hx as [Hx|Hx].
      - apply (zin_W (sh a) (msz / 8)) in Hx; [| clear - AHI' CE' MSZ SZ; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia | clear - AHI' CE' MSZ SZ; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia | clear - AHI' CE' MSZ SZ; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia].
        assert (SHALL : u8arr asegs m' (sh a) (repeat (b8 250) 512 ++ sec_shadow size msz)).
        { apply (proj2 (u8arr_app2 m' (sh a) _ _)). split; [exact SHA'|]. rewrite repeat_length.
          replace (sh a + Z.of_nat 512) with (sh (a + 4096)) by (clear - AL; try acb; unfold sh; Z.div_mod_to_equations; lia). exact SHU'. }
        destruct SHALL as [_ (W1 & W2 & W3)]. rewrite length_app, repeat_length in W3. unfold sec_shadow in W3. rewrite !length_app, !repeat_length in W3.
        match type of W3 with forall i, 0 <= i < ?n -> _ => assert (LEN : n = msz / 8) end.
        { destruct (Z.eqb_spec (size mod 8) 0) as [E|E]; cbn [length]; unfold round_up; clear - E MSZ SZ; try acb; Z.div_mod_to_equations; lia. }
        rewrite LEN in W3. specialize (W3 (bv_unsigned x - sh a) ltac:(hci; clear - Hx; try acb; lia)). replace (sh a + (bv_unsigned x - sh a)) with (bv_unsigned x) in W3 by (clear; lia).
        unfold wa in W3. rewrite Z_to_bv_bv_unsigned in W3. exact W3.
      - apply WM'. exact (AWV x Hx). }
    assert (SHB : 2148314624 <= sh a) by (clear - AHI'; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    split.
    { (* [comment removed for export] *)
      destruct FXR as (FX1 & FX2 & [gg FX3] & FX4 & [bb FX5]).
      (* [comment removed for export] *)
      pose proof (akobj_lit _ _ T2) as THL. unfold kPageSize in THL.
      split; [(eapply rw_cells_transport; [exact FX1| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1; try acb; subst nch nres st; (first [clear - NB1 BND AHI' SHB ACEILB; lia | lia]))|].
      split; [(eapply rw_cells_transport; [exact FX2| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1; try acb; subst nch nres st; lia)|].
      split; [exists gg; (eapply rw_cells_transport; [exact FX3| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1 THL; try acb; subst nch nres st; lia)|].
      split; [(eapply rw_cells_transport; [exact FX4| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1; try acb; subst nch nres st; lia)| exists bb; (eapply rw_cells_transport; [exact FX5| exact MU'| exact WM'|]; unfold ml_W, depot_W; cbn [disjoint_from cells_size csize length Nat.add]; unfold AINST, AllocRepX.ALIBCPGSZ, AllocRepX.AGOT_SSP, AllocRepX.ASSPGUARD, ACFLAGS; clear - BND AHI' SHB SPR NB1; try acb; subst nch nres st; lia)]. }
    assert (PAR' : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil) by (exact (conj P2 P3)).
    assert (NCH' : 0 <= nch <= nres /\ nres + 16384 <= 2^20) by (unfold kChunksBlockCount in NB2; clear - NB1 NB2; try acb; subst nch nres st; lia).
    pose proof (amodelx_after s mo mo' a size d (conj AM AK) DCOV SZ AR3 FREE (lzok_LM OK) (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK)) ALLOW PAR' NCH' MO') as AMA.
    destruct AMA as [AMX2 DC2].
    split; [exact AMX2|].
    split; [pose proof MO' as M; unfold as_model in M; cbv beta iota zeta in M; exact (proj1 M)|].   (* [comment removed for export] *)
    split; [exact DEP'|].
    split.
    { unfold depot_placed. unfold d'. rewrite !d_nb_put, !d_sb_put. eapply depot_placed_after; try eassumption. }
    split; [intros x Hx; apply DC2; unfold d' in Hx; rewrite !d_nb_put, !d_sb_put in Hx; exact Hx|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact MU'|]. split; [exact WM'|].
    split.
    { (* [comment removed for export] *)
      assert (OKs : ast_ok s) by exact (conj PL WFs).
      assert (HLB : forall b, In b LB -> In b (alb s)) by (intros b Hb; exact (proj1 (proj2 (proj2 HR) b) Hb)).
      assert (SPhi : aceil <= bv_unsigned sp) by (clear - LO HI; try acb; lia).
      pose proof PNEW as PN. destruct PN as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
      assert (BS1 : a + msz <= a_sb s \/ a_sb s + kSpaceSize <= a) by (clear - N1; try acb; unfold disj, kSpaceSize, kPageSize in *; subst sb; lia).
      assert (BS2 : forall sc, In sc (as_sec (a_st s)) -> a + msz <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= a)
        by (intros sc Hsc; pose proof (N8 sc Hsc) as D; clear - D; try acb; unfold disj in D; lia).
      pose proof (bsep_outside s OKs LB HLB a (a + msz) BS1 BS2) as BSEP.
      apply (amframe_of_munch s LB (bv_unsigned sp) _ m m' MU'). unfold ml_W, depot_W.
      destruct (apriv_depot_statics s OKs LB HLB (bv_unsigned sp) SPhi) as [AP1 AP2].
      destruct (apriv_depot_blocks s OKs LB HLB (bv_unsigned sp) (d_nb d) (d_sb d) G10 G12 G3 G4 G9 (proj1 DFS) (proj2 DFS) SPhi) as [AP3 AP4].
      repeat apply Forall_cons; cbn [fst snd]; try apply Forall_nil.
      - apply (apriv_stack s OKs LB HLB); exact LO.
      - apply (apriv_thread s OKs LB HLB); unfold kPageSize; try exact SPhi; clear; subst TH; lia.
      - apply (apriv_app s OKs LB HLB); [exact (arng_of_aapp _ _ AHI)| clear - CE SPhi; try acb; lia| exact BSEP| clear - N5; try acb; unfold disj in N5; lia].
      - replace (msz / 8) with ((a + msz - a) / 8) by (f_equal; clear; lia).
        apply (apriv_shadow s OKs LB HLB); [exact (arng_of_aapp _ _ AHI)| clear - MSZ SZ; try acb; lia| clear - AL; try acb; Z.div_mod_to_equations; lia| exact SPhi| exact BSEP| clear - N5; try acb; unfold disj in N5; lia].
      - apply (apriv_ptrarr s OKs LB HLB); unfold kPtrArrayReserve; try exact SPhi; clear - NCH'; try acb; subst pa; lia.
      - apply (apriv_inst s OKs LB HLB); [clear; lia| clear; lia| exact SPhi].
      - apply (apriv_thread s OKs LB HLB); unfold kPageSize; try exact SPhi; clear; subst TH; lia.
      - exact AP1.
      - exact AP2.
      - exact AP3.
      - exact AP4. }
    split.
    { (* [comment removed for export] *)
      apply (acompl_of_munchF s (sx a) d lo (bv_unsigned sp) _ m m' MU'). unfold ml_W, depot_W.
      assert (NEWSC : In (mkSC a msz needed) (as_sec (a_st (sx a)))).
      { change (as_sec (a_st (sx a))) with (as_sec st ++ [mkSC a msz needed]). apply in_app_iff. right. left. reflexivity. }
      repeat apply Forall_cons; cbn [fst snd]; try apply Forall_nil; intros aa Haa.
      - left. exact Haa.
      - right; left. unfold kPageSize. clear - Haa BND; try acb. subst TH. lia.
      - do 5 right; left. exists (mkSC a msz needed). split; [right; exact NEWSC| left; cbn [sc_map_beg sc_map_size]; exact Haa].
      - do 5 right; left. exists (mkSC a msz needed). split; [right; exact NEWSC| right; cbn [sc_map_beg sc_map_size]; exact Haa].
      - do 4 right; left. unfold kPtrArrayReserve. clear - Haa NCH' BND; try acb. subst pa. lia.
      - do 6 right; left. left. clear - Haa. lia.
      - right; left. unfold kPageSize. clear - Haa BND; try acb. subst TH. lia.
      - do 6 right; left. right; left. clear - Haa. lia.
      - do 6 right; left. right; left. clear - Haa. lia.
      - do 7 right; left. clear - Haa. lia.
      - do 7 right; right. clear - Haa. lia. }
    split.
    { (* [comment removed for export] *)
      pose proof MO' as MOx. unfold as_model in MOx. cbv beta iota zeta in MOx. destruct MOx as (_ & VM2 & _).
      apply (avmx_cons s (sx a) mo mo' a msz needed).
      - clear - AHI'; try acb. lia.
      - clear - MSZ SZ; try acb. lia.
      - clear - CE AHI'; try acb. lia.
      - exact (region_free_app_r _ _ _ _ FREE).
      - intros x Hx. rewrite VM2, in_rangesb_cons, Hx. apply Bool.orb_true_r.
      - intros sc Hin. change (as_sec (a_st (sx a))) with (as_sec st ++ [mkSC a msz needed]) in Hin. apply in_app_iff in Hin.
        destruct Hin as [Hin|[<-|[]]]; [left; exact Hin| right; reflexivity]. }
    split. { eapply new_block; [exact HR | exact DPL | exact SZ | exact AR3 | exact LO | exact NRES' | exact PAJ' | exact FILL' | exact SLK' | exact SHA' | exact SHU']   (* this tree's new_block has no NSEC premise *). }
    split. { eapply new_block; [exact HR | exact DPL | exact SZ | exact AR3 | exact LO | exact NRES' | exact PAJ' | exact FILL' | exact SLK' | exact SHA' | exact SHU']   (* this tree's new_block has no NSEC premise *). }
    (* [comment removed for export] *)
    apply (am_malloc_large st a size SZ); fold r; fold needed; fold msz.
    - unfold kPageSize. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by (clear - AHI'; try acb; lia). exact AL.
    - unfold kHighMemBeg, kHighMemEnd, kLowMemEnd, kShadowOffset. clear - ALIT AHI' CE'; try acb. lia.   (* [comment removed for export] *)
    - destruct PNEW as (N1 & _). unfold disj, kSpaceSize, kPageSize in N1. unfold in_primary. apply andb_false_iff.
      clear - N1 MSZ SZ; try acb. subst sb st. unfold a_sb, kSpaceSize, kPageSize in *. destruct N1 as [N1|N1]; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
    - intros h Hh Hle. destruct PNEW as (_ & _ & _ & _ & _ & _ & _ & N8). pose proof (N8 h Hh) as D. pose proof (SEC h Hh) as (_ & _ & _ & Q4 & _).
      unfold disj, kPageSize in *. clear - Hle D Q4 MSZ SZ; try acb. lia.
    - unfold kMaxNumChunks, kChunksBlockCount in *. clear - NB1 NB2 NSEC; try acb. subst nch. try subst nres. subst st. lia.
  Qed.
End MallocLargeGlue.
