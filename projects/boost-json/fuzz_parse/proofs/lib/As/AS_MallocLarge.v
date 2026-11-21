(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proof terms re-threaded to the revision's definitions, statements written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AsDepotHash AsDepotPut AsUnwind AllocWalkKit F_memset.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AW_Leaves AW_PoisonShadow AW_DepotFrame AW_AllocBase AW_MallocBase AW_LargeAlloc1 AW_SysconfPg
     AW_MallocPre AW_MallocRet AW_AllocPreSec AW_AllocSec1 AW_AllocSec2 SecLazy AS_LargeAlloc AS_AllocSec1 AS_AllocSec AS_MallocLarge1 AllocTacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AS_MallocLarge () := KReplay.lz_vm "#$q1C89OSSVerify6Proofs:boost_json:fuzz_parse3lib2As8AsShadow4aappC13~~~C56Stdlib6ZArith6BinInt1Z3add!t/\5aceil!t0B2leK47Corelib7Numbers7BinNums1Z02!s`<6moduloI!sd+4Init5Logic2eq00!s@83and00C!sA75proj1K!sA19Datatypes4list01I!sFA0K4!t~&9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr01!vv=8positive02K!tAL1!sQ65Tauto8G!sJ'4C!sJ<B!sJ&K!wv;1!sb6:Z!tV+=Z!sn$CheckerC!vf<4find!sqAC!sq0_soun!{LVllocRep8!|U#_env!{O&7!snN>Asan!so$Model@kPtrArrayReserve!sy%I!|-?0!xTG3!|q@!zS7!vL-;!}-%!uB$!|H#!xO:5eKind!|+=uni!|+9!se%4kind!yz8!zM13Op2!uF/!t58!}[>bool!vS/!sF81K4ELinuxProcessSemantics?!s<23Run6config!|~?1N02C45stdpp9bitvector;definitionsDbv_unsigned_in_range!sYA;!sY-!sPA:bv_!#6'#us!yDG1!{r\5akobj!zt&!skR<!sk$WalkKit6hidden00!#:>Bpow!t|S:AsDepotInv4d_nb!t1Cmul!#9Z8or00!tKas!tK'!#<QZ;!#<Q#_facts!#4-U8HeapCeil5h!#=A,!|&;6length!#=#<of_nat!sF34Znat5Nat2Z9is_nonneg!sk<8max_spec!#>p=t!ws>ax!#4P59SatDivModCZ!{p#!tS&!tZ'!sWBdiv!sW2!tM<div!sC<>pow_po!uxD:!sN#!sJ%!#7]?3!#>A=3P!#4t$!x8:3nat!#>9E5Psatz04!sOK2!t?<6option!tB8!#@E12I!#4z?2bv!#CE-5Lists7!s+#Def3map!x<+!sA%4!s+#:!zx%_!sE$!~%68eq_ind_r!#5P\wlist!~+[!#?1/li!snZ9!sn$TacXAregion_side_intro!sxc;!sx-!srkrank!#5Va2sh!w:b?!w:$sh!w=#!~H#!uSc9!uS&lb!spkub!w7kpsep!#827!#Ln,2!vh\9!#>;#!z}]!so3!#Gy+!#<R\8d_frames!wSex_unh!{d,!#I]]8round_up!tcc:!xF&fam!sqY=AW_Ma!su#Base:icpt_chain!}M\Unwind6utrac!#3/Y?AS!tc&Large1Fm!s3$_l!s4#_head_po!#6jW3Lib5F!x~#3mkR!{p'!#9d>7Z_to_bv!t5T8PropExec7seg_rom!t}Z6MState2MS!sg%K!vkR!#G|71!w_iA!w_4!|&V<LazyRestrictEsame_but_materialize!s|W6!s|#SR8hid_!sz#!tgc8r!s/&!so%I!#@vB0!xWT4!~/#2wz!t/B4prod!t,V!{]%5munch!zIZ3Mem7mem_i!#7?&!#OITW_A!#3t&4AENV!#OG'!uf13Nat3subI!#Cn96Forall!#`q4Peano2le!#NWT!tj06a!#9+#!}%V!w2$Cells4cell!|y'!sj`5!wwZ!yi%b8!tQf4!tQ&!#Lg;sub!#O^=7inj_iff!#?]77iff_symK!#Sk:1!#;h\!#A0&hul!#R<%!t4<2!|bZ=disjoint_f!#85X2As>AW_!#6R#!u/$1>senv_transport!|{Y!sz24S!|}/!#5_[:!#]2&!#Wa'!#^hI>Riscv!sE+5wview!x~83not!#Nd8!y?#refl!#T_5;ZifyClasses3injC!{TY:!{T#s_siz!~['!#RYI7!#R7D7!#6pTArr@u64arr!x|3!zkZFstk!sq,_!zy'!x9'!vu@9and_morph!sOB7rew!~L$!zpR;!#I-%Hash:d!s0#_ha!#OGZ!#I{,7d_putid!#4rA7di!#dU#!sG<=mo!#EQ#_b!#mG#!sM@neg!sM25!vF$8PreO!s/#1Z;!t>#0_r_ext!sL>!st#!sL&!#4j7!#u##1!#E/Z<!#hC'!#Nv+4!#7n2div?!#^v$plus_full!}W86!#Y=$!tZT2Nd:!ys#elimF8!x^d5d_ids!#4MP5!v+$8m_vmmaps!s]Q7vm_!s\$!#6UN:LazyLedger>entries_nowrap!#7JbL!#Gl7!uP'!v5V;vm_noac!s;#!uZ[9nooverl!uUe:eager_use!#K6c;pages_total!yFXvm_limit!tQ]K!ws9!uZ$!taW9!#NR$top!xRUr!#yl$d!#lp;3app!$&N9x00!t?Q<map_contains!#H|TS!#H|$Sec1A!ui%sec_sr!#Ur-!#F+;eqb!t{Q=!|I#_subtract!$+QA2!#73Z6ret_pc!#5WX!v108as_model!srf4as_W!sn%!#Jb_3!sjf2!uF[!#OC,5b1_o!#hG&!#Po:repeat!t6\Sec2:!zO$!#hu#!#:qfput!smd7!#B4$W!soV!ze-;!ze%_even!ve3!#>L1sym!t4T9LiaTuning9zify_don!#b$Y7SecLazy>free_vs_mapp!#9+&c!ssR>!#^<04ml!vf+!ut79False!#AE#!#RS7and!#AbW!#I>$7out!#qAY!sk,6sub_fp!sj`<!#\@#_weak!x{'!#Lx5!$2l:3!x@S!#U0+=rx_not_in_s!#p0W!u:,;!u:%!#M,#!soawmono!so\!#3G%!y{%Ret?!#e6%!|}$o!#yTZ!sy0:!sy,!|aa:nonvm!#e2-!#>;Pvm_mmap_base!saQ6vm_brk!t>Ustart!sa#!#=U<!#e3#1!#3m[!v2,_ma!w#b@!ss-!yg`!#=`,<!#>T&!tmZ!#Nj%;ex!$#;$F1!#Nk&!#kbUBevt_sreach_lazy_!ta`!#PM'31!sl]:ex!sk%17!w4Y;!w4-@!#El-!u\#!uTg15!uTg!sk_!w/,!sk%I!xiPSR!v$#6!v/%!#bl&!#_JJ6!#9PM2!$M]?!sDA3!$KoE!sJG5!sJF8!#anD5!sIE3I!}7V4lzok!#g8'!#;8X5!#;8#!si`3stk!sgZ4Step8rw_!#f4#!}iY!#H3-DEPOT!sm&!#ci@6mkapp2!sLB5mkrel!sKEapp!sKB;!#e%%_rev!w-ZB!vF'!#gq2!}5K5!tGT3Arr6!#i6$!t9<!{024!|BF7!#X$Q!$/L&ree!u9X5u8!u8?!tm36!zAS5ASegs5aseg!$HSV4Scfg=hunspell_scfg!tz<!#6,:!$S>I!sMJ5I!#rsX=machine_s!w~#!#}t3!$EV10I!{oT!#VH,!$P$25!v+$8!$###Na!$#h'!#zs=;inj_sub_max!#^S74True!$V&3!sB/1!t,>6!t,#leI!#GCPVmMaps!$%5T!$E_+AINS!#5[%!tJQ5!$:;#!tIU!{e%8AIMG_TOP!#7mX!$CX'6AHI_LO!|VV!$<T1:kSpaceS!#xY,!zL?!$$3]=!#4O%tabl!#iJ'!|w58ZifyInst7Inj_Z_Z!z385!#Vv#!#ecR9page!#{=$!x+X7!x+$!w=+!x'[9ALOWSH!soe3me!$&iY!#aa/>k!s1%egMagic!tc[!|i&9AGOT_VAL!$<z%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~k15depot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~o93ivl35stdpp9bitvectorbdefinitionssb2bv46Stdlib6ZArith6BinInt1Zud3addhc4conshc4pairhc4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~hi05AINST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~hm72shud3mulk17depot_Wud3divsbbbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem5Statehsf5Model3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsig6dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeike5bvmaphm73mem37Corelib4Init5Logicio43and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ipf4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~iu35asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ji72wzio42exipf2C8hc3nilo93stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jo08rw_cellshc4boolji72b8io42eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jta5u8arripf2C1hc3app37Corelib5Lists7ListDefki96repeathsf8m_vmmaps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsDepotHash~~~~~~kl6adepot_hashhc4Nonehc6lengthhc4true3h5LinuxProcessSemanticsfLinuxProcessSem3Runkrc5mkCfghsfdmaps_subtracthsfbregion_freehsf7vm_mapshsfbvm_reserved79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAS_AllocSec1~~~~~~lib8as_model89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAS_MallocLarge3HCW~~~~~~ln94ml_W79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAW_AllocBase~~~~~~ls94AENVls95b1_okls9ekAllocBegMagic79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAW_AllocSec2~~~~~~mieasec_shadowhi05wlistk15DEPOTk15d_putk17d_putidhm74aapphm75aceil69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~mr28restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~mvd4lzokjta6u64arripf2C2ipf2C4o93mkRo95muncho95wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~nma2MSnma6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~nr77mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~nvc7seg_romud3eqbud2leud6moduloud6of_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~om38round_up79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAllocWalkKit~~~~~~or06hiddenud3maxud3powud2ltiu38AIMG_TOPhi05akobjio42orom3akSpaceSizeom3h0kPtrArrayReservek14d_nbk14d_sbhm76AHI_LOk18d_framesk15d_idsom34zlen79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsUnwind~~~~~~pne9goodframepnebframe_chain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAW_MallocBase~~~~~~pt84IENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAW_LargeAlloc1~~~~~~qi34SENV69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~qmfeentries_nowraphsfbvm_noaccessqmf9nooverlaphsf9page_sizehsf8vm_limitmr2aeager_usedmr2bpages_totalhsf9alloc_topiu37AIMG_LOmr2ain_rangesbhm79ALOWSH_LO69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~rk35hceilhc6optionio43notig65wviewhsfcmap_containshc5falsesb7Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition ml_W : ltac2:(zQ "60!h9!j4!jb!o1!s5!u8>2lo$0>2sp@1$5@1$2#k0>1a$0>3msz$0>2pa$0>3nch$0>4nres$0>2TH$0>1d$3@1$1$4") := ltac2:(zQ "e0!h9!hg5!hgb!hh2!hh9!jb!hle!hq5!hqb!o1!hr1!hrb!u8!hs1\2lo$0\2sp@1$c@1$5#k0\1a$0\3msz$0\2pa$0\3nch$0\4nres$0\2TH$0\1d$9@3$2@2$4$0$0@4$3$0$0^9@2$d@1$5#k0^8@3$2@2$4$0$0@4$3$0$0@2$1^2+sm0@2$1^2+sm1@3$2@2$4$0$0@4$3$0$0^7@2$1^7^6@3$2@2$4$0$0@4$3$0$0@1$7^7@2$1@1$7^7@2$b^6+8@3$2@2$4$0$0@4$3$0$0@2$1^5@2$8+8^4@2$1^5@2$8+8@2$1^3+kgg0@3$2@2$4$0$0@4$3$0$0@2$1$6+n0@2$1$6+it8@3$2@2$4$0$0@4$3$0$0@2$1^2+qv0@2$1^2+sm0@1$a^1").

(* [comment removed for export] *)
Definition malloc_large_post : ltac2:(zQ "a2!jb!u8!h9!j4!hh9!hvd!ijd!in4!o1!ind&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>1L~1>1S~1>2Zr~1>2mo$5>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$9>2lo$2>4size$2>6needed$2>3msz$2>3TSD$2>3CTX$2>2TH$2>2sb$2>2pa$2>4nres$2>3nch$2>6chunks@1$3$2>1T@1$3$2>1d$8>4msF'$6>3mo'$5P") := ltac2:(zQ "k83!jb!u8!hg5!ip8!itb!h9!jhe!hgb!jm2!jm8!jme!j4!hh9!jn4!jna!hle!jrb!js7!jse!hqb!jt4!ind!hq5!kh4!khd!ki3!kk0!ijd!hvd!kka!kp7!hs1!kq5!kqc!hh2!kr5!ku8!kv1!lg2!lh1!lhc!in4!lmd!ls1!mgb!mh3!mhc!mn0!mne!mo7!mof!mp7!o1!mq1!mq9!mv1!nj6!nje!nk8!nke!nl4!nla!nm2!nq7!nqd!nv1!ojb!hrb!ok6!okc!ol1!ola&@2$c@1$1@1$0#k0@1$1@1$0#k0&@1$b~0&@3$7~0^1^jc\1L~1\1S~1\2Zr~1\2mo$hc\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$i9@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$h5\2lo$5\4size$5\6needed$5\3msz$5\3TSD$5\3CTX$5\2TH$5\2sb$5\2pa$5\4nres$5\3nch$5\6chunks@1$b$5\1T@1$b$5\1d$j4\4msF'$hb\3mo'$hc@2$9$5\1a$5@2$9@1$1@1$0#k0\2t0@1$1@1$0#k0@2$9@1$1@1$0#k0\2t1@1$1@1$0#k0@2$9@1$1@1$0#k0\2t2@1$1@1$0#k0@2$9@1$1@1$0#k0\2a1@1$1@1$0#k0@2$9@1$1@1$0#k0\2a2@1$1@1$0#k0@2$9@1$1@1$0#k0\2a3@1$1@1$0#k0@2$9@1$1@1$0#k0\2a4@1$1@1$0#k0@2$9@1$1@1$0#k0\2a5@1$1@1$0#k0@2$9@1$1@1$0#k0\2a6@1$1@1$0#k0@2$9@1$1@1$0#k0\2a7@1$1@1$0#k0@2$9@1$1@1$0#k0\2t3@1$1@1$0#k0@2$9@1$1@1$0#k0\2t4@1$1@1$0#k0@2$9@1$1@1$0#k0\2t5@1$1@1$0#k0@2$9@1$1@1$0#k0\2t6@1$1@1$0#k0@2$9$5\2b1$5@2$9@1$b@1$1@1$0#k0\4rest@1$b@1$1@1$0#k0@2$9$h5\2m'$h5=9committed$h1@2$k4^h8^h9=5nres'$5Mh1\9committed$h1$5^1@2$2^ha+kgg0^ha=2L'~1Mh1\9committed$h1~1^2@3$i5^jb@2$2^hc@2$h3+8^hb@2$2@2$2^hc@2$h3+8^hb+iggg0^jb=1W~0@4$i2@1$1@1$0#k0@1$1@1$0#k0@1$8@1$h6^h5@1$8@2$k3^i2+8@2$3@3$j5?5HCEIL^h6^i3@2$3@2$k5@2$2^h6^i3@1$j6?5HCEIL@2$3@3$h4$5@2$k6^h6+hgg0Z@2$3@3$h4$h1@3$i6@3$h9~0@1$i8@1$hd^ja@1$i7@1$hd^ja@1$8^h6@1$8^i3$i3@2$3@5$j8$6^2~2^jb@2$i4^h8^h7@2$3@3$h4$hb@3$j7^2~2^h8@7$jf@hf$jc^j9^j8^j7^j6^h5^h4^h3^j5^j4@1$8@2$2^h6+hog0^h2^h1^h0^f^e^d^c^j3^j2^j1^j0^if^ie^id^ic^ib^ia^b^a^9^8^i9@1$k0^j9^i8@1$i0@1$1@1$0#k0^5@1$k2$6@2$3@7$ia^ja^h6^i3^he^hd^4^h7@2$3@3$jd@9$ib^i6^j8^h6^i3^he^hc^hd^i0^h9^i7^5@2$3@3$je$6^i7^5@2$3@2$k1$6^5@2$3@4$e$6^5^i6@2$hf@1$0#k0^j8@2$3@9$ic^j6^i2^i1^i0^hf@2$2@2$hf@1$0#k0^j8-ol0^ha^6^5@2$3@4$h0$6^5@2$2^i0+sm0@3$7$4@1$h8@1$h2Z@1$d$4@2$3@4$h0$6^5@2$2$f+k0@3$7$4@1$a@1$8+hgg0@3$7$4@1$a@1$8^he@3$7$4@1$a@1$8^he@1$d$4@2$3@4$h0$6^5@2$2$f+n0@3$7$4@1$a@1$8^3@3$7$4@1$a@1$8@2$2^hc+1@3$7$4@1$a@1$8Z@1$d$4@2$3@4$e$6^5@2$2$f+o8@2$2$f+iq8@2$3@4$h0$6^5@2$2$f+iq8@3$7$4@1$a@1$8Z@1$d$4@2$3@4$e$6^5@2$2$f+ir0@2$2$f+it8@2$3@4$j9$6^5^he@1$j0@3$h9$5^hb@3$7$5^h6@1$d$5@2$3@4$e$6^5@2$2^he@2$h3+8@2$2^hc+1@2$2^he@2$h3+8^3@2$3@4$h0$6^5^h6@3$7$4@1$a@1$8^h6@3$7$4@1$a@1$8^i3@3$7$4@1$a@1$8^i4@3$7$4@1$a@1$8^hc@1$d$4@2$3@4$e$6^5@2$2^h6+i0@2$2^h6+hgg0@2$3@4$h0$6^5@2$2^h6+hnv0@3$7$4@1$h8@1$h2+2@3$7$4@1$h8@1$h2^7@3$7$4@1$ja@1$8Z@3$7$4@1$jb@1$8^i5@3$7$4@1$a@1$8@2$j3^h9@1$he^ha@1$d$4@2$3@1$id^7@2$3@4$h0$6^5@2$2^h6+hgg0@3$7$4@1$a@1$8$ie@3$7$4@1$a@1$8@2$2^h6+hnv0@1$d$4@2$3@4$e$6^5@2$2^h6+hgh0@2$2^h6+hnv0@2$3@4$h7$6^5@2$2^h6+hog0@3$ha@1$1@1$0#8@1$h2+reNhgg0@2$3@4$e$6^5@2$2@2$2^h6+hog0+hgg0@2$2^h6^i3@2$3@4$h7$6^5@1$h6^h6@3$ha@1$1@1$0#8@1$h2+vaNig0@2$3@4$h7$6^5@1$h6@2$2^h6+hgg0@2$if^i5^i3@2$3@4$e$6^5@2$2^i0+qv0@2$2^i0+sm0@3$j1$6@3$j2^h9@1$he^ha@1$k7@2$i1$5^ha^5").

End HCW.


(* [comment removed for export] *)
Ltac region_retable :=
  repeat match goal with
         | H : region_tabled |- _ => clear H | H : region_psep _ _ _ |- _ => clear H | H : region_fam _ _ |- _ => clear H
         | H : region_rank _ _ |- _ => clear H | H : region_lb _ _ |- _ => clear H | H : region_ub _ _ |- _ => clear H end;
  region_table.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Section MallocLarge.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size needed msz : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT sb pa nres nch : Z) (CH : list (Z * Z)) (chunks : list Z).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0x90e00 (bv_unsigned sp) TOP BOT 30 CHI.
  Hypothesis DEFS : ltac2:(zQ "70!jt4!h9!oq4!hg5!ip8!ov2!ovc@1$5@2$4@3$0$1?6needed@2$3@2$2@2$6?4size+8+8+hgg0@3$0$1?3msz@2$3@2$2?6needed+hgg0+hgg0").
  (* [comment removed for export] *)
  Hypothesis LO : ltac2:(zQ "20!mq9!okc@2$1@1$0?5HCEIL?2lo").  Hypothesis HI : ltac2:(zQ "40!jb!hg5!okc!hs1@2$2@2$1?2lo+rm0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "60!jt4!jb!h9!ov2!ol1!hs1@1$3@3$0$2@2$4@2$5@1$1#k0?2sp+h0Z").
  Hypothesis SPT : ltac2:(zQ "60!jb!ov2!hg5!okc!pg2!hs1@1$1@2$3@2$2@2$5@1$0#k0?2sp+h0@2$4+2+if").
  Hypothesis SZ : ltac2:(zQ "30!pg8!ip8!pg2@2$1@2$0+vsg0?4size@2$0?4size@2$2+2+i0").
  Hypothesis TPR : ltac2:(zQ "70!jb!okc!hs1!ip8!pgd!ov2!hg5@1$5@2$3@2$1+mqiho8@2$2@1$0#k0?2tp@2$1@2$6@2$2@1$0#k0?2tp+hgg0$4").
  Hypothesis RNG : ltac2:(zQ "b0!ip8!okc!hg5!mq9!jt4!h9!pgd!ph9!ov2!mq1!ol1@1$8@2$0@2$1+mqihj0?3TSD@2$0@2$1@2$2?3TSD+8$6@2$0@3$9?5HCEIL?3CTX+q0@2$0@2$1@2$2?3CTX+q0@1$3?5HCEIL@2$0@3$7?5HCEIL?2TH+hgg0@2$0@2$1@2$2?2TH+hgg0@1$3?5HCEIL@3$4$5@2$a?2TH+h0Z").
  Hypothesis PLC : ltac2:(zQ "60!hg5!okc!pi2!ip8!pi8!ov2@1$5@2$3@2$2@2$1@2$0?2TH+hgg0?2sb@2$1@2$0@2$0?2sb$4+hgg0?2TH@2$3@2$2@2$1@2$0?3CTX+q0?2sb@2$1@2$0@2$0?2sb$4+hgg0?3CTX@2$2@2$1@2$0?3CTX+q0?2TH@2$1@2$0?2TH+hgg0?3CTX").
  Hypothesis PLC0 : ltac2:(zQ "60!hg5!okc!pi2!ip8!pj6!ov2@1$5@2$3@2$2@2$1@2$0?3CTX+q0?2TH@2$1@2$0?2TH+hgg0?3CTX@2$3@2$2@2$1@2$0?2pa$4?2TH@2$1@2$0?2TH+hgg0?2pa@2$2@2$1@2$0?2pa$4?3CTX@2$1@2$0?3CTX+q0?2pa").
  Hypothesis PLCD : ltac2:(zQ "a1!hg5!okc!hqb!ip8!pkb!pl2!pi2!mq1!pi8!ov2&@2$0@1$4?1d@2$2+h0+hggg0@1$9@2$3@2$6@2$1@2$0?2TH+hgg0@1$4?1d@2$1~0?2TH@2$3@2$6@2$1@2$0?2TH+hgg0@1$5?1d@2$1@2$0@1$5?1d@2$2+8+ogg0?2TH@2$3@2$6@2$1@2$0@2$0?2sb$8+hgg0@1$4?1d@2$1~0?2sb@2$3@2$6@2$1@2$0@2$0?2sb$8+hgg0@1$5?1d@2$1@2$0@1$5?1d@2$2+8+ogg0?2sb@2$3@2$6@2$1@2$0?3CTX+q0@1$4?1d@2$1~0?3CTX@2$3@2$6@2$1@2$0?3CTX+q0@1$5?1d@2$1@2$0@1$5?1d@2$2+8+ogg0?3CTX@2$3@3$7?5HCEIL@1$4?1d@2$2+h0+hggg0@3$7?5HCEIL@1$5?1d@2$2+8+ogg0").
  Hypothesis PLCDP : ltac2:(zQ "90!hg5!okc!pi2!pkb!pl2!pj6!hqb!ip8!ov2@1$8@2$7@2$2@2$1@2$0?2pa$5@1$3?1d@2$1@2$0@1$3?1d@2$6+h0+hggg0?2pa@2$2@2$1@2$0?2pa$5@1$4?1d@2$1@2$0@1$4?1d@2$6+8+ogg0?2pa").
  Hypothesis SBR : ltac2:(zQ "70!okc!ip8!ov2!pl9!mq9!pi8!hg5@1$2@2$1@2$0$3?2sb@2$0@2$6?2sb$5@1$4?5HCEIL").
  Hypothesis TBR : ltac2:(zQ "50!ip8!okc!ov2!pg8!pg2@1$2@2$0@2$0@2$1+hgg0?3TOP@2$1?3TOP@2$4+2+if@2$0@2$1Z?3BOT@2$3?3BOT?3TOP").
  Hypothesis DLO : ltac2:(zQ "60!hg5!okc!hqb!ip8!pkb!pl2@2$3@2$1@2$0@1$4?1d@2$2+h0+hggg0?2lo@2$1@2$0@1$5?1d@2$2+8+ogg0?2lo").
  Hypothesis DCAP : ltac2:(zQ "60!hg5!ip8!pm3!pme!okc!pg8@2$1@2$5@2$0@1$3?1d+1+hggg0@2$4@2$0@1$2?1d+hf+ogg0").
  Hypothesis PAR : ltac2:(zQ "90!ip8!pj6!jt4!h9!mq1!mq9!hg5!okc!ol1@2$0@3$4?5HCEIL?2pa$1@2$0@2$7@2$6?2pa$1@1$5?5HCEIL@3$2$3@2$8?2pa+hgg0Z").
  Hypothesis NCH : ltac2:(zQ "40!okc!ip8!hg5!pg2@2$1@2$1@2$0Z?3nch@2$0?3nch?4nres@2$0@2$2?4nres+kgg0@2$3+2+h4"). Hypothesis NRQ : ltac2:(zQ "40!h9!jt4!jm8!hqb@2$2$0\1q$0@3$1$0?4nres@2$3+ig0^1").
  Hypothesis LEN : ltac2:(zQ "30!h9!jt4!pn6@3$1$0@2$2$0?6chunks?3nch").
  Hypothesis FCH : ltac2:(zQ "b0!jb!hs1!js7!kr5!jt4!prc!ip8!jhe!ps9!hg5!okc>0@3$4$2@3$5?3BOT@2$1@1$0#k0?2sp?3TOP$3>0@3$4$2@3$5@2$1@1$0#k0?2sp@2$1@1$0#k0?2s0?3TOP$3@2$6@2$a@2$9@2$1@1$0#k0?2sp+h0@2$1@1$0#k0?2s0@5$8$7?1m?3TOP@2$1@1$0#k0?2s0?2CH").
  Hypothesis Ha0 : ltac2:(zQ "40!jt4!jb!jm2!u8@3$0@1$3@1$1#k0?2a0@1$2?4size").
  (* [comment removed for export] *)
  Hypothesis IEN : ltac2:(zQ "10!qhb@8$0?2tp?3TSD?3CTX?2TH?2sb?3TOP?3BOT?1m").
  Hypothesis SEN : ltac2:(zQ "10!qm7@5$0?2tp?3TSD?3CTX?2TH?1m").
  Hypothesis MI : ltac2:(zQ "20!jhe!nv1@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!jb!jhe!jna!hs1@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis UNW : ltac2:(zQ "80!itb!hgb!jn4!jhe!khd!jrb!jse!hg5@4$5$3?1m@2$7?2TH+sm0@3$1$0@1$4@1$6Z@1$2$0").
  Hypothesis INST64 : ltac2:(zQ "90!itb!hgb!jme!jm2!jn4!jhe!hle!jrb!hg5@4$7$5?1m@2$8$6+k0@3$1$0@1$2@1$3+hgg0@3$1$0@1$2@1$3?2pa@3$1$0@1$2@1$3?2pa@1$4$0").
  Hypothesis NRES : ltac2:(zQ "90!itb!hgb!jme!jm2!jn4!jhe!hle!jrb!hg5@4$7$5?1m@2$8$6+n0@3$1$0@1$2@1$3?4nres@3$1$0@1$2@1$3?3nch@3$1$0@1$2@1$3Z@1$4$0").
  Hypothesis SST : ltac2:(zQ "40!hle!hg5!jhe!jna@4$3$2?1m@2$1$0+o8@2$1$0+iq8").
  Hypothesis MTX : ltac2:(zQ "90!itb!hgb!jn4!jhe!hle!jme!jrb!jm2!hg5@4$6$3?1m@2$8$4+iq8@3$1$0@1$5@1$7Z@1$2$0").
  Hypothesis GST : ltac2:(zQ "40!hle!hg5!jhe!jna@4$3$2?1m@2$1$0+ir0@2$1$0+it8").
  Hypothesis TST : ltac2:(zQ "30!hg5!jhe!jna@4$2$1?1m@2$0?2TH+qv0@2$0?2TH+sm0").
  Hypothesis PA : ltac2:(zQ "30!jhe!mne!nje@4$2$0?1m?2pa@1$1?6chunks").
  Hypothesis PAJ : ltac2:(zQ "40!hg5!hqb!jhe!jna@4$3$2?1m@2$0?2pa@2$1+8?3nch@2$0?2pa@2$1+8?4nres").
  Hypothesis DEP : ltac2:(zQ "20!jhe!mo7@3$1$0?1d?1m").
  (* [comment removed for export] *)
  Hypothesis NW : ltac2:(zQ "30!kka!lh1!qqc@1$2@1$1@1$0?2mo"). Hypothesis NWA : ltac2:(zQ "30!kka!qre!qqc@1$2@1$1@1$0?2mo").
  Hypothesis NOV : ltac2:(zQ "30!kka!lh1!qsd@1$2@1$1@1$0?2mo").
  Hypothesis BUD : ltac2:(zQ "90!hg5!qta!hqb!kka!qu7!qv3!rg1!hrb!okc@2$8@2$0@2$0@2$0@2$0@1$5?2mo@2$2@1$6?1S$1?3msz@2$2@2$0@2$7?3msz+ogg0+2$1+iggg0@1$4@1$3?2mo").
  (* LPS revision repair (75d69e00, checker 2c6b6db8).  GAP written out as explicit text (rule 11,
     never re-encoded), with one conjunct added for the placement window the revision introduced
     in Bs/SecLazy.v's sr_mmap_kernel_MS and LazyNodes.v:503-505's sreach_mmap_kernel_lazy
     ("Linux places only in [page_size, mmap_top) or [task_unmapped_base, alloc_top)").
     alloc_sec_sreach, which this file applies, demands that window as its 98th argument, and g
     is GAP's own witness, so it must come from above.  It is written here as the WITNESS LOWER
     BOUND `AHI_LO <= bv_unsigned g`, not as the window disjunction itself, because that is the
     fact the producer already proves: As/SecGap.v's gap_witness_fit_top hands its caller
     `B <= bv_unsigned g` out of gap_witness_fit, and this tree instantiates B := AHI_LO =
     17594333495296, which is above task_unmapped_base = 183251939328.  The proof below turns it
     into alloc_sec_sreach's disjunction by lia.  Stating it this way keeps the frozen
     As/AG_MallocLarge.v proof applicable unchanged.
     FAITHFULNESS CONTROL (rule 22c): `About GAP` on the encoded original here, printed by
     a farm round (image 2c6b6db8), reads this text minus the last
     conjunct, character for character, and identically on both sides. *)
  Hypothesis GAP : exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + msz <= alloc_top (m_vmmaps mo)
                                    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g (wz msz) = true
                                    /\ AHI_LO <= bv_unsigned g.
  (* [comment removed for export] *)
  Hypothesis IMGR : ltac2:(zQ "e0!jb!hs1!js7!kr5!ip8!jt4!kka!lhc!rhd!pgd!ri8!okc!pg8!u8>1x@1$d@1$0#k0>0@2$4@2$b$8@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1$9@3$5$2@2$a^2@1$7@1$6?2mo$3").
  Hypothesis SHLAND : ltac2:(zQ "e0!jb!hs1!js7!kr5!ip8!jt4!kka!lh1!pl9!rj6!ri8!okc!pg8!u8>1x@1$d@1$0#k0>0@2$4@2$b$9@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1$8@3$5$2@2$a^2@1$7@1$6?2mo$3").
  (* [comment removed for export] *)
  Hypothesis ATOP : ltac2:(zQ "50!jt4!h9!rh0!kka!rne@3$0$1@1$2@1$3?2mo@1$4?5HCEIL").
  Hypothesis ZRSH : ltac2:(zQ "h00!jb!hq5!hs1!ip8!okc!pg8!js7!kr5!jt4!pi2!pgd!pl9!rj6!mq9!ri8!u8>1x@1$f@1$0#k0>0@2$9@2$3@2$4@1$1$b@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1@1$d?5HCEIL@2$3@2$4@1$1$a@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1$c@3$8$6@2$e^2?2Zr$7").   (* [comment removed for export] *)
  Hypothesis HSRF : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_reserved (m_vmmaps mo)) a n = true.
  Hypothesis HSMC : forall a n : word, 0 < bv_unsigned n -> (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      map_contains (vm_maps (m_vmmaps mo)) a n = true.
  Hypothesis SVIS : ltac2:(zQ "b0!jb!u8!jt4!kq5!js7!ro7!kr5!rp0!rp7!jhe!ri8>1x@1$1@1$0#k0>0@3$2$4@2$a^1?1S$6@1$7@3$2@1$5@1$1@1$0#8@3$8$9?1m^2@1$3@1$1@1$0#8").
  Hypothesis TMAPS : ltac2:(zQ "d0!jb!hs1!js7!kr5!ip8!jt4!kka!lh1!ri8!hg5!okc!pg8!u8>1x@1$c@1$0#k0>0@2$4@2$a?2TH@2$1@1$0#k0^1@2$b@2$1@1$0#k0^1@2$9?2TH+hgg0@3$5$2@2$8^2@1$7@1$6?2mo$3").
  Hypothesis CMAPS : ltac2:(zQ "d0!jb!hs1!js7!kr5!ip8!jt4!kka!lh1!ri8!hg5!okc!pg8!u8>1x@1$c@1$0#k0>0@2$4@2$a?3CTX@2$1@1$0#k0^1@2$b@2$1@1$0#k0^1@2$9?3CTX+q0@3$5$2@2$8^2@1$7@1$6?2mo$3").
  Hypothesis PMAPS : ltac2:(zQ "e0!jb!hs1!js7!kr5!ip8!jt4!kka!lh1!pj6!ri8!hg5!okc!pg8!u8>1x@1$d@1$0#k0>0@2$4@2$b?2pa@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1@2$a?2pa$8@3$5$2@2$9^2@1$7@1$6?2mo$3").
  Hypothesis SBMAPS : ltac2:(zQ "e0!jb!hs1!js7!kr5!ip8!jt4!kka!lh1!pi8!ri8!hg5!okc!pg8!u8>1x@1$d@1$0#k0>0@2$4@2$b?2sb@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1@2$a?2sb$8@3$5$2@2$9^2@1$7@1$6?2mo$3").
  Hypothesis DNMAPS : ltac2:(zQ "f0!jb!pkb!hs1!js7!kr5!ip8!jt4!kka!lh1!ri8!hg5!okc!pg8!hqb!u8>1x@1$e@1$0#k0>0@2$5@2$b@1$1?1d@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@2$a@1$1?1d@2$d+h0+hggg0@3$6$3@2$9^2@1$8@1$7?2mo$4").
  Hypothesis DSMAPS : ltac2:(zQ "f0!jb!pl2!hs1!js7!kr5!ip8!jt4!kka!lh1!ri8!hg5!okc!pg8!hqb!u8>1x@1$e@1$0#k0>0@2$5@2$b@1$1?1d@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@2$a@1$1?1d@2$d+8+ogg0@3$6$3@2$9^2@1$8@1$7?2mo$4").
  Hypothesis PAMC : ltac2:(zQ "a0!jt4!jm2!js7!kr5!h9!kka!rq0!lh1!hg5!hqb>0@3$0$4?3nch?4nres@3$0$2@3$6@1$7@1$5?2mo@1$1@2$8?2pa@2$9+8?4nres@1$1+iggg0$3").
  Hypothesis PARF : ltac2:(zQ "a0!jt4!jm2!js7!kr5!h9!kka!lg2!lhc!hg5!hqb>0@3$0$4?3nch?4nres@3$0$2@3$6@1$7@1$5?2mo@1$1@2$8?2pa@2$9+8?4nres@1$1+iggg0$3").
  Hypothesis PAZR : ltac2:(zQ "d0!jb!hg5!jt4!hqb!hs1!js7!rr0!ip8!h9!ri8!okc!pg8!u8>0@3$2$8?3nch?4nres>1x@1$c@1$0#k0>0@2$7@2$a@2$1?2pa@2$3+8?4nres@2$4@1$0#k0^1@2$b@2$4@1$0#k0^1@2$1@2$1?2pa@2$3+8?4nres+iggg0@3$2$5@2$9^2?2Zr$6").
  Hypothesis OK : ltac2:(zQ "30!ku8!jhe!nj6@5$2$1?1L?1S?2Zr@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "b0!jb!kq5!jt4!ijd!jhe!mv1!nl4!nq7!ojb!rr8!u8@3$2$3@3$5?1L?1S?3msF@7$7@hf$6?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$9@1$0#k0+pgtj8?2fc@1$1@1$a@1$0#k0?1m@1$8$4").

  Let PAE : 7430144 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let POST := malloc_large_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed msz TSD CTX TH sb pa nres nch chunks T d.

  (* [comment removed for export] *)
  Theorem malloc_large_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
Proof.
    (* LPS revision repair (75d69e00, checker 2c6b6db8).  The frozen KReplay.run1z proof of this
       theorem transported GAP under a hard-coded FOUR-conjunct motive, so it cannot carry the
       fifth conjunct the revision added to GAP: a farm round reports
       "Illegal application ... eq_ind_r ... which should be a subtype of (fun v => ...)
       (m_vmmaps mo)".  There is no recorder and a blob is never edited or re-encoded, so the
       proof is written out as explicit Rocq text (rule 11g), in the shape As/AS_CombinedLarge.v
       and As/AS_LargeAlloc.v already use in this tree, where the transport motive is recomputed
       from GAP at application time by rewrite ?(same_but_materialized_vmmaps _ _ SBM1) ...;
       try eassumption.  Every literal is this tree's own, printed from this file's own
       definitions by a farm round: AINST = 1821656, and malloc_large_head_post's
       frame aframe (sp + -2144) (wz 430168) sp (wz size) (wz 593408) (wz 1) (sp + -2128)
       (sp + -81) s6 .. s11.  No donor address is transposed: the caller's return address is
       taken from the goal by a match. *)
    intros K.
    (* Turn GAP's witness lower bound into the placement window alloc_sec_sreach demands.
       AHI_LO = 17594333495296 and task_unmapped_base = 183251939328, so the right disjunct
       holds by lia: no hypothesis is added, the fact comes from gap_witness_fit. *)
    assert (GAPD : exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + msz <= alloc_top (m_vmmaps mo)
                                    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g (wz msz) = true
                                    /\ (bv_unsigned g + msz <= mmap_top (m_vmmaps mo) \/ task_unmapped_base <= bv_unsigned g)).
    { destruct GAP as (g & P1 & P2 & P3 & P4 & P5). exists g. repeat split; try assumption.
      right. clear - P5. unfold AHI_LO, task_unmapped_base in *. lia. }
    clear GAP.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof SBR as R; destruct R as [SBR']. pose proof SPT as R; destruct R as [SPT'].
    pose proof SPA as R; destruct R as [SPA']. pose proof PAR as R; destruct R as (PLO & PHI & PAL). pose proof PLCD as R; destruct R as [PLCD']. pose proof NCH as R; destruct R as (NLO & NHI).
    unfold AHI_LO, AIMG_TOP, kSpaceSize, kPtrArrayReserve in RNG', TPR', SBR', PLO, PHI, PLCD'. acb.
    pose proof LO as LO'. acb. change (2^47) with 140737488355328 in SPT'.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    unfold AINST in *. change (1821656 + 64) with 1821720 in *. change (1821656 + 112) with 1821768 in *. change (1821656 + 136) with 1821792 in *.
    change (1821656 + 680) with 1822336 in *. change (1821656 + 688) with 1822344 in *. change (1821656 + 728) with 1822384 in *.
    region_table.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply (malloc_large_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size needed d TSD CTX TH TOP BOT CH sb);
        try eassumption. { destruct DEFS as [(D1 & D2)]. constructor. exact D1. } clear - HI; try acb; lia. }
    cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & jk & j8 & rest & m1 & VIS1 & MU1 & WM1 & MI1 & AEN1 & LR1 & TR1 & NT1 & ST1 & AFR1 & FRI1 & TFB1 & F41 & UNW1 & DEP1).
    fold CHI in AEN1, LR1, TR1, NT1. fold T in AEN1, LR1, TR1, NT1.
    senv_at SEN MU1 WM1 SEN1.
    assert (SVIS1 : forall x : word, in_rangesb x S = true -> wview asegs m1 x <> None) by (intros x Hx; apply WM1; exact (SVIS x Hx)).
    clear SEN ST UNW IEN.
    transport_after_call asegs m m1 MU1 WM1.
    replace (bv_unsigned sp + -2272) with (bv_unsigned sp + -2144 + -128) in VIS1, ST1 by lia.
    (* [comment removed for export] *)
    eapply (alloc_sec_sreach L S Zr msF1 mo1 Q (wz 430168) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp F fc m1
              sp (wz size) (wz 593408) (wz 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 j8 lo size needed msz TSD CTX TH sb (bv_unsigned sp + -2128) pa nres nch (size / 8) (size mod 8)
              (Z.of_nat (length T)) (d_putid d (depot_hash T)) chunks T rest d);
      rewrite ?unsigned_lit by (first [clear - LO' SPT' HI; lia | lia]); rewrite ?(same_but_materialized_vmmaps _ _ SBM1), ?(same_but_materialized_eager _ _ SBM1); try eassumption.
    { destruct DEFS as [(D1 & D2)]. constructor. repeat split; try assumption; try reflexivity. clear - SZ; try acb; Z.div_mod_to_equations; lia. }
    { clear - HI; try acb; lia. }
    { constructor. replace (bv_unsigned sp + -2144) with (bv_unsigned sp + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact SPA'. }
    { clear - SPT'; try acb; lia. }
    { clear - SZ; try acb; Z.div_mod_to_equations; lia. }
    { destruct PLCDP as [(Q1 & Q2)]. constructor. destruct PLCD' as (E1 & E2 & _ & _ & E5 & E6 & E7 & E8). exact (conj E1 (conj E2 (conj E5 (conj E6 (conj Q1 (conj Q2 (conj E7 E8))))))). }
    { constructor. clear - SPT'; try acb; lia. }
    { clear - NT1; try acb; lia. }
    { clear - DCAP NT1; try acb; lia. }
    cbv beta. intros msF2 mo2 P2.
    destruct P2 as (a & y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & b1 & m2 & AHI & CE & AL & FREE & OK2 & VIS2 & MO2
                    & MU2 & WM2 & MI2 & ST2 & AEN2 & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & PAJ2 & LHDR2 & LHJ2 & CH2 & B1 & MAG2 & MAGJ2 & FILL2 & SLK2 & SHA2 & SHU2 & TST2 & DEP2).
    rewrite ?unsigned_lit in MU2, ST2 by lia. unfold as_W in MU2. rewrite ?unsigned_lit in MU2 by (first [clear - HI PAE SPR LO'; lia | lia]).
    (* The caller's return address is whatever malloc_large_head left in ra; take it from the
       goal rather than transpose a donor literal. *)
    match goal with
    | _ : context[ret_pc (wz ?RA)] |- _ =>
        replace (ret_pc (wz RA)) with (Z_to_bv 64 RA) in VIS2 by (symmetry; apply ret_pc_even; [lia|reflexivity])
    end.
    rewrite unsigned_lit in ST2 by (first [clear - HI PAE SPR LO'; lia | lia]). unfold depot_W in MU2.
    unfold AINST in MU2, INST2, NRES2, SST2, MTX2, GST2. change (1821656 + 64) with 1821720 in INST2. change (1821656 + 112) with 1821768 in MU2, NRES2.
    change (1821656 + 136) with 1821792 in SST2. change (1821656 + 680) with 1822336 in SST2, MTX2. change (1821656 + 688) with 1822344 in GST2. change (1821656 + 728) with 1822384 in MU2, GST2.
    (* [comment removed for export] *)
    pose proof CE as CE'. acb.
    assert (MSZ : size + 4096 <= msz) by (destruct DEFS as [(D1 & D2)]; clear - D1 D2 SZ; try acb; subst needed msz; unfold round_up; Z.div_mod_to_equations; lia).
    pose proof (aapp_env _ _ AHI ltac:(clear - MSZ SZ; lia)) as [AHI' _]. pose proof (aapp_lit _ _ AHI) as ALIT.   (* [comment removed for export] *)
    assert (PLCA : hidden ((TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX) /\ (a + msz <= pa \/ pa + 8388608 <= a)
                           /\ (a + msz <= d_nb d \/ d_nb d + 16 * 65536 <= a) /\ (a + msz <= d_sb d \/ d_sb d + 8 * 32768 <= a))).
    { rewrite (same_but_materialized_vmmaps _ _ SBM1) in FREE. constructor. split; [| split; [| split; [| split]]].
      - pose proof (free_vs_mapped _ _ a msz TH 4096 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) TMAPS). (first [clear - H; lia | lia]).
      - pose proof (free_vs_mapped _ _ a msz CTX 160 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; (first [clear - SZ PAE SPR AHI' CE'; lia | lia])) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) CMAPS). (first [clear - H; lia | lia]).
      - apply (free_vs_mapped _ _ a msz pa 8388608 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; lia)). unfold kPtrArrayReserve in PMAPS. exact PMAPS.
      - apply (free_vs_mapped _ _ a msz (d_nb d) (16 * 65536) FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PLCD'; aunf; lia) ltac:(hci; clear - PLCD'; aunf; lia) ltac:(hci; lia) DNMAPS).
      - apply (free_vs_mapped _ _ a msz (d_sb d) (8 * 32768) FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PLCD'; aunf; lia) ltac:(hci; clear - PLCD'; aunf; lia) ltac:(hci; lia) DSMAPS). }
    assert (DBND : 7430144 <= d_nb d /\ 7430144 <= d_sb d) by (clear - PLCD'; try acb; aunf; lia).   (* [comment removed for export] *)
    assert (SHB : 2148314624 <= sh a /\ sh a + msz / 8 <= 17594333495296) by (clear - AHI' CE' AL; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (ABND : 7430144 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil) by (clear - AHI' CE'; try acb; lia).   (* [comment removed for export] *)
    region_retable.
    apply (munch_weaken _ (ml_W lo sp a msz pa nch nres TH d)) in MU1; [| unfold ml_W, depot_W, sub_fp; cbn [outside]; clear; intros; tauto]. unfold ml_W, depot_W in MU1.
    unfold AINST in MU1. change (1821656 + 112) with 1821768 in MU1. change (1821656 + 728) with 1822384 in MU1.
    senv_at SEN1 MU2 WM2 SEN2. clear SEN1 ST1 AFR1 DEP1 SVIS1 INST64 NRES SST MTX GST TST PA PAJ.
    transport_after_call asegs m1 m2 MU2 WM2.
    (* [comment removed for export] *)
    pose proof AEN2 as E2. open_env E2.
    eapply (evt_sreach_lazy_at asegs _ _ Zr _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (malloc_ret sp ra s0 s1 s2 s3 s4 s5 (wz 430168) gp tp _ _ _ sp (wz size) _ _ _ _ _ _ _ (wz 593408) (wz 1)
                (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 lo (a + 6144) T rest jk);
        try eassumption. { clear - HI; try acb; lia. } { first [clear - AHI' CE' MSZ SZ; try acb; lia | (try acb; lia)]. } }
    cbv beta. intros msF3 mo3 OK3 SBM3 HS3 P3. destruct P3 as [VIS3 ST3].
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Eso Etr.
    (* [comment removed for export] *)
    apply K. unfold POST, malloc_large_post.
    exists a, y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, b1, rest, m2.
    cbv zeta. unfold ml_W, depot_W, AINST. change (1821656 + 64) with 1821720. change (1821656 + 112) with 1821768. change (1821656 + 136) with 1821792.
    change (1821656 + 680) with 1822336. change (1821656 + 688) with 1822344. change (1821656 + 728) with 1822384.
    split; [exact AHI|]. split; [exact CE|]. split; [exact AL|]. split; [rewrite <- (same_but_materialized_vmmaps _ _ SBM1); exact FREE|].
    split; [exact OK3|]. split; [exact VIS3|].
    split.
    { apply (as_model_mat _ _ _ _ _ _ mo2); [| exact SBM3].
      pose proof MO2 as MO; unfold as_model in MO |- *. cbv beta iota zeta in MO |- *.
      rewrite <- (same_but_materialized_vmmaps _ _ SBM1), <- (same_but_materialized_eager _ _ SBM1).
      destruct MO as (NV2 & REST). split; [| exact REST]. eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| exact NV2]. }
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI2|]. split; [exact ST3|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End MallocLarge.

End HCW2.

