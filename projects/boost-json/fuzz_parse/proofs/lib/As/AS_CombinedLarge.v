(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text. *)
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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit F_memset.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AW_Leaves AW_PoisonShadow AW_MmapFixed AW_SecMmap CidBits SecMsb AW_Combined AW_AllocBase
     AW_LargeAlloc1 AW_LargeAlloc2 AW_LargeAlloc3 AW_LargeAlloc4 AW_CombinedLarge AW_MallocBase SecLazy AS_LargeAlloc AllocTacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AS_CombinedLarge () := KReplay.lz_vm "#$^AC89OSSVerify6Proofs:boost_json:fuzz_parse3lib2As8AsShadow4aappC13~~~C56Stdlib6ZArith6BinInt1Z3add!t/\5aceil!t0B2leK47Corelib7Numbers7BinNums1Z02!s`<6moduloI!sd+4Init5Logic2eq00!s@83and00C!sA75proj1K!sA19Datatypes4list01I!sFA0K4!t~&9micromega6VarMap1!sd$!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr01!vv=8positive02K!tAL1!sQ65Tauto8G!sJ'4C!sJ<B!sJ&K!wv;1!sb6:Z!tV+=Z!sn$CheckerC!vf<4find!sqAC!sq0_soun!{LVllocRep8!|U#_env!{O&7!snN>Asan!so$Model@kPtrArrayReserve!sy%I!|-?0!xTG3!|q@!zS7!vL-;!}-%!uB$!|H#!xO:5eKind!|+=uni!|+9!se%4kind!yz8!zM13Op2!uF/!t58!}[>bool!vS/!sF8!|I>1N02C45stdpp9bitvector;definitionsDbv_unsigned_in_range!sYA;!sY-!sPA:bv_!#5N#usI!zpR<!z#$WalkKit6hidden00!zt&!srR@AW_CombinedLargeHc!s4&_l!s5#_seg1_post!t-V3Lib5Frame3mkR!sg%!{LG1!vYA7Z_to_bvI!sL@2bv!y5>6op!sL#02!uGT8PropExec7seg_rom!v7Z6MState2MS!sg&!|?59SatDivModCZ!yC#_nonneg!s,&!sWCdiv!sW2!#>[;div!sC<>pow!xo#!skDpow!sC<:!sk#!sg%!#;6D2!sIE7!tU=mul!{kdC!{k6!z}'ELinuxProcessSemantics?!s<23Run6config01!#9AO<LazyRestrictEsame_but_materialized!#:?U6!s|#SR8hid_!sz#!siV!tg08r!s/&!#:x2!|v:0!|-T4TacX2wz!#3=B1Z03!#8t<prod00!yD=sub!#5%Y5munch!~[Z3Mem7mem_i!#?U'!#@EZ5akobj!#3J&!wM;length!#HQ<of_nat!sF34Znat5Nat2Z9is!}wE3P!#<b0!tT23nat!#F#E5Psatz!#JO=2lt!u`,5Lists7!s+#Def3map!#5o'!sA%4!s+#:!uw%_!sE$!tm0!#F6$8eq_ind_r!wN]wli!#;lW!#N$-;!#N$#_facts!}YV8HeapCeil5h!#Np,!t[R9!uH$!}4#;regio!#A/#k!src9!sr&lb!spkub!|Hb!#Ig$lit!t`cA!t`&side_intro!w@k!sx#!yib2sh!vFb?!vF$sh!vI#_div!#8A7!#Oe%or!#89Q!t7/9!#4y#!wX]!so3e!#6[Z!z'/x_unh!wM\!xA5psep!#7T7!#Wb,2!#Q3^8round_up!u$c:!u$&fa!#Fb%K!xa;1!v5ehull!t4B!#HzT!#=@$=disjoint_f!#H}X2As>AW_!#DI#!u/$1>senv_transpor!#A;&!sza4SENV!#O-'!#:C7iff_refl!#Iq5;ZifyClasses3inj!sIB;rew_!su%v!vuUCells:c!s+#_size!x#'!#=oH7!t?T3Arr@u64arr!w;3!yD8!#aR#1!t5T!#NQ%<!#UK'!#48+4!#AO2div?!#NS$plus_fullK!xnR!#Tv71!t?'!#K-H5!u$$8m_vmmaps!s]Q7vm_!s\$!#3tN:LazyLedger>entries_nowra!#3v&!#Jr[L!#L[7!uP'!v5V;vm_noac!s;#!uZ[9nooverl!uUe:eager_us!#O#W!sq0;pages_total!yFXvm_limit!tQ]K!ws9!uZ$!taW9a!{s#_top!xRUr!#e;$d!#Lm;3app!#mu9x00!xA^!#aL&sb!ujW<map_contains!#:0R=AS!#94,@!#WO$!vc%!#`=,!#RW;eqb!t{Q=!}<#_subtract!#pkA2!#6zZ6ret_pc!#=;X!v118la_model!ssg4la_W!soV!#Wp+b8!#=p2!#Qp06repe!#T14!#TQ+to_natK!#=CX4cell!#9S'!wcZ;!wc%_even!uC3!|c-6eq_sym!u@<7di!#ir#!sc83no!uz==!#<^#os_b!#rH#!sM@neg!sM25!#?k#8PreO!s/#1Z;!tW#0_r_ext!sL>!st#!sL&K!#3K:!#G$S!#>;/:!#>;$_ou!#k,`:!#]&#!#DQ$!sn`wmono!sn[!#IV/=rx_not_in_s!#T`W!td,7out!#RoY!sk,6sub_fp!sj`<!w,%weak!{o+!spY;!sp%!#FR#!soa!wx%!so[!#rhI2!#rhZ!#k'I2!#3\73Nat!$->#!#LA@5mkrel!#a3>app!#mN=ax!sC<8max_spec!$%pE6!tP7=!#8'$_!#e]%!xRS3Arr?u8!#Lm5!#7#;i!$%@T7SecLazy:nonvm!#m=-!#@dPvm_mmap_base!saQ6vm_brk!t>Ustart!sa$!ujZ>!uj,_ma!{IZ!ss'@!ss-!}H^!#?h0<!#@]&!tnZ!y^#2Nd;ex!#c%$F14!sl]:and_elimF5!sk]9ex!sj%!#?}&!#u#UBevt_sreach_lazy_!v:_!uL,3!w#^!sk+26!tY^!v:+6!ySgB!#J=-!vM%!vEg!tj&I!x#PSR!tM#6!tT%!#^-&!$;s?2!sD@3!#~mD3!#7^E8!sJF!snG5I!{,V4lzok!v&,!#Mr:!#zl#1!#>aY5!#>a#!xeZ!$1=%stk!sgZ4Step8rw_!#al#!xc<!#ag74!sOK6!sO6!$:_:!$,<E4!#?XDapp!sKB6!sK$!#i2ZB!vP'!#c~4!v1I5!u]E5!tjT3Arr6!#ef$!yf`Fstk!uO,_!#kn&!sz&!#[NP!#nk&ree!uFX5!#B>#!v{<!y];!~qG7!#7cR5ASegs5aseg!#~EV4Scfg=hunspell_scfg!yKJ!$B3#5!t}S!$%:+AINST!#8c%!x,J>Riscv!sE+=machine_s!xD#00I!ypT!#X>,0!x=T!$ENI1!#b+74True!$>s3!sB/!$Ef<!$/B#0I!#GUPVmMaps!$4N,5!uA$8PeanoNa!#MP+!$1N<7inj_!#Ms88ZifyInst@!$2<$_!#\p$_eq!tuQ5!#z5#!#~VT!{l%8AIMG_TOP!#;cA!v_$!#z#]=!#3G%tabl!#kh'!v3>7Inj_Z_Z!#i]Qpage!#v2$!v+X7!v+$LO!#6uU!$+C-9ALOWSH!soe6AHI!sle3mem!xMB!$NN$2!}-85False00".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44listk44prod3h5LinuxProcessSemanticsfLinuxProcessSem5Statema5Model3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsq0dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeu75bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~hh53mem46Stdlib6ZArith6BinInt1Zhla3add37Corelib4Init5Logichn93and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hp45asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ht82wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ih94cellk44conshn92exih92C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~in03stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~ir35AINSTk44boolk43nilhh52sh79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jgd8rw_cellshla3mulhn92eqk43app37Corelib5Lists7ListDefjm76repeatma8m_vmmaps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jp35u8arrht82b8hla3divhla3subk44Nonek44pairk44true3h5LinuxProcessSemanticsfLinuxProcessSem3Runjvf5mkCfgmadmaps_subtractmabregion_freema7vm_mapsmabvm_reserved79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAS_LargeAlloc~~~~~~kma4la_Wkma8la_model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAW_LargeAlloc1~~~~~~ks14SENVir35wlisthh54aapphh55aceil69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~li78restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~ln24lzokjp36u64arrin03mkRin05munchin05wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lt62MSlt66ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mi37mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mm87seg_romhla3eqbhla2lehla6modulohla6to_nathfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAllocWalkKit~~~~~~mu16hidden69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~nid8round_uphla3powhla2lthp48AIMG_TOPir35akobjhn92ornidh0kPtrArrayReservenid4zlen69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~nrfeentries_nowrapmabvm_noaccessnrf9nooverlapma9page_sizema8vm_limitli7aeager_usedli7bpages_totalma9alloc_tophp47AIMG_LOli7ain_rangesbhh56AHI_LOhh59ALOWSH_LO69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~op95hceilk46optionhn93notq05wviewmacmap_containsk45falsehf7Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition combined_large_post : ltac2:(zQ "92!h9!jc!k1!lc!m3!p8!t7!hgd!hl3&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>1L~1>1S~1>2Zr~1>2mo$5>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$8>2lo$2>4size$2>3msz$2>5size8$2>3TSD$2>3CTX$2>2TH$2>2pa$2>4nres$2>3nch$2>6chunks@1$3$2>4msF'$6>3mo'$5P") := ltac2:(zQ "jd3!h9!jc!hn2!hod!k1!hsf!ih3!il5!ild!im4!ima!m3!iqc!iv1!iva!lc!jg1!jg7!jk8!jl4!jlb!hl3!jm1!jne!t7!p8!jo8!jsd!jt6!jtc!ju3!jua!jv1!jv8!kib!kj4!kk4!kl2!klc!hgd!kqd!kr5!lg5!lgd!lh6!lhe!lm6!lqb!lr3!lrd!ls4!lsd!mh3!mh9!mld!mq7!mr2!mr9!mrf!ms9!mt3&@2$b@1$1@1$0#k0@1$1@1$0#k0&@1$f~0&@3$8~0^1^j5\1L~1\1S~1\2Zr~1\2mo$h9\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$i7@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$h5\2lo$4\4size$4\3msz$4\5size8$4\3TSD$4\3CTX$4\2TH$4\2pa$4\4nres$4\3nch$4\6chunks@1$f$4\4msF'$h8\3mo'$h9@2$9$4\1a$4@2$9@1$1@1$0#k0\2t0@1$1@1$0#k0@2$9@1$1@1$0#k0\2t1@1$1@1$0#k0@2$9@1$1@1$0#k0\2t2@1$1@1$0#k0@2$9@1$1@1$0#k0\2a2@1$1@1$0#k0@2$9@1$1@1$0#k0\2a4@1$1@1$0#k0@2$9@1$1@1$0#k0\2a5@1$1@1$0#k0@2$9@1$1@1$0#k0\2a6@1$1@1$0#k0@2$9@1$1@1$0#k0\2a7@1$1@1$0#k0@2$9@1$1@1$0#k0\2t3@1$1@1$0#k0@2$9@1$1@1$0#k0\2t4@1$1@1$0#k0@2$9@1$1@1$0#k0\2t5@1$1@1$0#k0@2$9@1$1@1$0#k0\2t6@1$1@1$0#k0@2$9$h5\2m'$h5=9committed$e@2$j8^h2^h3=5nres'$4Me\9committed$e$4^1@2$2^h4+kgg0^h4=2L'~1Me\9committed$e~1^2@3$i3^j4@2$2^h6@2$h3+8^h5@2$2@2$2^h6@2$h3+8^h5+iggg0^j4=1W~0@4$i0@1$1@1$0#k0@1$1@1$0#k0@1$6@1$h1^h1@1$6@2$hd^hc+8@2$3@3$ic?5HCEIL^h2^hd@2$3@2$j9@2$2^h2^hd@1$id?5HCEIL@2$3@3$h4$4@2$ja^h2+hgg0Z@2$3@3$h4$e@3$i4@3$h6~0@1$i6@1$ha^j3@1$i5@1$ha^j3@1$6^h2@1$6^hd$i1@2$3@5$if$5^2~2^j4@2$i2^h4^h3@2$3@3$h4$h8@3$ie^2~2^h4@7$j4@hf$j1^j2^j1^j0^if^h1^h0^f^ie^id@1$6@2$2^h2+hgg0@1$6+9^e@1$6+8^d^c^b^a^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^9^8^7^6^i2@1$j5^j2^i1@1$hf@1$1@1$0#k0^5@1$j7$5@2$3@7$i9^j3^h2^hd^h8^h7^4^h3@2$3@3$j2@8$i8^hf^j1^h2^hd^h8^h6^h7^h9^i0^5@2$3@3$j3$5^i0^5@2$3@2$j6$5^5@2$3@4$c$5^5^hf@2$jc@1$0#k0^j1@2$3@5$ia^if^hb^ha^h9^5@2$3@4$h2$5^5@2$2$d+k0@3$8$7@1$a@1$6+hgg0@3$8$7@1$a@1$6^h8@3$8$7@1$a@1$6^h8@1$h0$7@2$3@4$h2$5^5@2$2$d+n0@3$8$7@1$a@1$6^3@3$8$7@1$a@1$6@2$2^h6+1@3$8$7@1$a@1$6Z@1$h0$7@2$3@4$c$5^5@2$2$d+o8@2$2$d+iq8@2$3@4$h2$5^5@2$2$d+iq8@3$8$7@1$a@1$6Z@1$h0$7@2$3@4$c$5^5@2$2$d+ir0@2$2$d+it8@2$3@4$j0$5^5^h8@1$ib@3$h6$4^h5@3$8$4^h2@1$h0$4@2$3@4$c$5^5@2$2^h8@2$h3+8@2$2^h6+1@2$2^h8@2$h3+8^3@2$3@4$h2$5^5^h2@3$8$7@1$a@1$6^h2@3$8$7@1$a@1$6^hd@3$8$7@1$a@1$6^he@3$8$7@1$a@1$6^h6@1$h0$7@2$3@4$c$5^5@2$2^h2+i0@2$2^h2+hgg0@2$3@4$c$5^5@2$2^h2+hgg0@2$2^h2^hd@2$3@4$hb$5^5@1$h1^h2@3$h7@1$1@1$0#8@1$hc+vaNig0@2$3@4$c$5^5@2$2@1$h1^h2+ig0@2$2@2$2@1$h1^h2+ig0^hc@2$3@4$hb$5^5@1$h1@2$2@2$2^h2+hgg0^he@3$h7@1$1@1$0#8@1$hc+va@1$jb@2$hd@2$he@2$he^hd+hgg0^he+8@4$c$5^5@2$2^h9+qv0@2$2^h9+sm0").

Section CombinedLarge.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size msz size8 TSD CTX TH pa nres nch : Z) (chunks : list Z).
  Hypothesis DEFS : ltac2:(zQ "50!jlb!k1!ni3!nme!hn2@1$2@3$0$1?3msz@2$4@2$3?4size+hgg0+hgg0").
  Hypothesis MI : ltac2:(zQ "20!hsf!mld@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!h9!hsf!iqc!mt3@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!lhe!mr9@2$1@1$0?5HCEIL?2lo").  Hypothesis HI : ltac2:(zQ "40!h9!hn2!mr9!mt3@2$2@2$1?2lo+ig0@2$3@1$0#k0?2sp").
  Hypothesis SPA : ltac2:(zQ "60!jlb!h9!k1!ni3!mrf!mt3@1$3@3$0$2@2$4@2$5@1$1#k0?2sp+h0Z"). Hypothesis SPH : ltac2:(zQ "50!h9!hn2!mr9!nna!mt3@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis Ha0 : ltac2:(zQ "50!jlb!h9!iv1!ih3!jc@3$0@1$4@1$1#k0?2a0@1$3$2"). Hypothesis Ha2 : ltac2:(zQ "40!jlb!h9!ih3!jc@3$0@1$3@1$1#k0?2a2@1$2?4size"). Hypothesis Ha3 : ltac2:(zQ "40!jlb!h9!ih3!jc@3$0@1$3@1$1#k0?2a3@1$2+8").
  Hypothesis SZ : ltac2:(zQ "70!hod!jlb!k1!mr9!no1!jl4!nna@2$0@2$4+hggg0?4size@2$0@2$3?4size@2$6+2+i9@3$1$2?4size@2$5+8?5size8").
  Hypothesis TPR : ltac2:(zQ "70!h9!mr9!mt3!hod!no7!ni3!hn2@1$5@2$3@2$1+mqiho8@2$2@1$0#k0?2tp@2$1@2$6@2$2@1$0#k0?2tp+hgg0$4").
  Hypothesis RNG : ltac2:(zQ "b0!hod!mr9!hn2!lhe!jlb!k1!no7!np3!ni3!lh6!mrf@1$8@2$0@2$1+mqihj0?3TSD@2$0@2$1@2$2?3TSD+8$6@2$0@3$9?5HCEIL?3CTX+q0@2$0@2$1@2$2?3CTX+q0@1$3?5HCEIL@2$0@3$7?5HCEIL?2TH+hgg0@2$0@2$1@2$2?2TH+hgg0@1$3?5HCEIL@3$4$5@2$a?2TH+h0Z").
  Hypothesis PLC0 : ltac2:(zQ "60!hn2!mr9!npc!hod!nq2!ni3@1$5@2$3@2$2@2$1@2$0?3CTX+q0?2TH@2$1@2$0?2TH+hgg0?3CTX@2$3@2$2@2$1@2$0?2pa$4?2TH@2$1@2$0?2TH+hgg0?2pa@2$2@2$1@2$0?2pa$4?3CTX@2$1@2$0?3CTX+q0?2pa").
  Hypothesis PAR : ltac2:(zQ "90!hod!nq2!jlb!k1!lh6!lhe!hn2!mr9!mrf@2$0@3$4?5HCEIL?2pa$1@2$0@2$7@2$6?2pa$1@1$5?5HCEIL@3$2$3@2$8?2pa+hgg0Z").
  Hypothesis NCH : ltac2:(zQ "40!mr9!hod!hn2!nna@2$1@2$1@2$0Z?3nch@2$0?3nch?4nres@2$0@2$2?4nres+kgg0@2$3+2+h4"). Hypothesis NRQ : ltac2:(zQ "40!k1!jlb!im4!jl4@2$2$0\1q$0@3$1$0?4nres@2$3+ig0^1").
  Hypothesis LEN : ltac2:(zQ "30!k1!jlb!nr7@3$1$0@2$2$0?6chunks?3nch").
  Hypothesis ENV : ltac2:(zQ "10!lg5@5$0?2tp?3TSD?3CTX?2TH?1m").
  Hypothesis INST64 : ltac2:(zQ "90!il5!ild!ima!ih3!jg1!hsf!iv1!jk8!hn2@4$7$5?1m@2$8$6+k0@3$1$0@1$2@1$3+hgg0@3$1$0@1$2@1$3?2pa@3$1$0@1$2@1$3?2pa@1$4$0").
  Hypothesis NRES : ltac2:(zQ "90!il5!ild!ima!ih3!jg1!hsf!iv1!jk8!hn2@4$7$5?1m@2$8$6+n0@3$1$0@1$2@1$3?4nres@3$1$0@1$2@1$3?3nch@3$1$0@1$2@1$3Z@1$4$0").
  Hypothesis SST : ltac2:(zQ "40!iv1!hn2!hsf!iqc@4$3$2?1m@2$1$0+o8@2$1$0+iq8").
  Hypothesis MTX : ltac2:(zQ "90!il5!ild!jg1!hsf!iv1!ima!jk8!ih3!hn2@4$6$3?1m@2$8$4+iq8@3$1$0@1$5@1$7Z@1$2$0").
  Hypothesis GST : ltac2:(zQ "40!iv1!hn2!hsf!iqc@4$3$2?1m@2$1$0+ir0@2$1$0+it8").
  Hypothesis TST : ltac2:(zQ "30!hn2!hsf!iqc@4$2$1?1m@2$0?2TH+qv0@2$0?2TH+sm0").
  Hypothesis PA : ltac2:(zQ "30!hsf!lgd!lr3@4$2$0?1m?2pa@1$1?6chunks").
  Hypothesis PAJ : ltac2:(zQ "40!hn2!jl4!hsf!iqc@4$3$2?1m@2$0?2pa@2$1+8?3nch@2$0?2pa@2$1+8?4nres").
  Hypothesis NW : ltac2:(zQ "30!jo8!kl2!nvc@1$2@1$1@1$0?2mo"). Hypothesis NWA : ltac2:(zQ "30!jo8!oge!nvc@1$2@1$1@1$0?2mo").
  Hypothesis NOV : ltac2:(zQ "30!jo8!kl2!ohc@1$2@1$1@1$0?2mo").
  Hypothesis BUD : ltac2:(zQ "90!hn2!oi9!jl4!jo8!oj5!ok0!oke!jtc!mr9@2$8@2$0@2$0@2$0@2$0@1$5?2mo@2$2@1$6?1S$1?3msz@2$2@2$0@2$7?3msz+ogg0+2$1+iggg0@1$4@1$3?2mo").
  (* LPS revision repair (75d69e00, checker 2c6b6db8).  GAP written out as explicit text (rule 11,
     never re-encoded), with the disjunct the revision added to Bs/SecLazy.v:140-143's
     sr_mmap_kernel_MS, exactly as As//Bs AS_LargeAlloc.v now carry it: large_alloc_sreach, which
     this file applies, demands it, and g is GAP's own witness, so it must come from above.
     FAITHFULNESS CONTROL (rule 22c): `About GAP` on the encoded original, printed by
     a farm round, reads this text minus the last conjunct, character for
     character.  It carries no address and no literal, and is the same on both sides. *)
  Hypothesis GAP : exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + msz <= alloc_top (m_vmmaps mo)
                                    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g (wz msz) = true
                                    /\ (bv_unsigned g + msz <= mmap_top (m_vmmaps mo) \/ task_unmapped_base <= bv_unsigned g).
  (* [comment removed for export] *)
  Hypothesis IMGR : ltac2:(zQ "e0!h9!mt3!iva!jv8!hod!jlb!jo8!klc!om9!no7!on4!mr9!no1!jc>1x@1$d@1$0#k0>0@2$4@2$b$8@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1$9@3$5$2@2$a^2@1$7@1$6?2mo$3").
  Hypothesis SHLAND : ltac2:(zQ "e0!h9!mt3!iva!jv8!hod!jlb!jo8!kl2!oo2!ooc!on4!mr9!no1!jc>1x@1$d@1$0#k0>0@2$4@2$b$9@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1$8@3$5$2@2$a^2@1$7@1$6?2mo$3").
  (* [comment removed for export] *)
  Hypothesis ATOP : ltac2:(zQ "50!jlb!k1!old!jo8!ot4@3$0$1@1$2@1$3?2mo@1$4?5HCEIL").
  Hypothesis ZRSH : ltac2:(zQ "h00!h9!jg7!mt3!hod!mr9!no1!iva!jv8!jlb!npc!no7!oo2!ooc!lhe!on4!jc>1x@1$f@1$0#k0>0@2$9@2$3@2$4@1$1$b@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1@1$d?5HCEIL@2$3@2$4@1$1$a@2$2@1$0#k0^1@2$5@2$2@1$0#k0^1@1$1$c@3$8$6@2$e^2?2Zr$7").   (* [comment removed for export] *)
  Hypothesis SVIS : ltac2:(zQ "b0!h9!jc!jlb!jua!iva!otd!jv8!ou6!oud!hsf!on4>1x@1$1@1$0#k0>0@3$2$4@2$a^1?1S$6@1$7@3$2@1$5@1$1@1$0#8@3$8$9?1m^2@1$3@1$1@1$0#8").
  Hypothesis TMAPS : ltac2:(zQ "d0!h9!mt3!iva!jv8!hod!jlb!jo8!kl2!on4!hn2!mr9!no1!jc>1x@1$c@1$0#k0>0@2$4@2$a?2TH@2$1@1$0#k0^1@2$b@2$1@1$0#k0^1@2$9?2TH+hgg0@3$5$2@2$8^2@1$7@1$6?2mo$3").
  Hypothesis CMAPS : ltac2:(zQ "d0!h9!mt3!iva!jv8!hod!jlb!jo8!kl2!on4!hn2!mr9!no1!jc>1x@1$c@1$0#k0>0@2$4@2$a?3CTX@2$1@1$0#k0^1@2$b@2$1@1$0#k0^1@2$9?3CTX+q0@3$5$2@2$8^2@1$7@1$6?2mo$3").
  Hypothesis PMAPS : ltac2:(zQ "e0!h9!mt3!iva!jv8!hod!jlb!jo8!kl2!nq2!on4!hn2!mr9!no1!jc>1x@1$d@1$0#k0>0@2$4@2$b?2pa@2$1@1$0#k0^1@2$c@2$1@1$0#k0^1@2$a?2pa$8@3$5$2@2$9^2@1$7@1$6?2mo$3").
  Hypothesis PAMC : ltac2:(zQ "a0!jlb!ih3!iva!jv8!k1!jo8!ov5!kl2!hn2!jl4>0@3$0$4?3nch?4nres@3$0$2@3$6@1$7@1$5?2mo@1$1@2$8?2pa@2$9+8?4nres@1$1+iggg0$3").
  Hypothesis PARF : ltac2:(zQ "a0!jlb!ih3!iva!jv8!k1!jo8!kk4!klc!hn2!jl4>0@3$0$4?3nch?4nres@3$0$2@3$6@1$7@1$5?2mo@1$1@2$8?2pa@2$9+8?4nres@1$1+iggg0$3").
  Hypothesis PAZR : ltac2:(zQ "d0!h9!hn2!jlb!jl4!mt3!iva!pg4!hod!k1!on4!mr9!no1!jc>0@3$2$8?3nch?4nres>1x@1$c@1$0#k0>0@2$7@2$a@2$1?2pa@2$3+8?4nres@2$4@1$0#k0^1@2$b@2$4@1$0#k0^1@2$1@2$1?2pa@2$3+8?4nres+iggg0@3$2$5@2$9^2?2Zr$6").
  Hypothesis OK : ltac2:(zQ "30!kib!hsf!lqb@5$2$1?1L?1S?2Zr@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "b0!h9!jua!jlb!t7!hsf!lm6!lrd!mh3!mq7!pgc!jc@3$2$3@3$5?1L?1S?3msF@7$7@hf$6?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1?2a0?2a1?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$9@1$0#k0+mtnu4?2fc@1$1@1$a@1$0#k0?1m@1$8$4").

  Let PAE : 7430144 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let POST := combined_large_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size msz size8 TSD CTX TH pa nres nch chunks.

  Theorem combined_large_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
Proof.
    intros K.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof SPA as R; destruct R as [SPA'].
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply combined_large_seg1; try eassumption; lia. }
    cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR'].
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    unfold AHI_LO, AIMG_TOP, kPtrArrayReserve in RNG', TPR'. pose proof PAR as PAR'. unfold AHI_LO, kPtrArrayReserve in PAR'.
    acb.
    unfold AINST in *. change (1821656 + 64) with 1821720 in *. change (1821656 + 112) with 1821768 in *. change (1821656 + 136) with 1821792 in *.
    change (1821656 + 680) with 1822336 in *. change (1821656 + 688) with 1822344 in *. change (1821656 + 728) with 1822384 in *.
    region_table.
    senv_at ENV MU1 WM1 ENV1.
    transport_after_call asegs m m1 MU1 WM1.
    (* [comment removed for export] *)
    eapply (large_alloc_sreach L S Zr msF1 mo1 Q _ (Z_to_bv 64 (bv_unsigned sp + -48)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1
              lo size msz size8 TSD CTX TH pa nres nch chunks DEFS MI1); rewrite ?unsigned_lit by lia;
      rewrite ?(same_but_materialized_vmmaps _ _ SBM1), ?(same_but_materialized_eager _ _ SBM1); try eassumption; try reflexivity; try (first [lia0 | qlia]).   (* [comment removed for export] *)
    { constructor. replace (bv_unsigned sp + -48) with (bv_unsigned sp + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact SPA'. }
    { intros x Hx. apply WM1. apply SVIS. exact Hx. }
    { rewrite Ha2, Ha3. exact VIS1. }
    cbv beta. intros msF2 mo2 P2.
    destruct P2 as (a & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & AHI & CE & AL & FREE & OK2 & VIS2 & MO2
                    & MU2 & WM2 & MI2 & ST2 & ENV2 & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & PAJ2 & HDR2 & HDR32 & USR2 & SHA2 & SHM2 & SHT2 & TST2).
    unfold la_W in MU2. rewrite unsigned_lit in MU2, ST2 by lia.
    remember (if nch =? nres then nres + 16384 else nres) as nres' eqn:EN.
    assert (NB : nres <= nres' <= nres + 16384) by (destruct (nch =? nres); lia).
    (* The donor names the caller's return address as a literal (ech 1705948).  That address is
       whatever combined_large_seg1 leaves in ra, so rather than transpose a number or invent
       one, take it from the goal: the rewrite is about the SHAPE ret_pc (wz _), and the side
       conditions are closed on whatever literal this tree's own seg1 produced. *)
    match goal with
    | _ : context[ret_pc (wz ?RA)] |- _ =>
        replace (ret_pc (wz RA)) with (Z_to_bv 64 RA) in VIS2 by (symmetry; apply ret_pc_even; [lia|reflexivity])
    end.
    pose proof DEFS as D; destruct D as [DMSZ].
    assert (MSZ : size + 4096 <= msz /\ msz < size + 8192 /\ exists q, msz = 4096 * q).
    { rewrite DMSZ. unfold round_up. split; [|split]; try (Z.div_mod_to_equations; lia). exists ((size + 4096 - 1) / 4096 + 1). lia. }
    destruct MSZ as (MSZ1 & MSZ2 & mq & MQ).
    pose proof (aapp_env _ _ AHI ltac:(clear - SZ MSZ1; lia)) as [ALO _]. acb.   (* [comment removed for export] *)
    assert (BND : 7430144 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil /\ 2148314624 <= sh a /\ sh a + msz / 8 <= sh aceil).
    { unfold sh, ASHADOW_BASE. rewrite MQ. assert (AQ : exists aq, a = 4096 * aq) by (exists (a / 4096); Z.div_mod_to_equations; lia).
      destruct AQ as [aq AQ]. rewrite AQ. clear - ALO CE MQ AQ MSZ1 SZ; try acb. Z.div_mod_to_equations. lia. }
    region_sides. name_bands.
    unfold AINST in MU2. change (1821656 + 112) with 1821768 in MU2. change (1821656 + 728) with 1822384 in MU2.
    region_table.
    pose proof (munch_refl (la_W lo sp a msz pa nch nres TH) m) as MU. unfold la_W, AINST in MU.
    change (1821656 + 112) with 1821768 in MU. change (1821656 + 728) with 1822384 in MU.
    pose proof (wmono_refl asegs m) as WM.
    clear ENV INST64 NRES SST MTX GST TST PA PAJ ST1 ENV1.
    transport_after_call asegs m m1 MU1 WM1. clear MU1 WM1.
    (* LPS revision repair (75d69e00, checker 2c6b6db8).  transport_after_call DROPS the
       saved-register frame FR1 here — a farm round printed
       "note: dropping hypothesis (not provably disjoint from callee footprint): FR1" and then
       the unclosed goal rw_cells asegs m2 (bv_unsigned sp + -48) [...], which is exactly that
       frame.  So carry it over by hand, with the same lemma the tactic uses, and discharge the
       disjointness from this tree's own stack bound (HI: lo + 512 <= bv_unsigned sp; the callee
       was entered at sp - 48, so its footprint stops below this frame). *)
    (* The one region region_decide cannot place is the shadow of the new chunk
       (a farm round printed exactly that conjunct and no other).  It is below
       the stack by this tree's own chain: BND gives sh a + msz / 8 <= sh aceil, acb's ACEILB
       gives sh aceil <= 0x10007fef8000 < 0x7fff7f800000 <= aceil, LO gives aceil <= lo and HI
       gives lo + 512 <= bv_unsigned sp.  No literal of mine: every number is ACEILB's. *)
    assert (SHSP : sh a + msz / 8 <= bv_unsigned sp + -48).
    { acb.
      first [ lia
            | (eapply Z.le_trans; [ exact (proj2 (proj2 (proj2 (proj2 BND)))) | ]; lia)
            | (eapply Z.le_trans; [ exact (proj2 (proj2 (proj2 (proj2 BND)))) | ];
               unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia) ]. }
    lazymatch type of MU2 with
    | munch ?W _ _ =>
        apply (rw_cells_transport asegs W m1 m2 _ _) in FR1;
          [ | exact MU2 | exact WM2
          | cbn [disjoint_from]; simpl_sizes; pose proof PAE as PAEc;
            repeat match goal with |- _ /\ _ => split end;
            first [ exact I | (right; exact SHSP) | region_decide | slia
                  | (try acb; try (unfold kPtrArrayReserve, kPageSize, AHI_LO in * ); lia) ] ]
    end.
    transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs _ (_ :: S) Zr _ msF2 _ mo2 Q OK2 VIS2).
    { eapply combined_large_seg2; try eassumption; try lia. all: first [ exact FR1 | assumption ]. }
    cbv beta. intros msF3 mo3 OK3 SBM3 HS3 P3. destruct P3 as (m3 & VIS3 & MU3 & WM3 & MI3 & ST3).
    clear ST2 FR1.
    assert (SHB7 : sh (a + 4096 + size) = sh a + 512 + size8).
    { unfold sh, ASHADOW_BASE. assert (AQ : exists aq, a = 4096 * aq) by (exists (a / 4096); Z.div_mod_to_equations; lia).
      destruct AQ as [aq AQ]. rewrite AQ. clear - AQ SZ; try acb. Z.div_mod_to_equations. lia. }
    assert (LENW' : Z.of_nat (length (wlist (chunks ++ [a]))) = nch + 1) by (unfold wlist; rewrite length_map, length_app; cbn [length]; unfold zlen in LEN; lia).
    unfold AINST in INST2, NRES2, SST2, MTX2, GST2. change (1821656 + 64) with 1821720 in INST2. change (1821656 + 112) with 1821768 in NRES2.
    change (1821656 + 136) with 1821792 in SST2. change (1821656 + 680) with 1822336 in SST2, MTX2. change (1821656 + 688) with 1822344 in GST2.
    change (1821656 + 728) with 1822384 in GST2.
    (* [comment removed for export] *)
    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) in SHT2 by (clear - SZ MQ; Z.div_mod_to_equations; lia).
    senv_at ENV2 MU3 WM3 ENV3. clear ENV2.
    (* Same shape as FR1: transport_after_call drops the poisoned-header shadow over seg2
       (a farm round left exactly u8arr asegs m3 (sh a) (repeat (b8 250) 512)
       unproved on the last line).  Carry every m2 u8arr over by hand first. *)
    lazymatch type of MU3 with
    | munch ?W _ _ =>
        repeat match goal with
        | H : u8arr asegs m2 ?A2 ?xs |- _ =>
            apply (u8arr_transport asegs W m2 m3 A2 xs) in H;
              [ | exact MU3 | exact WM3
              | cbn [disjoint_from]; simpl_sizes; try rx_arr_sizes; try simpl_arr_sizes;
                repeat match goal with |- _ /\ _ => split end;
                first [ exact I | region_decide | slia | (try acb; lia) ] ]
        | H : stk asegs m2 ?loq ?hiq |- _ =>
            apply (stk_transport_disjoint asegs W m2 m3 loq hiq) in H;
              [ | exact MU3 | exact WM3
              | cbn [disjoint_from]; simpl_sizes;
                repeat match goal with |- _ /\ _ => split end;
                first [ exact I | region_decide | slia | (try acb; lia) ] ]
        end
    end.
    transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3.
    apply K. unfold POST, combined_large_post.
    exists a, u0, u1, u2, v2, v4, v5, v6, v7, u3, u4, u5, u6, m3.
    split; [exact AHI|]. split; [acb; lia|]. split; [lia|].
    split; [rewrite <- (same_but_materialized_vmmaps _ _ SBM1); exact FREE|].
    split; [exact OK3|]. split; [exact VIS3|].
    split.
    { apply (la_model_mat _ _ _ _ _ _ mo2 _); [| exact SBM3].
      destruct MO2 as (NV & REST). split.
      - eapply nonvm_same_trans; [apply (nonvm_same_mat _ _ SBM1)| exact NV].
      - rewrite (same_but_materialized_vmmaps _ _ SBM1), (same_but_materialized_eager _ _ SBM1) in REST. exact REST. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. rewrite <- EN.
    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) by (clear - SZ MQ; Z.div_mod_to_equations; lia).
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End CombinedLarge.

End HCW.

