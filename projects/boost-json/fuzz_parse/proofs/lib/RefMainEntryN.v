(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv MuslStrlen
  SymExec SymExec2 SymExec2Sound SymRun SymDrive
  MemSplit RefLayout StartupTac RefStartupDefs RefStartup RefStartupFacts RefMainEntry SymDriveX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SegRead.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefMainEntryN () := KReplay.lz_vm "#%2NC47Corelib7Classes9Morphisms6Proper!sI-Program6Basics4flip!sg?:forall_def!sM?Krespectful_per_obligation_1C46Stdlib9micromega5Tauto5eKindK!sE;8GFormula08!si+5Lists4!s+#6nth_ok!td,4Init5Logic8eq_ind_rK!u&,Numbers7BinNums1Z02!sD=8positive!sK?1N02I45stdpp9bitvector;defini!ur#s2bv00I!tp19Datatypes4list00C!sF;6lengthC5!us&6ZArith6BinInt1Z6of_nat!sF<2leI!v<73and!tE#ELinuxProcessSemantics?!s<23Run?total_arg_bytes!s},!wW%7!s+#Def6F!yD$!t'#!v5?7Z_to_bv!xE72In!xA83notC6!u%JSys2Fs5Namei>path_has_slash!v082eq!v/M2Fs8!sz$eqb!u88tlK!xA;3nat!yK#!tR1Peano2le00K!tl;!|T7;Zify!}A'and_m!}E#!x}34Znat5Nat2Z9is_nonneg!yJ<>pow_po!sND2l!z6=3pow!sC<:!t/#!t'&!y;@;bv_unsigned!us69SatDivModCZ_mod!sz&!u-C6moduloK!}JA1!#4C56VarMap1!x-$!sD>0!sD6=RingM!s4'7!#5-&0!t567Env!sT#5PExpr02!sIE!t{7!t?:1!un<6op!w<#!t>8!#7525!#7x;8B!sJ&!sH6:Z!t^+=Z!sT$CheckerC!vl<4find!sqAC!sq0_sou!sX8!|9/;rew_iff_rev!#8PF!}1C5mkrel!vVF4I!~u@!#8w,!#:K50!~6>6inj_le!#;3?1!#9}<unit!zJ8!u7%4kind!yQ>!sf%1!viG3!#6bM4path!u'=bool!#6-3!sF32!#9$W;dotdot_!tO#!#7p@1!#9D74True!~f8!zw-;!x4%Proof!wC8!}y13Op203!ueB1C!#9O8tC79OSSVerify6!tA$s:boost_json:fuzz_parse3lib8SymDrive9junk_valsC13~~~!slP3Amb7a_hwcap!seV>RefStartupDefs8canary_w!sq%!#7eA2!#B1;3ap!#Fm,!#@K03nth!vGQPropExec4getr!u[&!t';seq!sB<map!whY;nth_map_!t+#!w'U9!sn'X@!xY+_!#EK%!uD&!zU&!#@m,8app_nth!z'33Nat3add!sZ7=!sZ&2_plus!trP6SymRun7!tj$ev!u\V!vL+8blob!sk,K8!skR!xY#23SX23env01!tY&!sl\2!tW'c!uDO=RefMainEntryN3p0N!skd6auxvp!sne4rnd!sle5!xX#!sme2EN!}H3!ze,sub!#6%8ge!#Fp<ge!#DD?1!|;?2!#=TB!t'8!#8Q54!#4PX5v_!}Q#!v/%!#I-;!}t$!#Hb>5bv_eq!#OCAbv_wrap!v,+!uh+divAZ!~_#!#H~#idemp_r!uFY=!t3&64!sr#!xW'!te?@!#Q&%!#Jr,!#>Y85Riscv3Sem5alu6!w7Z7alu!w9-!sjO<!{-/3spx!#3ob6edenot!sm%!#E;=N00K!v3@5Instr!v5#op01K!#XIC1!#6a\4e!#LI#!v]V:!#>x+5me_ra!#8<%!un=Z03!{z=!#31#!#Iv?7!#Jn%!#NhD4!sIE7!xUP=!vQ'Sound4SX2S7u_small!vXesp!#7'c8spxN_va!t\fgp!sjet!sjfs0!sjea!{>fs2!sja8!sj#zero!~u3!#L7,2or!#]%:o!#WA8!#;U+3!#RoE3!#5n\@regs_ok_by_index!~D'!|oC3!uF<1!#bV77and_i!#VSC5mkapp!uF]8all_!uJ#!wU&!#67a0!}qfr_mainN!#6=2!#RG31!#W@Ct!#@jH5!zC85False!#XN?8!t4#succ!t6I1!wmP3Amb5a_ui!#=bV9RefLayout:lay_bsb_n!#Qz%!#XYJ;Stack!sk%Abuild_s!s8#!#kP$!t\P7ArgvEnvBargv_ptr_bounds_at!~d8!#aU40!t>QCat!zW#<cat_!tB'!yf8!t851!#ko9x!tRR!wH,>u_!tV5!uFX?!sn#struct_size!y/`?!so&av!wT%!ssV!#EL'C!#q^1!#r}#!u^]I!su3firstn_l!uha<!wI$str_len!tmW!{,&>rdn_wmem!{w%!sp^4!sl#!}MQ3RunAentry!}E&image!~3W<!sf%to_!tS#!xfX8wrap_!u:,!uzPFileSim@read!|+%c!wb#!vn'!}=78!#j]$fl!#;\A3inj!t[P!#@/,Dmain_!w$%!xW#above!#3C&!#85A5Psatz!#@07!#eY:2!x%K6BvBase;nat!wz#wor!#S;A6b!#T'$!#IOa9w!sl#!~0-!w_76!$%/$!#;r=7inj_iff!#@{8!xF#sym!#A}=3Pol!#syE!wH&4K!#7l:1!v-P3Lib2Nd:and_elimF!#F|WMuslStrlen?!{S$!x&#!#3B/!taV9ex!t`%1!#:w7!$&P,1!~:Y3rdn!x`3!$&T1!#7=$!}BB6!#Ex#2!x$K6!t|/!tu96!#5I#s5Plain1M?loaded_segment!#mK&!zI'5!zH$8!#_N#Na!#gU+!ziB!sI#!tXS5phdrs!#7vP5State<sp_window_hi!sa\lo!wR68!wR#Inst7Inj_Z_Z!#4KM1!#f\^evN_38!v+%!snd9!|8V!#WL6know_ok!sti9k!#8u$!sv'!#\eb2!smc6!t_%05!sok6!soc5sadd!#_7'!t_e7!sok1!}]Q>!#bg#!sE+8store_ok!#UOD5!#`r<mul!#@4ZG!#@4,!tZ'!~e#!{?V!v=1a_base!smc5a_off!|ti4fl!#?b'!sqb6es!v]#!vCe!#iO,!yXZ@!#>C#to_le!#SX%!#<5Aeq!#Au#!#=bW6!#D8#i!u#&!#KpV?!#Ht+ptr_!#VJ'!#?[/!#<J#!{;#!#FQP8!v%$le8!uSY>n!ve&8_spec!#3#%!#@B:!$Cp%1!sGC2!#:Q]9!}S$strN!z$V!#EI3!#7s%!t^^7len_av!#z{d9kn!#F6$!sq&I!#7,c!#agd4keN0!}AQ!#Ao$>!#R^$max!#YC#!tQb!#jyV!{%+9u64_rang!#X/V!$3y16envp!}W+!so_auxv!soX!#Zf&6w!#50$!tYd4pn!uHg:progname!uLYStepTac6u_Z2bv!shXeq!v6#?!#\/#!#]q$hit8!z|'!#8O?8or!$M?%!tAO:!uu&Tac@!tD-out_Z!xH^D!$6l$_N!#:`/!z1eD!#lj#!soe3rb!sl&!#rmE6I!#3>I<MemImageType7S!#P~$!#tX3;Hexadecimal4uint!$Z&-!sH:6!sHD5!sH26!$#4$!t/&!#<w5;of_num_!sG#!viP9StreamSim7wseg!#LL+!tqC!$Hy=prod!#j_Q?!x@,Facts@!#5v#_disjoint_b!td8!tB31!$B1<or!$&@+4Bool!s'$<orb_true!#BL#!#I1;leb!#]`73!#]y/!$bv5!$bO+!sM?@subrel!$bh$!#cw$!sS+!$d81imp!sq@5flip2!sH?F!t;1!tnGI!tb#exive_!s0,proxy!$Wh<leb_le!wV=fst!sC=snd!u9@!tT0per!t[&!sY>B!ul/p!$h=2!sU4NR!t0,artial_app!#78$ism!sa5>!sa+_Prop?or!$Tk#!sW=!t:,D!sO#!xF#_!tr-!wU@!sW#!xV#!s\F?R!sA'!s6%=!sb#!uS+!}Y`<!#7e$_missb!#:s&!x@:4and!}67=!s>#!}7,!sG'!$@&,7!$lI$!$cJ7>!sB&_!s-%!tL2!#}o%proj!#]p^C!#481subN!#:QU!v\;cel!$Qp'!uu7ex!s2#b!|w=to!$j}6!#cg$Z2Nat2id!uu^:!xM$!ul[!$,T/;!ui&non!#FxV!#X^,C!#X^,mem_dat!$</&!#Kjc4!#D[XoreOk?!#Z;-do!#EN%!$/F^kimg_ok!z0g!wE'self!wEmrdn!wE-!ze<7add_0_l!u8`>!tF-t!$/PW!sx3=!}<'!$ZW#!#E`d<!$[H%!#GHZ!uh4!sv/!#L6W!#B73!vb-guard!zbd!vb'!$TN-!tq`?!sw&page!$-wY!#6l:!$`w,!#5j^!#GP#!{\#!$W5ekeN!#[:d5keN!#pD&!t[b3!t[i8!w|V!$?R0kn!$-l%!so%!#;c5:!#`L$_appI!sE66E!#<&#00!uB^;!#sI#!#^D-!ssd!uK$!sse!v>#m!$A1+!#:NP!#ff%5argc!sgW!$JI2!$CPeevN_jun!#Q5%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~k1ccat_argv_ptr69OSSVerify6Proofsaboost_jsonafuzz_parse3libeRefStartupDefs~~~~~~oa6auxv_w3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutt4dat_random_ptr37Corelib4Init9Datatypeshh84listhh84conshh83apphh83nil79OSSVerify6Proofsaboost_jsonafuzz_parse3libdRefMainEntryNaMainEntryN~~~~~~hke3p0N69OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Amb~~~~~~hq07a_hwcaphke6auxvpNhke4rndNoa8canary_w69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~hve9junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ik63envhke5valsNhve8blobs_evik63Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~iq87vals_evik64exprik64EVarik64ELit69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMainEntry~~~~~~jg43spxik66kentryik66KRangeik62SAik66KAlignik65KWordik63KWrjg48kn_imagehke9kn_stackNhh86length37Corelib4Init5Peanojq12le37Corelib4Init5Logicjrb3andhh83natjrb2eq37Corelib4Init3Natju33addjq12lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~kg24getrhke2ENik62ev46Stdlib6ZArith6BinInt1Zkl16of_nathf7Z_to_bv01Zik66edenotkl13addhfbbv_unsignedhke8sr_mainN79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~kqb7regs_ok37Corelib5Lists7ListDefkvb3nthkl12lehh84Somehh86optionkg23rdn69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~lj8floaded_segmentsjrb2exkqb7know_ok3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelp27Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticslt2h0word_to_le_bytesoa6D_main37Corelib4InitbHexadecimalmi72D0hh84boolhh84truemi72D1mi72D4mi73Nilju3bof_num_uint37Corelib4Init6Numbermn9fUIntHexadecimal69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~mq17wseg_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefStartupFacts~~~~~~mu8h0range_disjoint_bhh84prodmu8cD_main_missbik64KImgkqb9kentry_okkl13subkl16to_nathke8kn_mainN69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ArgvEnv~~~~~~no95argcNt49EntryDraw3h5LinuxProcessSemantics5Riscv7Preludent85bvmap3h5LinuxProcessSemanticsfLinuxProcessSem3Runog7avalid_argvog7avalid_envpog78valid_spkl12ltkl13pow69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefStartup~~~~~~om8amain_entrymi72D3" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MainEntryN.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  (* LPS-revision port, MIRROR of the ported Section MainEntry in this unit's own
     farm-GREEN RefMainEntry.v (:78-121).  main_entry gained the ProcInput, the mmap base
     and the entry point (RefStartup.v:101), and av/envv are now read OFF the input, so
     this section gains `inp`, `mbase`, `entry` and the two bridges Hargv/Hve'.  Both
     bridges are reflexivity where MainOpen and MainTop build inp with mkProcInputC. *)
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable rdraw : ltac2:(zQ "10!nsc$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!nve!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!h9!jc!li7>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Hypothesis Hva : ltac2:(zQ "10!oj3@1$0?2av").
  Hypothesis Hve : ltac2:(zQ "10!ok1@1$0?4envv").
  Hypothesis Hvsp : ltac2:(zQ "10!okf@1$0?3sp0").
  Hypothesis Htid : ltac2:(zQ "50!h9!olb!kp1!jsf!om1@2$3@2$1Z@2$2@1$0#k0?3tid@2$1@2$2@1$0#k0?3tid@2$4+2+h6").
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = envv.
  (* The encoded ME held the pre-revision 7-argument
     `main_entry sp0 av envv rdraw tid regs mem`; a blob is never re-encoded, so it is
     written out (rule 11). *)
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  (* LPS-revision port, MIRROR of the landed plain twin's Section KnowProofs
     (RefMainEntry.v:385-418), whose comment records the About probe
     a farm round these argument lists are read off:
       lay_bsb_nw          v inp mbase ph entry sp brk rdraw Hvl Hlau Hsp_hi
       argv_ptr_bounds_at  v inp mbase sp brk draw Hlau k Hk
       u_cat_argv_ptr      v inp mbase ph entry sp brk rdraw Hvl Hlau Hlo Hhi k Hk
       struct_av_bound     inp mbase ph entry sp brk rdraw
       argv_str_len        inp Hva k Hk
       read_argv_cstr_k    v segs inp mbase ph entry sp brk draw k Hlau Hk
       read_word_stack     v segs inp mbase ph entry sp brk draw k m Hlau Hk Hm Hnw
                           (MuslStrlen.v:655-664, read there)
     so this section gains `brk`, `Hvl` and `Hlau`; `v` is Sv48 and `ph` is RPH, as the
     plain twin's header explains.  `Hhw` is the same AT_HWCAP bridge: both new
     hypotheses are discharged by the layer above -- MainOpen and MainTop build inp as
     `mkProcInputC [a0s; path] envv fs0 stdin0` (Amb.v:36-40), where in_hwcap inp IS
     a_hwcap, and `valid_launch` / `entry_launch_ok_va` are already conjuncts of
     valid_input and a Hypothesis of ref_startup (RefStartup.v:132). *)
  Hypothesis Hhw : in_hwcap inp = a_hwcap.
  Variable brk : word.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  (* The stack readers state their argv premise over the ProcInput, where this section's
     `Hva` is over `av`; Hargv is exactly the bridge. *)
  Lemma kvaN : valid_argv (in_argv inp). Proof. rewrite Hargv. exact Hva. Qed.

  (* LPS-revision port, written out rather than re-encoded (rule 11), and the same three
     tree-local signature moves the plain twin's Section MainEntry carries:
       cat_argv_ptr gained execfn and its base is the DRAWN top (CatExec.v:258-260);
       auxv_w is exported over the ProcInput (RefStartupDefs.v:60);
       at_random_ptr gained the rseq flag (RefStartupDefs.v:68's own rnd_w).
     kb_rseq is read from the run and never pinned. *)
  Definition p0N : word := cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0.
  Definition auxvpN : word := auxv_w inp sp0.
  Definition rndN : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av envv.

  Definition valsN : ltac2:(zQ "30!hj0!h9!jc@1$0@1$2@1$1#k0") := ltac2:(zQ "b0!h9!jc!hj8!hk0!hk7!hp9!ht6!hu1!hub!hv3!ij9@3$3@1$1@1$0#k0@3$2@1$1@1$0#k0?3sp0@3$2@1$1@1$0#k0$5@3$2@1$1@1$0#k0$5@3$2@1$1@1$0#k0$7@3$2@1$1@1$0#k0$8@3$2@1$1@1$0#k0?3tid@1$4@1$1@1$0#k0@3$3@1$1@1$0#k0@1$a?4regs@3$2@1$1@1$0#k0@1$6?3AMB@3$2@1$1@1$0#k0@1$9?5rdraw@1$4@1$1@1$0#k0").
  Definition EN : ltac2:(zQ "10!io5$0") := ltac2:(zQ "80!hj0!hk7!h9!ioc!ip5!iq1!iu1!jc@2$5@1$6$3@1$4@1$1@1$0@1$7@1$2#8").

  Definition sr_mainN : ltac2:(zQ "20!hj0!iuc@1$0$1") := ltac2:(zQ "60!iuc!hj8!iv4!ivc!jk3!hk7@3$1$0@1$3Z@3$1$0@1$3+tqgsc@3$1$0@1$4-j0@3$1$0@1$3+hgog0@3$1$0@1$3+hgrmr8@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$4+8@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$4+8@3$1$0@1$2Nh2@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$3+knjt0@3$1$0@1$2Nh9@3$1$0@1$3Z@3$1$0@1$3Z@3$1$0@1$3Z@3$1$0@1$3Z@3$1$0@1$3Z@3$1$0@1$3Z@3$1$0@1$3Z@3$1$0@1$3Z@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@1$5$0").

  (* LPS-revision port, written out rather than re-encoded (rule 11), and the SAME ONE
     CHANGE this unit's landed plain twin had to make to kn_stack (RefMainEntry.v:134-155):
     the encoded KWr claimed the stack write window as [sp0 - 8388608, sp0), i.e. everything
     from sp0 - stack_max_size.  THAT IS FALSE AT THIS REVISION -- the model certifies
     writes only from MemSplit.wok_lo sp0 = bv_unsigned sp0 + stack_window_reach
     - stack_max_size (MemSplit.v:137-138), which is 2,244,095 bytes higher.  The window is
     written SYMBOLICALLY, never as the literal 6144513, so it tracks the model.  Every
     other entry is the encoded one unchanged, in its encoded order: align 16; the sp0
     range; the KWr; p0N's word at offset 8; p0N's range.  Measured, not inferred: without this the
     store_ok bullet's trailing lia answers "Cannot find witness"
     (a farm round, line 261). *)
  Definition kn_stackN : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (stack_window_reach - stack_max_size)) (stack_max_size - stack_window_reach);
     KWord (SA (EVar 0) 8) 8 (EVar 1);
     KRange (EVar 1) 0x7fff80000000 0x800000400000].

  Definition kn_mainN : ltac2:(zQ "20!hj0!jka@1$0$1") := ltac2:(zQ "40!hk0!jne!joa!jka@3$0$3$2$1").

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Lemma len_avN : ltac2:(zQ "60!jp7!hj0!jr5!h9!jc!jsf@2$5@2$2N1@2$0@1$1@1$4@1$3#8?2av@2$2@2$0@1$1@1$4@1$3#8?2avNkg0").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "##:eh01ah12Hah24__x1h31Hh42H1h52H2h62_Hh77__arithh84__ffh96__sat3h:!s/%4h;!s/%5h<8__varmaph=5__with>4cstrh?1vp;1p;2p;3p;6p;4p;7p;<p;8p-1R0p10000p4p710p9P!s6%SR1!s8,P!s2$2!s3/31!sS,11!sc11X!s6'g002PR!t&%1g002o!s}%3101p8p1003S!sR&1003n!s2&8g004Lj17Tg004jj18Tg005Oj1=!s/$mj1jTg006Pj1ATg0070j2G!s/$PR2j1?Tg0080R3j23!s1$LR4j25!s1$gj1KTg009cj3;Tg00:Dj2i!s/$jj3cTg00;Aj1^!s/$Zj1[Tg00<^j3:Tg00=8j2X!s/$lj2WTg00>Cj10!s/$bR5j2@Tg00?<j29!s/$Vj6MTg00@?j1L!s/$dj2JTg00ALj2>!s/$hj2ITg00BEj3O!s/$ij2PTg00CSj2HTg00DDj2T!s/$dj1UTg00EDj2h!s/$bj1gTg00F@j1f!s/$kj2bTg00GNj2ETg00H1j4C!s/$\j1]Tg00I>j7\!s/$bj2ZTg00JDj2_Tg00K0j3Y!s/$Oj4`Tg00LAj4a!s/$lj1FTg00MQl<dTg00N6j7eTP1j8VTf0R1#8#8p=2%F1#Fp=4%01#0p=S!s-$#0#0p=R!s2+!s$'p=Q!s:4!s$3p=N!sJD!s$Cp=1g00NZg00O9R6P5P2P3g00OWf5f4f3R3f2R2f1R5P1M<dp=<g00P9R7/31p=6P5P0g00PWR8P8g00Q7R9P1g00QWFep=DP3P0P8P8P9P2P5P1GVp=Bp,3Hvag00R7R3#7R:%83R;#2R<#=R=#jR>#AR?p,2avR@'GRA#?RB'3RC%8<R<#2RD#2#2RE#7RF,3BRG'5RH%K@%8E#2!s$+7'31G>1#?%43#4!s$07'3X0?=;?@1i=7=c>1#^!s7&g00R\R>g00SLR=%[1g00SlRE3:g00TL,X1=:=E'5X0>1W?@3;'5'5'5R@'5P4PHP@g00UM#0R?/@AR>%0?#S#R#Q#N#1!s$_RE,@ARI'5RJP1P4PCPGPJ\@P1PJPHP>PI!s8$?P:196:PAPB196BR?E<PAPBP?PEPF196FE<EM%LA%6B%7;RA%4;#8#7R;'J1>7A%6;1IA;RE,>7[[%6AR?g00UlRIAOA;5UW1%6E\I^1?%=Dp,3sp0'PRD%7<R<'H%6D%6<1TD<#6[[g00VHR<#U%A<1h65%g6%f6R<P61b63R3g00W4RD1E6FCC,D<R?%]8RIP<P61E6:PDP3!s>%3PIP<!y\+3P?F\CBCB1Z<9P1P2g00W[R<,9=1_12=:=<dAY675C`b8b<b=X26131F13:513:2132F'5[[^26P1PBf6f7O3b7b9b:b;b>CaX6@X5GX4CP5P1O2n200100001012!s/$00X3H!sC=b?o"). Qed.

  Lemma evN_junk : ltac2:(zQ "b0!h9!jt6!jtd!jv5!jvc!kjd!kk5!kkb!km9!kn3!jc>1i$1>0@2$4^1Ni0@3$2@1$a@1$0#k0@2$7$6@2$3N6^2@2$5?4regs@2$9@1$0#5@1$8^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "##0+h01ih12Hih21bh31np;2p;1p;3p;4p;6p;5g00X;j2<Tg004jj14Tg005Oj1:!s/$mj1BTg00XSj1PTg00YYj1KTg00ZXj1ITg00Ddj1ATg00[cj30Tg00\Cj3;Tg00:Dj27!s8$`j46Tg00Llj1RTg007Pj19Tg00]<j28Tg00<^j33Tg00?<j2QTg00^=j2O!s/$Yj4NTg00_5j6MTg003nj65!sn$0j2?Tg00`=j1JTg00aKj6H!s/$hj2=Tg00b?j5G!s/$aj2>j1FTg006Pj1LTg00ccj1ETg00dhj2DTg00enj2@Tg00>Cj12Tf0R0#2#2p=C%2!s0$#2p=1g00NZR1g00UMR2#C#1R3#C#1!s$,R4,<0g00R7#4R5#4#4R6#4!s$$:R7#BR8P8f1R9p,4regsR:#PR;p,3AMB#Kp,5rdraw#I%A8R<508508R=5;8R>g00P9,77R7C6R?%R5#:R5f2R@#9'7,8:9380X28RAP8P8P9P;P7C6RBPAP8%99,75,8:RCPA1Q8C!sG$1P8%90!s?%X01R51O24CNP7C6P8P5P9P4P7P0EME5A38BCeP?P8P;P=P7!sd$41<@0X31P01?8;%J:E5EHE5P8p,3sp0g00g1R:g00h6g00i>p,3tid=08!uN&908:!uX&:,?8/=9R<A;8:>R;!tR&:P>P7P9DGE51>;<=38Ceg00jDR;1=39R9'>!s:$%F;%:6#B#L#A#E'D/@9!sR'kK!s3'W1W0o"). Qed.

  Lemma evN_38 : ltac2:(zQ "60!jtd!h9!ht6!kk5!kkb!jc@3$0@1$5@1$1#k0@2$4$3Ni6@1$2?3AMB").
Proof.
ltac2:(KReplay.run1 (kr_t_RefMainEntryN ()) ["MainEntryN"] "h01nh17__arithh24__ffh38__varmaph45__with51bp;1p;3p;2p;4p;6p;7p;5p;<g004jj12Tg005Oj1?Tg005mj1:Tg00XSj1\Tg00YYj1XTg00ZXj1VTg00Ddj17Tg00[cj31Tg00\Cj3>Tg00:Dj2DTg00\`j45Tg00<^j34Tg0070j2@Tg00lOj2=Tg00?<j28Tg00`=j1WTg003nj66Tg00lfR0j29Tg004Lj1UTg00m>R1j2TTg006Pj1;Tg00mZj1JTg00Ebj1ITg00F@j1FTg00GNj2GTg00H1j4HTg00N6j7ETg00Ibj2KTg00JDj2LTg00K0j3CTg00KOj4MTg00LAj4NTg00n8j6BTg00ahj2OTg00b?j5PTg00baj2Rj1STg00ccj1[Tg00dhj2ZTg00enj2<Tg00>Cj13Tg00MQl<YTf0R2#3#3#3#3p=0g00NZR3g00O9R4P0g007PP1g00nUf5f4f3f2R1f1R0P2M<Yp=Q%32#3p=Ag00R7#2#2#2R5#2#2R6#2#?R7#:R8P8g00UM#0#0#0#0#0#0#0#0R9p,4regsR:#\R;p,3AMB#XR<p,5rdraw#V%78R=518518R>5>8R?g00P9R@,D7R7C5RAA482<X58RBP8P81@8;RC,=9P>P7C5PBP3P9P81=92P>P7C5=48<X03188<PC%W:R:E6PAP8P;P>P7P9P3P91992X031999%U6R6/T6R3P9P61846R>P9P6P>EQg00VHR>#7%;>%J4%I4%F4R>g002Pg00PWR;P;g00Q7R;P41G46R6g00o7P6CHg00QWFE1K>;P2P1g00SLR;g00W[R>'81L21=4;>dAC4@0CMb2b3b4P3P2b1CNPCP:E6EBE6P8p,3sp0g00g1R:g00h6g00i>p,3tid=18=518518918:518518R:,@8/O9A>8:?P7C5P8P:P?P7P9DPE6g00jDR7%A9#0R9'R=48<e%S7%?5#:#;#7#['Z/<9=48<eg00kK/<9=48<eo"). Qed.

  Lemma evN_39 : ltac2:(zQ "60!jtd!h9!kk5!hv3!kkb!jc@3$0@1$5@1$1#k0@2$4$2Ni7@1$3?5rdraw").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "##2}h01nh17__arithh24__ffh38__varmaph45__with51bp;1p;3p;2p;4p;6p;7p;5p;<g004jj14Tg005Oj1B!s/$mj1=Tg00>Cj12Tg00XSj1XTg00YYj1VTg00ZXj1NTg00Ddj18Tg00[cj31Tg00\Cj3<Tg00:Dj2D!s8$`j47Tg00<^j33Tg0070j2@Tg00lOj2?Tg00?<j25Tg00`=j1WTg003nj66!sJ$fR0j2>Tg00Llj1UTg004Lj1:Tg00m>R1j2MTg006Pj19!s:$Zj1JTg00Ebj1ITg00F@j1HTg00GNj2;Tg00H1j4GTg00N6j7KTg00Ibj2FTg00JDj2ETg00K0j3O!s/$Oj4P!tN$Aj4QTg00n8j6RTg00ahj2CTg00b?j5S!s/$aj2]j1\Tg00ccj1[Tg00dhj2ZTg00enj2ATg00MQl<YTf0R2#!s$&p=0g00NZR3g00O9R4P0g007PP1g00nUf5f4f3f2R1f1R0P2M<Yp=L%2!s`$Tg00R7#4#4#4R5#4R6#4!s6$BR8#=R9P9g00UM#0!s$1R:#2R;p,4regsR<#XR=p,3AMB#Vp,5rdraw#NR>%89R?519519R@5<9RAg00P9RB,D8R8C7RCA392>X59RDP9P91@9=RE,?;P@P8C7PDP3P:P91?;2!s8%=39>X03159>PE%W<R<E6PCP9P=P@P8P;P3P:1>;2X031>;:%U6#:R6%:7R7'MR3P;P61546P:P71547ELg00VHR:#8%9:%J4%I4%H4R:g002Pg00PWR@P@g00Q7R@P41;46g00o71;47CGg00QWFK1F:@P2!w4$SLR@g00W[R:'51E21=3@:dAO4B0CPb2b3b4P3P2b1CQPEP<E6ERE6P9p,3sp0g00g1R<g00h6g00i>p,3tid=19!vb&919<!vl&<,@9/C;A<9<A!vI$9P<PAP8P;DSE6g00jDR8%T;#0R;']=39>e%\8%B5#=#9#8#['Z/A;!s>$g00kK!s3'o"). Qed.

  Lemma spxN_val : ltac2:(zQ "a0!h9!jtd!knd!jk3!kk5!ko0!koa!kn3!jc!kp1>1k$2@3$1@1$8@1$0#k0@2$5$4@1$3^1@2$7@1$0#k0@2$6@2$9@1$0#k0?3sp0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_RefMainEntryN ()) ["MainEntryN"] "h01zh12b1h22b2h31nh41Hh51bh61kp;1p;2p;3p;6g004jj17Tg005Oj1HTg005mj18Tg00enj2?Tg00:Dj29Tg00o^j2ETg00Bij20Tg010`j22Tg00<^j36Tg011=j3>Tg011aj24Tg004Lj1<Tg00Ahj2GTg00DDj23Tg00?<j2FTg012Gj3DTg012nj1;Tg0148j2:Tg014gj3CTg015Oj2BTg003nj6=Tg016Sj1ATg017Wj2@Tg00O9R0f1R1f0R236p=1P0f4R3f3R4f2R5P1P2E=p=5g00R7#7R6#7#7#7#7#7R7#HR8#8R9g00kKR:g00UM'?R;1982R<'ER=p,3sp0,08R>/21R?,98R@9692X59g018^RA%82RB%81RCg008L%85?61210451041'1RD[10511052'1%84?651[RE%83?645\DA>512P2n2001000000120000000W2W1W3PE^2C^1B^3AP2P81981,08RA,2>RB,98RCP@148B12>5RE,98,08RD,12X001481R412>2R3,48/1DX00148?RD1485,2>,48/12X0012>4RF%<6%<7'GR7'3148ER6,12X001317RG1337/16X0013?7R61357,2>/37/12X00P613E7,12X001F0612>G/37AD1>7D5PD%;?D5P4%;1D5148F%;FD5108@1:8?D5PA1:81D5108C1:8BD5O4b41983R3969=eg019<?C;<1B;<E=%A2,@:=693eX60o"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac reg_caseN :=
    cbn [nth sr_mainN all_regs];
    first [ rewrite spxN_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot EN (EVar n)) with (ev EN n);
              first [ rewrite (evN_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact (me_ra _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ _ _ ME); cbn; tauto
          | idtac ].

  Theorem main_regs_okN : ltac2:(zQ "30!kk5!kpf!kv0@3$2$0$1?4regs").
Proof.
    pose proof Hlo as HloA. pose proof Hhi as HhiA. pose proof Hal as HalA.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* LPS-revision port, written out rather than re-encoded (rule 11).  The encoded
     statement applied the pre-revision `cat_argv_ptr sp0 av envv k`; CatExec.v:258-260
     gives it the DRAWN top as base and an execfn argument, exactly as the landed plain
     twin's main_str (RefMainEntry.v:793-797) states it.  Nothing else moves: the same
     five conjuncts, the same 2107576, the same 131071, the same trailing 8-byte read.
     Tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntryN.v:135-155, with every
     argument list re-threaded to the revision's generalisation sets (Section header). *)
  Lemma main_strN : forall k, (k < length av)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z   (* [comment removed for export] *)
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) + Z.of_nat (length (nth k av []))))
                         8 = Some t8).
Proof.
    intros k Hk.
    pose proof Hlo as HloA. pose proof Hhi as HhiA.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Hargv; exact Hk).
    pose proof (lay_bsb_nw Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                  ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (argv_ptr_bounds_at Sv48 inp mbase sp0 brk rdraw Hlau k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                  ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound inp mbase RPH entry sp0 brk rdraw) as Hsb.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (argv_str_len inp kvaN k Hk') as Hlen.
    pose proof (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k Hlau Hk') as Hr.
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
    (* The stack image's LENGTH bound (RefLayout.v:387, length <= 2101782).  The span
       bullet needs it, and so does the trailing-word bullet's `rdn_above` side goal
       `bv_unsigned a + 8 <= 2^64`: scoped inside one bullet it left the other with
       "Cannot find witness" (a farm round at the span bullet,
       a farm round at the trailing word), so it is posed once here. *)
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl.
    rewrite <- Hargv, <- Hve'.
    repeat split.
    - rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME)
        by (first [ exact B1 | lia ]).
      rewrite Hw by lia. exact Hr.
    - exact B1.
    - lia.
    - exact Hlen.
    - destruct (read_word_stack Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k
                  (length (nth k (in_argv inp) [])) Hlau Hk' ltac:(lia) Hnw) as (t8 & Hl8 & Hr8).
      exists t8. rewrite w_add_nat in Hr8.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME)
        by (rewrite u_small by lia; lia).
      rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
  Qed.

  (* LPS-revision port.  MainOpen's path_facts carries a conjunct main_strN does not:
     how far the argv string's END is from the top of the user address space.
     PRE-REVISION that came from `build_stack_bytes_within_span` (the block fitted
     inside `Run.entry_stack_span`, hence inside `sp0 + span <= 2^47`); 75d69e00 DELETED
     that lemma and says in its own words why it is FALSE for the kernel's block
     (PropExec.v:1839-1844: an `arch_align_stack` pad near 4095 makes the real block
     longer than the span).  The replacement chain is the model's own:
       bsb_len_lower          cat_string_off + TAB(argv) + 8 <= |image|   (MuslStrlen.v:604)
       total_arg_bytes_firstn_within                                      (CatExec.v:204)
       length_entry_stack_image_launch  |image| = ed_top - sp             (PropExec.v:1846)
       entry_page_top_within_window     ed_top <= va_stack_top Sv48 = 2^47 (PropExec.v:2327)
     i.e. the argv strings are followed inside the image by the envp strings, the exec
     file name, its NUL and the eight-byte VMA-top slot, and the image ends AT ed_top.
     THE MARGIN IS 8, NOT 17.  Measured, not inferred: the pre-revision `+ 17` is FALSE
     at this revision -- at ed_top = 2^47 with envp = [] and a one-byte execfn
     (State.v's `default_execfn`) the last argv NUL sits at 2^47 - 9, so `+ 17` asks for
     2^47 + 6, and `Run.entry_stack_fits` does not exclude that corner (it bounds
     sp + span from ABOVE, and under the launch sp + span <= ed_top - 274 already).
     8 is exactly what the consumer needs: RefOpenFailCS.ref_cannot_open,
     RefReadErr.ref_read_error take `bv_unsigned pp + length path + 8 <= 2^47`. *)
  Lemma str_fits_N : forall k, (k < length av)%nat ->
    (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k)
       + Z.of_nat (length (nth k av [])) + 8 <= 0x800000000000)%Z.
Proof.
    intros k Hk.
    pose proof Hlo as HloA. pose proof Hhi as HhiA.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Hargv; exact Hk).
    pose proof (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                  ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (bsb_len_lower inp mbase RPH entry sp0 rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk') as Hw.
    pose proof (length_entry_stack_image_launch Sv48 inp mbase RPH entry sp0 brk rdraw
                  Hlau) as Hlen.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp0 brk rdraw Hlau) as Htop.
    unfold entry_page_top, va_stack_top, sp_window_hi in Htop.
    rewrite <- Hargv, <- Hve'. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma keN0 : ev EN 0 = sp0.
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "###op;1p;2g004jj10Tg005Oj13!s/$mj12Tg00?<j21Tg00R7#0!s$-3#2p,3sp0'1o"). Qed.
  Lemma keN1 : ev EN 1 = p0N.
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "###np;1p;2g004jj10Tg005Oj13!s/$mj12Tg00?<j21Tg00R7#0!s$-3#2g00g1'1o"). Qed.
  Lemma keN3 : ltac2:(zQ "60!jtd!h9!kk5!hu1!kkb!jc@3$0@1$5@1$1#k0@2$4$2N3$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "###np;1p;2g004jj10Tg005Oj13!s/$mj12Tg00?<j21Tg00R7#0!s$-3#2g00h6'1o"). Qed.
  Lemma keN5 : ev EN 5 = tid.
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "###op;1p;2g004jj10Tg005Oj13!s/$mj12Tg00?<j21Tg00R7#0!s$-3#2p,3tid'1o"). Qed.
  Lemma keN38 : ltac2:(zQ "60!jtd!h9!ht6!kk5!kkb!jc@3$0@1$5@1$1#k0@2$4$3Ni6@1$2?3AMB").
Proof.
ltac2:(KReplay.run1 (kr_t_RefMainEntryN ()) ["MainEntryN"] "g02?To"). Qed.
  Lemma keN39 : ltac2:(zQ "60!jtd!h9!kk5!hv3!kkb!jc@3$0@1$5@1$1#k0@2$4$2Ni7@1$3?5rdraw").
Proof.
ltac2:(KReplay.run1 (kr_t_RefMainEntryN ()) ["MainEntryN"] "g02@\o"). Qed.

  Lemma know_stackN : ltac2:(zQ "40!kk5!joa!lo7!lme@4$2$3$0?3mem$1").
  (* LPS-revision port, written out rather than re-encoded (rule 11); the STATEMENT is
     untouched.  The replay applied the pre-revision `cat_argv_ptr sp0 av envv 0` and the
     pre-revision stack readers.  Shape from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntryN.v:167-186, with the
     argument lists and the two window unfolds taken from this unit's own landed
     RefMainEntry.v:449-524: at this revision the KWr window is symbolic, so lia must be
     shown stack_window_reach and stack_max_size, and main_entry_store_ok_win's lower
     bound is MemSplit.wok_lo (MemSplit.v:137-138). *)
Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof Hal as HAL.
    pose proof len_avN as Hlen.
    (* p0N's KRange entry is bounded by main_strN's own second and third conjuncts, which
       are stated about exactly `cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) 0`;
       without them the last bullet's `lia` has no bound on p0N and answers "Cannot find
       witness" (a farm round, line 287). *)
    destruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
    unfold kn_stackN, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?keN0, ?keN1;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
    - split; [lia | exact HAL].
    - lia.
    - split; [try unfold stack_window_reach; try unfold stack_max_size; lia|].
      intros d m Hd Hm.
      apply (main_entry_store_ok_win inp mbase entry sp0 rdraw tid regs mem ME);
        rewrite u_small by (try unfold stack_window_reach, stack_max_size in *; lia);
        try unfold MemSplit.wok_lo, stack_window_reach, stack_max_size in *; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME)
        by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw kvaN Hvl Hlau
                    ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat
                    ltac:(rewrite Hargv; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      rewrite Hargv, Hve' in Hr.
      rewrite Hr. unfold p0N. rewrite n_to_le_8_spec. reflexivity.
    - unfold p0N. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvpN : forall segs,
    rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12b950) 8
    = Some (word_to_le_bytes 8 auxvpN).
  (* LPS-revision port, written out rather than re-encoded (rule 11); the STATEMENT,
     including the address 0x12b950, is untouched.  The replay applied `envp_w sp0 av`
     and the pre-revision 6-argument D_main; RefStartupDefs.v's Section Defs now exports
     envp_w/auxv_w over the ProcInput and :191 reads `D_main inp sp0 rdraw tid`.  This is
     the same lemma at the same address as this unit's own landed D_main_auxvp
     (RefMainEntry.v:671-688) and closes the same way: auxvpN unfolds to auxv_w inp sp0,
     and RULE 15 -- boost-json's D_main is D_cxx (not beast's D_cx), RefStartupDefs.v:181. *)
Proof.
    intros segs. pose proof (u64_range tid). pose proof Hlo. pose proof Hhi.
    unfold auxvpN, auxv_w, D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)

  Lemma wseg_dataN : ltac2:(zQ "e0!mk1!mk7!mkf!ml7!mld!mm3!jtd!mma!moe!h9!mtd!lme!kn3!or3@3$6$1@3$a$b@2$c@1$9#k0+vpgg0@1$7@1$8@1$d@1$4@1$0@1$0@1$0$5$2").
Proof.
vm_compute. reflexivity. Qed.   (* [comment removed for export] *)

  Lemma range_disjoint_subN : ltac2:(zQ "a0!knd!mk7!jt6!mkf!jtd!nia!koa!lh9!njf!km9>2lo$0>1n$2>1c@2$8$0$2>1i$0>0@3$4$1@3$5^4^3^2$3>0@2$7^5^2>0@2$7@2$6^3+1@2$6^6@1$9^5@3$4$1@3$5^4N1^5$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "##H^p'0h01Hh12b1h22b2h35lemmah41xh52H0h62Hah74__x1h84__x2h94__x3h:4__x4h;4__x5h<4__x6h=1ih>1ni001nh?1yh@1AhA1BhB4Hhi'hC4Hlo'hD7__arithhE4__ffhF6__sat1hG!s/%2hH!s/%3hI8__varmaphJ5__withK1chL2c0hM4cstrhN5cstr0hO2lohP1mhQ1wi011pi021zp&0p;2p;3p;1p;4p;8p;<p;6p;=p;7p;;p;Bg038BR0k20:Tg038bj3HTg0080R1j20Tg004Lj1BTg010`R2j21Tg007PR3j13Tg00>Cj1ATg03:6j4X!s/$Vj2CTg01I5R4j24Tg03;3j2a!s/$Sj2;Tg03<0R5j2K!s1$Ij4JTg000Sj4}Tg03=0j2y!s/$]R6j2uTg03>;j4s!s/$]j8PTg03?Pj3nTg03@Fj2ITg01iNj1d!s/$lj4cTg00?<j2=Tg00MQl<_Tg02U?j3^Tg02m@j6]Tg00@?j1Q!ua$jj15Tg00Llj1:!sA$dk209Tg00ALj2\!s/$hk208Tg00BEk307Tg005Ok10!s`$Bik204Tg00CSj2|Tg00DDj2{Tg01kbj2@Tg028^j3DTg01lKj2W!sJ$dj1xTg00[cj3VTg006Pj1tTg00EDj2MTg00mZj1r!vv$ij4G!sA$bj1qTg00F@j1p!s/$kj2>Tg00GNj2UTg01L<j3NTg00H\j1oTg00Ibj2mTg00JDj2lTg00K0j3v!s/$Oj4w!uw$Aj4k!vy$fj3jTg03ACj3zTg00<^j3Y!s8$`j4iTg03BSl=~k700Tg03CBm;01Tg01MVm<02!uf$8lBg!tR$1j4fTg00N6k703Tg032Vj7eTg002ok806Tg00SLR7f0R8g00W[R93Yp=2p-0R:f1R;P5P8CJp=LP:f4R<P5P5f3R=f2R>P;P8GPp=T1;;8=Y79p=7P:P5P;P8Cip=FP8P;P4g03D=R?P>g00QWR@P=P<f5RAf6RBf7RCf8RDf9REM=~p=RP:!si$5P8P5P6g03DnGPp=hP=P>P4P?P;P@P8K00p=ZP:PCP5PBP4PAP<!sH$;P8N;01p=[g00NZR4g00O9R?P?P?P3P3!sO0<02p=b!sA$!s$'2!u&$>P2P=P<PAPBPCPDPEMBgp=`g00P9R2/08p=6%58#5p=OP?P;g00W4P8Cfp=<!s4$2PR3g00PWRFPFg00Q7RGP8P@K03p=8P>P3PFPFPGP;P8Fep=S%:8#:p=?!s|$#5#5p=9P=!sM+!t~$L06p=E20:?4P0P?P4AH<=;#210A;R0g00R7R3#BR@,1>RH%3A,1BRI'0g00UMRJ#ARK=H=<#2[[[^=?P8P?P4P>P;CX9HCB#210D;%3D,1ERL,0Hg008LRH1C;8#2%2>RM%2;RN'4RO[RP%28,4N1C>;#2RN[RQ%2=/4M\N1a;8RNP;n20010!s#$12!s-%0X27X17PP^27^17P8f;RMf:RR#3RS'1/;BRT1;IMRIP=O3%2T%2I'4PHPPPQ1C=>#2\OPNP8!t%>Q!t%'%3KRQ,1BRN/;DRO%3C,1DRP/;B%2O10ND'KP:^A:RO^@:RHP:\:!z:'CJRI'LRT!s6&!s>%6C}RUCJRV,LORWPO1y:5RXPIPV!zq+XP5PUP:P51u8;X?:X4:g03E_CsGPDTRU11CQRY/7E10YEP817LCRYPYg03FU9n:5RZ/FYM:RW31INDf=RNf<R[#3'1R\/7D10\DR]'KPHP!ti'6CJR6,LOR5POPXPIP6%hXDTRXf>RI%3N'1RH!t>$HERH!t@$IR^P^1FZ^!t6&\DP;O217PN,4]10LC,KYPOPVPO\:RVPTPWPUCZ11DQRU/0RRW1FZW%3E,1RRE!tc$EDRYP8G[W31ILC10LIR],K^POP6PVPTP5PXCZf?RX%3IR5'1/0RRT1FZT17EX10EX!sc+IP8O214H]14WYR]11D@RH/0RRL/4YPWPYPLPY!}]$1P8X4?RLP110;8#dX??X4?PUPHPL!s$$?P?g02>D11;8Cc,=?XP?X>?PDPD1=?DPQP@PLPL%38,=?X44PKP@1=?@EbM:`PRPR1=?RM<_1=:Y9^YYE]%QI%65%QR%6S%53RS#BRR%:SR5#:#5#BRY+091\2R%6Y208RYR:,\2[[%6RRLg00UlRDB07RY;UW6%6:\D^6L%OSRL#5RD#O$05p,3sp0+04R:%BDRD'|%6:%6D1{:D#6[[g00VHRD%AK#ARY#ARR,@?1@?YRY1@?J5D?5D!um$hRJ'W%A!sE&K9D?Y5D?/WJ%xD5VD3V%tD!vf$?1M?BPB%r?RDCGP>PDCGP;!s=$<P=1M?ACGCG%q?%p?RD1>?3RJ1U?@5N?RY%:3R3#:RR,>?RH1>?L5N?RL'<,8D%oFRFPD1<HJ,8DPFPD1>?SRS,<L,8!so$9N?SR3/<H,8D5S!sI$%:R#?!s$-5#O#9!s$0BRR,U?1>?5!t4$PF1<YS,8D1<3J!sn%CE!s$%1mDGP8P>1=791l8>#2dAv?2;CwbEbIbJX7?X8?X9?X:?X;?X<?118@11<A'011BC/0=11=</0B'410RB11<@/0A11AB/0<'4[[\0[^7?^8?^9?^:?^;?^<?P8fD#3fEP:%3Xf@PIPMP[PBp,3HloO:bDbFbGbHbNbMCkP]eb0O2b0O2O3b5b0b511=QP?!#:o$CXR<9j?4RA';Az?4<#3,1A/;='C#2eAH=K<#2eWBWCW0X=?XQ4XK?P;P8O2n2001101000121102100WLX>4XO?o"). Qed.

  Lemma missb_subN : ltac2:(zQ "90!mk7!mkf!jtd!knd!nk7!koa!lh9!jt6!km9>2lo$3>1n$7>1i$3>0@3$2$0@2$4^3^2$1>0@2$6^4^2>0@2$6@2$5^3+1@2$5^5@1$8^4@3$2$0@2$4^4N1$1").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntryN ()) ["MainEntryN"] "##J'h01Hh14__x1h24__x2h31xh44__x3h51nh61mh77__arithh84__ffh96__sat4h:!s/%5h;!s/%6h<8__varmaph=5__with>2b1h?2b2h@4cstrhA1AhB2H0hC2H2hD2H3hE2HahF4__x4hG1fhH1lhI2H1hJ2HchK4Hhi'hL4Hlo'hM1chN1ihO2lohP1yp;2p;1p;3p;6p;4p;7p;<p;8p;Bg03GEj2UTg0080R0j22Tg004Lj1@Tg010`R1j23Tg007PR2j14Tg03HUj25!sY$LR3j2BTg03I3j2aTg038Bj2_!sk$jj11Tg00Llj1=Tg03;Sj28Tg00>Cj1JTg03@Fj2kTg006Pj1R!sn$Tj3CTg00:jj3LTg03J0j3S!t$$bj2Hj3O!s;$Sj6^Tg00@?j1G!s/$dj2]Tg00ALj2N!s/$hj2\Tg00BEj3[Tg005Oj1Z!s8$ij2YTg00CSj2XTg00DDj2W!s/$dj1VTg00EDj2MTg00mZj1z!s8$bj1yTg00F@j1x!s/$kj2ATg00H\j1wTg00Ibj2sTg00?<j2?Tg00JDj2rTg00K0j3q!s/$Oj4pTg00GNj2DTg01L<j3K!uN$nj7oTg01kbj2ITg028^j3QTg01lKj2jTg00[cj3iTg026>j4PTg01iNj1h!s/$lj4lTg00MQl<n!wC$Aj4fTg00<^j3eTg01Iij4d!u&$1j4cTg00N6j7tTg002oj8uTg01MVl<b!tL$8lBvTg00SLR4f0R5g00W[R63ep=0f2R7f1R8/H5g03LCR93Cp=6g00P9R:/85p=;%=5#=p=:%15#1#1#1p=T!s2+!s$'p=E12:5p=7AC859p=`!sI$p=Fg00O9R;P7P8P5Cdp=>P7g002PR<g00PWR=P=g00Q7R>P;P8g00W4P5Ccg00QWFtp=9f3R?P<P=P=P>!sm%Gup=<g00NZR<P;!s$$2P2f5R2f4R@P?!sL%M<bp=g!sF&!s$%1P5P8P7P1P?P@P2f6R1f7RAf8RBf9RCMBvp=m1U78#012?8g00R7RD#@RE,37%4?,3@'2P31585#0%07RF%08RG'BRH[RI%05,BG1578#0RG[RJ%0?/BF\G1a85RGP8n20010!s#$12!s-%0X?4X>4RFPI^?4^>4RKP51_;<RL?612%;1RM'5RN%42,31%1DR2#1RO#=#1#:#1#=#T#E#@RP'8RQP?O3%0N%0Q'BP3A6LA1%;A'5#0%41,3A/8P#0g00UMRQ#JRN96L1/5M%4NRM,31/8P'5#0P5A6LCB%;C'5#0f:RB%4C'3!sc$PFPKP5f<RKf;56LRF%;KR1P7O3%0F%01'BP3f=RF=6LK#0%;F#0A6LKN/5113KM!t0+f?f>56L#0f@#;#0P31885#01278RK[R11285RF18!vi$R[RS12?7\R1k85RR!vg:6;X5;RTP1^6;^5;RUP5P:fBRVP8O3%7VPTPUP5fDRUfC#4'3RTPPPCO312TPP3PIPJ15?7#0\HPGP5!wr>GPJ!wr&J!vJ$UN%;U'5RH13UM/8PRU%0H%0UPGPJP5fERJ=6LNRG%;JRU%0G%0Ug03MSp4p710RUP4\5RG%R8RHP3AC785#0AL@57P@P8O1#0[^3?RI[AL?58P?!s:+7AC?78#0[RTAC@!u1$IAS785!u49WHWGWAPT^HH^GG^AUP5PLfFRU/HNP9ALL59RGfJRHfIRTP8fH1HHTRI,`L#0fMRCfLRV;O8#0\G^3L[fKRW=OV!s6'A6LWH#0[ASLI9PBP8P5E^%GTRI%4T#7R9%@2RG%=2RX!z{$@RY']RZ1N:G%7Y1\GYR[,N:[[R\%7GR]g00UlR^A[GY8UWERY%7[\^^E]R]%FORO#F#Zp,3sp0'YR^%@ORO'XR[%7^%7O1W^O#7[[ROg00VHRG#VR_%RGR`1M;7Ra%z;Rb7>8%y;Rc%x;Rd1A;DRe1A;2R259dRf%w=R=PfC<1sd>R>P5P71?461r57#0dAq;:8CpR6b8b<b=X1;X2;12581287[^1;^2;P5PCfOR4PWO3b7b9b:b;b@PIP9PZP\PYP]P[POP_P`1M;?R99>a8PcPd1D;E9K;eRa%=DRD,A;RI9K;!te$2P=P2C<P>P!tH0X4;135ER21387'2138E137?Rf'2!t[&^4;P5fN#4P4PCPHO4!t`,FoWJXMLO4b0P3P1PS18!yb$KPR!{m:!|x%RPS!|x&SP5P:PUfGRK#G%4K#7!uX/%JNR1#J,I;1I;11I;Q5Q;5Q;g02>h'j=iG_R_P`A>97bR99>b!u|%A;XRX=9deP=!v2$:R:=9dXP=Pd%:D#:!s$-1#F#T#E!s$$@RG,D;=9dIRIP=A9d:eC<C<!vR9275%7?R712G?RGP7[[!vM/PCP^PWPTPBp,3HloRBO6!vU,O3b0CPO3b0PRPSP513JMRSPP12SPRR13JERT/2PP;P;P0P5X3;RCP0%hFXP;X3;PSPTPC!s$$;P!v&$D1385Cl,?;!w#%PJPJ1?;JPMPEPCPC%45,?;X3<PNPE1?;EEgM:mPPPP1?;PM<n%GU%4U!wC1!yu&@9>b@?>89PcPd%1D,A;9K;XRX99da!w#&PRD9!w#&P!vY%aD!vY<XF;122f13?@/2P13?E/2P\G!v^-^F;P5%4WPVP^PHPKPAPBO7!v^,CfPRe!vc,bDb0bCb0WCWIP8P5O2!z90!s/&b0bBWDW0!sHA1U?N#0eWKWLW0XN;X5<XO;o"). Qed.

  Lemma kimg_okN : ltac2:(zQ "c0!knd!lh9!mk7!mkf!jtd!kk5!nk7!nl7!nlf!lme!nmc!nn3>2lo$0>2hi$0>0@3$4$2@2$6^2@1$b@2$a^1^2$3>0@2$1^3^2>0@2$1^3+hitgg0@4$8$9$5?3mem@2$7^5^4").
  (* LPS-revision port, written out rather than re-encoded (rule 11); the STATEMENT,
     including the 0x12d000 bound, is untouched.  The replay applied the pre-revision
     6-argument `D_main sp0 av envv a_hwcap rdraw tid`, and RefStartupDefs.v:191 now
     reads `D_main inp sp0 rdraw tid`.  Tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntryN.v:219-230, re-threaded
     exactly as this unit's own landed kimg_ok (RefMainEntry.v:706-724): D_main_none's
     argv premise is over `in_argv inp`, hence kvaN, and main_entry_mem_data is
     RefStartup.v:351's. *)
Proof.
    intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _].
      apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 rdraw tid regs mem ME)
      by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none inp sp0 rdraw tid i kvaN); [lia | lia |].
    apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.

  Lemma know_imageN : ltac2:(zQ "40!jne!kk5!lo7!lme@4$2$3$1?3mem$0").
  (* LPS-revision port, written out rather than re-encoded (rule 11); the STATEMENT is
     untouched -- the same kn_image this unit's plain twin claims.  The replay applied
     the pre-revision 6-argument D_main.  The bullets are this unit's OWN, taken from
     the landed RefMainEntry.v:740-787 (whose nine goals were read off rule 3o-FINAL's
     all-goals probe a farm round), with E/ke* replaced by EN/keN* and
     kimg by kimgN; beast's addresses are NOT used (rule 22).  The hwcap cell holds
     `in_hwcap inp` at this revision where kn_image claims the ambient a_hwcap, so the
     Hhw bridge closes it (rule 12k-DONOR: re-index and bridge, never delete the claim). *)
Proof.
    pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimgN;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5, ?keN38, ?keN39;
      unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xf9000) (Z_to_bv 64 (0xf9000 + d))
                0x34000 m 0xf9000 0x12d000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_dataN
        | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_dataN (D_main_self inp sp0 rdraw tid).
    - kw_memN (main_entry_tid inp mbase entry sp0 rdraw tid HLO regs mem ME).
    - kw_dataN (D_main_canary inp sp0 rdraw tid); rewrite ?keN39; reflexivity.
    - kw_memN (main_entry_guard inp mbase entry sp0 rdraw tid HLO regs mem ME);
        rewrite ?keN39, ?(canary_bytes_w rdraw); reflexivity.
    - kw_dataN D_main_auxvpN.
    - kw_dataN (D_main_pagesize inp sp0 rdraw tid kvaN).
    - kw_dataN (D_main_hwcap inp sp0 rdraw tid); rewrite ?Hhw; reflexivity.
    - lia.
  Qed.

  Theorem main_know_okN : ltac2:(zQ "40!kk5!nnd!lo7!lme@4$2$3$0?3mem$1").
Proof.
ltac2:(KReplay.run1 (kr_t_RefMainEntryN ()) ["MainEntryN"] "h01Ah11Ph22l1h32l2h41Hp;1p;3p;2p;4g006Pj13Tg00\Cj31Tg009cj30Tg008LR0j22Tg03j0j47Tg02C2j36Tg026>j45Tg02Adj44Tg03jOp4p710R1f0R2p-0[R3f1R4#3R5f2R6#3R7P0f3R0A1042706f4R8?006A0804'2R9[A0064A0062'2A18649080[R:f5R;A1;06708\9P0P6P4P2C7P2n2001000000120000000W3W2W1W0P:^37^25^13^01P2g02`3R2g029GR1g00kKR3p,3memR536R7g02^hR:g03hgR4A027:A0274g03jlg03l9C5O5b4P1P3P5g03mFC4eo"). Qed.

  (* [comment removed for export] *)
  (* LPS-revision port, written out rather than re-encoded (rule 11).  The encoded
     statement held `argcN av`: ArgvEnv.v:58 now reads `Definition argcN : word :=
     len_word (in_argv inp)` over the Section's ProcInput, so applied outside it argcN
     takes `inp`, not the argv list.  Hargv (`in_argv inp = av`) is exactly the bridge,
     the same move this unit's landed plain twin makes at RefMainEntry.v:486-492.
     The index 16 and the lemma are otherwise untouched. *)
  Lemma evN_argc : ev EN 16 = argcN inp.
Proof.
    (* 16 = 6 + 10, and EN's slots 6..37 are the register file (evN_junk), so this is
       register x10 = a0.  RefStartup.v:110 states main_entry's own `me_a0 : getr regs
       10 = argcN inp` over the ProcInput at this revision, which is the whole content
       of the lemma; the replay reconstructed the pre-revision `argcN av`. *)
    etransitivity.
    - exact (evN_junk 10%nat ltac:(lia)).
    - first [ exact (me_a0 _ _ _ _ _ _ _ _ ME)
            | rewrite <- (me_a0 _ _ _ _ _ _ _ _ ME); f_equal; vm_compute; reflexivity ].
  Qed.
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
