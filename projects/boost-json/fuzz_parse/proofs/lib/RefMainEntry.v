(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv
  SymExec SymExec2 SymExec2Sound SymRun SymDrive
  MemSplit RefLayout StartupTac RefStartupDefs RefStartup RefStartupFacts.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SegRead.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefMainEntry () := KReplay.lz_vm "#%S\C47Corelib7Classes9Morphisms6Proper!sI-Program6Basics4flip!sg?:forall_def!sM?Krespectful_per_obligation_1C46Stdlib9micromega5Tauto5eKindK!sE;8GFormula08!si+5Lists4!s+#6nth_ok!td,4Init5Logic8eq_ind_rK!u&,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!uT#s2bv00I!tR19Datatypes4list00C4ELinuxProcessSemantics?!s<23Run:valid_argv!u3G1C!tm@;bv_unsignedC5!vc&6ZArith6BinInt1Z2leK!u8;3nat02C79OSSVerify!yi#ofs:boost_json:fuzz_parse3lib?RefStartupFacts<D_main_missbC13~~~!svP8!{&#Exec9u64_range!sl%!w~>Z02!ue<3powI!yL73and!ws#!s^&4Bool!s'$=andb_true_iffC!x\<!sM#!tE<6of_nat!te=ad!wi=3leb!y|<6op!x[#00K!sHC2!un82eq00!xQ`@!w\$_disjoint_!xUW!sz3B!sz2djw!s|&!w$<leb_le!~p9iff_refl!#4<5;Zify!#5%%3inj!sIB7rew!xv$!tV;>pow_pos_nonneg!}->!x|=:!sj#!sf%K!#3d@1!#6?56VarMap1t!x`#!sD>0!sD6=RingM!s4'7!#7&&0!t567Env!sT#5PExpr02!sIE1!sIE7!#8~;8B!t[&K!{+;!#9b6:Z!uC+=Z!sn$CheckerC!v8<4find!sqAC!sq0_soundC8!{UN=SymExec2S!sa#4SX2S7u_small!{M&!#8#?7Z_to_bv!|qP>!|q,Defs6envp_!|d'!#:BI>Riscv!sE+@word!tY#le_bytes!t_P7Cat!u{#6w!sb%!#3<T!uI3auxv!uI+!so^4pn!smg:progname!ss'!~'B2!t;_8canary!t9,!~X>1!#5;A;!#5;%_rev!#;7;6length!xaXD!sb%_N!yS0!u/$!#:C8or!#:CQ8MemSplit>!yt%_outside!y|f!#@`$!x@Cprod!w/#!#B9:fst!sC=snd!#<,_3!#;v+!xXA5mkapp!sKB6!sK$2!sqErel!#81D3K!#9mK1!#J=E4!sJF5!x^_3rbn!vjH6eq!#DP$!sL@8or_morph!u-F6!#Jz<bool!#Cz=!sF%1!#GK?1I!sD?!#LF<!#J4#!#Le=unit!#>p7!uU%4kind!xI8!xt13Op2!yC#!t5@!smJ5!#MdF3I!#;LI;StackLayout9EntryDraw!wT>!vP$!#6s68!y/#Inst7Inj_Z_Z!#5T74True!#C57!#?z,;!#Dr$!{C$00!#G,2Peano2ltK!#R-C!#PbA5bv_eq!t,,!#TB$7!s+#Def3nth!#FT24Znat5Nat2Z9is!#FU'!{cD3c!}kO<RefMain!wU$8all_regs!#JR8!t`-8inj_succ!sJ>6!sJ#!vY#!wa<!|X?N!#UX<5!#B+#7Prelude5bvmap!wDA4BvWfK!#E@N8!#E@&3SX24e!#HU#!#Cz@!td16!x^$bC!tB]ridx!#;s2!#3v53!#90=3P!#4{$!~IB5Psatz!#KP7!sO84!sOK6K!}1M2!#BX?3!{_F!#;<F:!#V'<!wtS!#KR5:!wz#!#Yc-!xm]6edenot!sm%!~0]<nth_!~42!}F76!#a2$!uwc>!uw%!s6#trip!u{dsr_get!smV!#P76!uy#_ok!#FHU!#_3'4getr!#H>%!uL\3env00!slc!#4B$0!#3$&!|vL1!#?GA2!#>XH1!#AyA2!zr]2p0!{]c2p1!sic5auxvp!slc3rnd!z/WSymDrive9junk_val!#U=V3Amb7a_hwcap!~Z8!#BH,!#L<#!#@'9seq!#mb6:!#QC%s!#@f=!#=0#!sa=!sE$!ta03Nat!#fS#!vMX;n!s{%!tb$!uh&!tL58app_nth1!sC7=!sC&2_plus!#4j\2ev!ySc7ev!xi-!sn]@!w4&!yb3!w@6sub!#G%8ge!#eh<ge!w+?2!#DQBge!#3yH4!#7ZX5v_!yf#!ui&!#aU?bv_wrap!#jJ<modulo!ud+!uG+divAZ!yF#_mod_idemp_r!t}Y=!tS&64!sr#!u,G@!#c\%!#tb+!#Ex?3Sem5alu6!vnZ7alu!vp,!#5q]sp!#F^'!t~?5Instr!u$#op!#[_3!#@L$5proj!sA>!#aWP:!#Wn+5me_ra!wK&!#Dh;!|C#!t/^s!#9\c2E!#;xc7spx!~z#!#9]U!uE2gp!sjetp!#6:fjunk!tZes0!sjV7ArgvEnv5argcN!tSf1!sjea0!sjf1!{sCmu!#cRE5C3!#5$$7tac!~I#<f_equal_help!to`2!w3f!sjg3!sj&!#;`52In!t%[8!t%#zero!#68&!#5I52or!#HM^@!#M>%_by_inde!#7K'!xCC4!y'>ax!sC<8max_spec!uC<!#8$87and!to#!#5J^r!#nQ,!to+5!tn$8!#A-#Na!#AN+!#@U<;!#^L$b_max!#bh75False!$4BL5State<sp_window_lo!sa\hi!#Ls]ev_38!#72b!sl$9!w+&!#Tta9ke!sy#!#Tv'!#`cb2!smc6!t_%05!sok6!soc5sadd!#c5'!t_e7!sok1!#4c=!$8U#!#lY69SatDivModCZ!#H+#!#j#$!$2E&!$&_X8store!y[#!#7-YG!$<K#!zI%!sr'!}##!{KV!vI1a_bas!#atc5a_off!}$i4fla!#_ii6es!v]#!ss%I!#Pv7le00!v]_!#dd,!$=/C!$'UB9and!#yj$!y=P3Amb5a_ui!#[@W!#M}&8wrap_mem!skV!#ET&;rea!$FT#c!$3wR!$G;,envp!tLX4w!u4,!tEJ6BvBase8!$56#le8!vYY>n!$/E%8!#?>#!v_V!~H-D!~H-rdn_abov!}V'!#TE?C!#TE&!$J+F7add_0!#V2Q!w/'?!xU'v_ptr!xY,!#Z}4mul!wQR;nat!u>#!wX#!ufA6b!#Y_$!u8P!$4F%<cat!u7+!#3rh9w!t\#!$Is#!xnU9Ref!$$6$>!vz,nu!$>d+!|TMA!#8s&ack_imageC!$%eU<!sf%to!~p$!y;W>!z{#!}H#!tY%!#5y2!#f606F!$W##01!#q'cknow!#q'a3rdn!sf_6!zV$i!uhI2I!#@uc!#Z&c3ke!#TY5!sc96!yi$s5Plain1M?loaded_segment!$'OD!$''$e!#IS]kp_lo!uic!sl#hi!slga!}ZR!#MF$>!|n%!#QA#ize!w>T5phdrs!xgf1!sjf2!sjc8kn!#3+-!#69Y8!$J5#!#E^+!#Sf>!$Y}5!zc-7!zc#!sI/!si7mul!siC!sI#!#8UY!uB'_b!$Q'#!yyP!#7o-Abuild!#8]%!$NzT!t`,;lay_bsb_len!x^d!#{2#_!#v2+!uNU=at_random!#=Y#!$=hVed!sh&!sdW?!tN,!vt%!#8695skipn!sD;6firstn!wYZ9rnd_fac!#6u'!#9AN3Lib2Nd:and_elimF5!}3`:!$TB$ords!sn`!#A6%!ss'!sr%!$,EM3!$8:J7!sOK5!#a#]!{N%u!u<&!#>$c8!#501!#x~3divide!$9NE7!sj<:mod_!sn%!$gn9x!$j],!#z0-:!#X~$mult!$JS<!$S5#0!#EiW!y'$!v##i!|}#!#7@&!#~?,flat!$'i#!{n`3!#54b<!z|+_at!#<Me!t_d7kn!|`$!tZf4!sjc4ke!#f_ernd!|d'!#KcPStepTac6u_Z2bv!shXeq!}N#?!#LM#!$\a$hit8!sqV:!#UH%Tac@!st-out_Z!su%!$Q_J<MemImageType7S!#HZ$!$Q^3;Hexadecimal4uint!${[-!sH:6!sHD5!sH26!$Ii$!t/&!#Uk5;of_num_!sG#!#8sPStreamSim7wseg!#kY+!tqC!$`+=orb!#3Q'!$xY+<or!$xX;!#ge%!s?0!%&05!%%a+!sM?@subrel!%%z$!$tg$!sS+!%'J1imp!sq@5flip2!sH?F!t;1!tnGI!tb#exive_!s0,proxy!t7@!sR0per!sYEB!tj/p!%-M2!sU4NR!t0,artial_app!#dj$ism!sa5>!sa+_Prop?or!$in#!sW=!t:,D!sO#!wD#_!tr-!vS@!sW#!wT#!s\F?R!sA'!s6%=!sb#!uS+!#;+67!%0z$b!sB7>!sB&_!s-%!#6_\!$},2su!$~'f!%+R&cel!$=j+!uX6ex!s2#!%&C=to!%&C6!#N<$Z2Nat2i!#}=]9!%-B#!uj,!sp];!ug&non!$nOV!#g<,C!#g<,mem_dat!$85%!#E+d4!#<7XoreOk?!#t;-dow!#@9dimg!#`NX!z+3!wC'self!wCmrdn!wC-!#j~Bl!u8`>!tF-t!#r<W!sx3=!}8'!$y:#!swV!$pB1<!$z'%!$}oZ!uh4!sv/!$}1W!%3{3!vb-guar!$D5c!#4s&!$Su,!to`?!sv&page!#aA#!#6fl!$SO,!#5d]!#BJ#!{Y,!#J]_5!sjc4ke!$1P&!#\m]kn!#p$%!so$!#Qc+!#ki80!$Uh7!sC%_appI!sE66E!#:b#00!tt]:!#o1#!#dE,!x2^!sq$!#Oif!tc%!v[-!#QL`!$:l,!snO!#\e,!#bt&n!#33V!#tZ&B!#zj'!#eD#s_!#wkbu_!#yW5!thP!#zG%?!sn#struct_!~|Z!te,?!so&av!#g|/!ssO!#u;'Ctotal!uY#!#7S%!#{?X!u^'I!su3!#dG$_l!uha<!wI$str!#i++!tmQFileSim@!#}++c!st#!}H&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list37Corelib4Init5Logicm02eq46Stdlib6ZArith6BinInt1Zn92lehfbbv_unsignedk14Nonek14boolk16optionk14true01Z3h5LinuxProcessSemanticsfLinuxProcessSem3Runs5avalid_argv3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutve9EntryDraw69OSSVerify6Proofsaboost_jsonafuzz_parse3libeRefStartupDefs~~~~~~hje6D_main69OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefStartupFacts~~~~~~ho9cD_main_missbhf7Z_to_bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~hu5ccat_argv_ptrhje6auxv_wvedat_random_ptrk14consk13appk13nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Amb~~~~~~ilc7a_hwcap79OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMainEntry9MainEntry~~~~~~ipd5auxvpipd2p0ipd2p1ipd3rndhje8canary_w69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~jge9junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~jl63envipd6blobs0ipd5vals0jge8blobs_evjl63Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~js27vals_evjl64expr3h5LinuxProcessSemantics5Riscv5Instrkge7ALU_ADDjl64EAlujl64ELitjl64EVaripd3spxjl66kentryjl62SAjl65KWordjl66KAlignjl66KRangejl63KWrjl65KDisjjl64KImgipd7kn_auxvipd8kn_imageipd8kn_stackm01Ihf2BVhf4BvWfk13nat37Corelib4Init5Peanokta2lt37Corelib5Lists7ListDefkv43nth79OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMainEntry4FPX2~~~~~~lh28all_regsn96of_nat3h5LinuxProcessSemantics5Riscv7Preludelmb5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~lpa4getrjl66edenot79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~lu77regs_okk16lengthn96modulo69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMainEntry~~~~~~mk93rndm03andn93addk14Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmq2h0word_to_le_bytesilc5a_uidlpa3rdn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9RefLayout~~~~~~mveaauxv_wordsmk95auxvp69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~nl1floaded_segmentsnl15phdrsn93mul37Corelib4InitbHexadecimalnq92D0nq92D1nq92D4nq93Nil37Corelib4Init3Natntcbof_num_uint37Corelib4Init6NumbernvdfUIntHexadecimal69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~oi57wseg_okho9h0range_disjoint_bk14prods58valid_spn92ltn93pows5avalid_envpnq92D3" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
(* LPS-revision port.  The encoded statement held the pre-revision D_main
   (sp0 av ev hw rdraw tid), which no longer exists: RefStartupDefs.v's Section Defs
   now exports D_main inp sp0 rnd tid, with av/ev read off inp.  A KReplay blob is never
   re-encoded, so the replay is replaced by an explicit proof (rule 11).
   Statement and tactic text: a donor tree
   :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:30-53 (the plain-text twin of
   this encoded file), statement AND proof, with boost-json's own D_cxx for beast's D_cx and
   boost-json's own cell table; the argument list re-threaded to boost-json's own
   RefStartupDefs.v:191 and RefStartup.v:101. *)
Lemma D_main_none : forall (inp : ProcInput) sp0 (rdraw : EntryDraw) tid (i : Z),
  valid_argv (in_argv inp) ->
  (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main inp sp0 rdraw tid (Z_to_bv 64 i) = None.
Proof.
  intros inp sp0 rdraw tid i Hva Hlo Hhi Hb.
  pose proof (u64_range tid) as Ht.
  unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
  repeat match goal with
         | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
         end.
  repeat match goal with
         | H : range_disjoint_b _ _ _ = true |- _ =>
             apply range_disjoint_djw in H; cbn [fst snd] in H
         | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
         | H : true = true |- _ => clear H
         end.
  assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
  unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX1.

Section MainEntry.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!hj2$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!lp1!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : word -> option byte.
  Let av : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8") := ltac2:(zQ "50!l9!h9!jc!ik9!il6@3$3@1$0@1$2@1$1#8?3a0s@3$3@1$0@1$2@1$1#8?4path@1$4@1$0@1$2@1$1#8").
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = ev.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* LPS-revision port, written out rather than re-encoded (rule 11).  Three tree-local
     signatures moved with the revision and the encoded forms hold the old ones:
       CatExec.v:258-260  cat_argv_ptr (top : word) av ev (execfn : list byte) (k : nat)
                          -- gained execfn; `top` is the DRAWN top, and this tree's own
                          ported CatExec.v:422 and :495 apply it as
                          `cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k`,
                          which is why the base is `ed_top rdraw` and not sp0;
       RefStartupDefs.v Section Defs exports  auxv_w inp sp0;
       at_random_ptr gained the rseq flag -- RefStartupDefs.v's own rnd_w reads
                          `at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev`.
     Donors, statement only, both ported and in agreement:
       this unit's own RefStartupDefs.v (pn_w / auxv_w / rnd_w) and
       a donor tree
       :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:116-119.
     kb_rseq is taken from the run and never pinned. *)
  Definition p0 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 1.
  Definition auxvp : word := auxv_w inp sp0.
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.

  (* [comment removed for export] *)
  Definition vals0 : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#k0") := ltac2:(zQ "c0!h9!jc!ik9!il0!il6!ip2!iu6!iuf!iv5!ivb!jg2!jk9@3$3@1$1@1$0#k0@3$2@1$1@1$0#k0?3sp0@3$2@1$1@1$0#k0$7@3$2@1$1@1$0#k0$8@3$2@1$1@1$0#k0$6@3$2@1$1@1$0#k0$9@3$2@1$1@1$0#k0?3tid@1$4@1$1@1$0#k0@3$3@1$1@1$0#k0@1$b?4regs@3$2@1$1@1$0#k0@1$5?3AMB@3$2@1$1@1$0#k0@1$a?5rdraw@1$4@1$1@1$0#k0").
  Definition blobs0 : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8") := ltac2:(zQ "71!h9!jc!ik9!l9!il6!il0!htb&@3$2@1$1@1$0#8@2$6@1$0#8Z@1$4@1$1@1$0#8@3$2@1$3@1$1@1$0#8@3$5@1$1@1$0#8?3a0s~0@3$2@1$3@1$1@1$0#8@3$5@1$1@1$0#8?4path~0@1$4@1$3@1$1@1$0#8").
  Definition E0 : ltac2:(zQ "10!jp5$0") := ltac2:(zQ "50!jpc!jq6!jqf!jrb!jvb@2$3@1$4$1@1$2$0").

  Definition spx : ltac2:(zQ "20!s2!kg6>1k$0$1") := ltac2:(zQ "50!s2!kj2!kjd!kk5!kkd\1k$0@3$2$1@1$4N0@1$3^1").

  Definition sr_main : ltac2:(zQ "20!l9!kg6@1$0$1") := ltac2:(zQ "60!kg6!ik9!kk5!kkd!kl5!il6@3$1$0@1$2Z@3$1$0@1$2+tqgsc@3$1$0@1$4-j0@3$1$0@1$2+hgog0@3$1$0@1$2+hgrmr8@3$1$0@1$3Nb@3$1$0@1$3Nc@3$1$0@1$3Nd@3$1$0@1$4+8@3$1$0@1$2+2@3$1$0@1$2+2@3$1$0@1$4+8@3$1$0@1$4+i0@3$1$0@1$3Nh3@3$1$0@1$3Nh4@3$1$0@1$3Nh5@3$1$0@1$3Nh6@3$1$0@1$3Nh7@3$1$0@1$2+knjt0@3$1$0@1$4+i0@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$3Ni2@3$1$0@1$3Ni3@3$1$0@1$3Ni4@3$1$0@1$3Ni5@1$5$0").

  (* LPS-revision port.  The encoded form claimed the writable stack window as
       KWr (SA (EVar 0) (-8388608)) 8388608
     i.e. everything from sp0 - stack_max_size.  THAT IS FALSE AT THIS REVISION: the model
     certifies writes only from MemSplit.wok_lo sp0 = bv_unsigned sp0 + stack_window_reach
     - stack_max_size (MemSplit.v:137-138), which is 2,244,095 bytes higher.  Measured, not
     inferred: a farm round's UNCLOSED-GOAL probe printed
       (bv_unsigned sp0 + 2244095 - 8*1024*1024 <= bv_unsigned sp0 + -8388608 + d)
     as the obligation main_entry_store_ok_win could not discharge.  8388608 is the
     zero-filled window here, not stack_max_size's other meaning, so it is the occurrence
     that MOVES (rules-broadcast 12h; G3-FINAL section 5).
     Written SYMBOLICALLY rather than as 6144513, so it stays right if either constant moves.
     A KReplay/CDef blob is never re-encoded, so the definition is written out (rule 11).
     SHAPE DONOR, mapped entry-for-entry onto this file's own zQ string before use:
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:134-138.
     RULE 22: every literal below is read from THIS file's encoded string
     (+h0 = 16, +nvvvogggggg0 / +ogggggggggg0 = the two sp bounds, Z/+8/+h0/+h8 = the
     offsets 0/8/16/24, N8 = 8, +2 / N1 / N2 / Z = the four values); only the window moved.
     UNITS: BYTES below sp0.  Not words, not pairs. *)
  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (stack_window_reach - stack_max_size)) (stack_max_size - stack_window_reach);
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  (* LPS-revision port.  Same stale window as kn_stack's KWr, in both KDisj entries:
     the encoded form claimed the stack write window as [sp0 - 8388608, sp0), where the
     model now certifies only from MemSplit.wok_lo sp0 = sp0 + stack_window_reach
     - stack_max_size (MemSplit.v:137-138; measured by a farm round's
     UNCLOSED-GOAL probe).  Written symbolically, not as 6144513.
     A KReplay/CDef blob is never re-encoded, so the definition is written out (rule 11).
     RULE 22: every other literal below is read from THIS file's own zQ string, decoded
     digit by digit (the numeral alphabet is g..v = 0..15 with the last digit in 0-9/a-f,
     so +q0 = 0xa0 = 160, +h0 = 16, +hggk0 = 0x10040, +j8 = 0x38, +hgg0 = 0x1000,
     +h7 = 23, +h9 = 25, Ni6 = 38, +nvvvogggggg0 = 0x7fff80000000,
     +ogggggkgggg0 = 0x800000400000).  The encoded table is the PRE-REVISION 10-pair
     vector: words 0..19 with 11 and 13 unclaimed, which is also what the plain-text twin
     still carries (boost-beast@a donor branch :.../RefMainEntry.v:404-425).
     THE KDisj SIZES.  160 was never the auxv block's size -- it is the extent of the
     PREFIX THIS LIST CLAIMS, and the claimed prefix moved with the table, so it becomes
     400 (words 0..49).  16 is at_random's 16 bytes and does not move.  Neither is written
     as auxv_size (kb_rseq (in_kernel inp)): that would make kn_main depend on a FREE
     kernel field and stop MainWalk_defs.v's `Eval vm_compute in runM ... kn_main` dumps
     from reducing at all.  The parametric auxv_size belongs where the revision really
     put it, in auxvp_u's bound, and it is there.
     UNITS: BYTES below sp0 for the window; BYTES for both claimed extents. *)
  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000;
     KRange (EVar 4) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (stack_window_reach - stack_max_size))
           (stack_max_size - stack_window_reach) (SA (EVar 3) 0) 400;
     KDisj (SA (EVar 0) (stack_window_reach - stack_max_size))
           (stack_max_size - stack_window_reach) (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     (* THE WHOLE TABLE MOVED, and this is the third and largest staleness site this lane
        has found inside an encoded definition.  MEASURED, not inferred: the Print probe
        in a farm round dumped the revision's auxv_entries, which is
          0 AT_SYSINFO_EHDR  1..8 the eight cache words  9 AT_MINSIGSTKSZ
          10 AT_HWCAP  11 AT_PAGESZ  12 AT_CLKTCK  13 AT_PHDR  14 AT_PHENT  15 AT_PHNUM
          16 AT_BASE  17 AT_FLAGS  18 AT_ENTRY  19 AT_UID  20 AT_EUID  21 AT_GID
          22 AT_EGID  23 AT_SECURE  24 AT_RANDOM  25 AT_EXECFN
          then (if la_rseq la then two AT_RSEQ_* pairs else nothing) then AT_NULL
        -- 27 or 29 pairs, matching auxv_count = if rseq then 29 else 27 and
        auxv_size = 16 * auxv_count, both printed by the same probe.  The encoded table
        claimed the PRE-REVISION 10-pair vector, which began at AT_PHDR; the revision
        inserts ten pairs ahead of AT_HWCAP, so every offset the blob carried now names a
        different auxv slot.  A text sweep could not see this: the table was encoded.
        WHAT IS CLAIMED HERE IS THE SAME SET OF FACTS AS BEFORE, at the offsets the
        revision puts them -- nothing is added and nothing is dropped except AT_NULL,
        whose pair index is 26 or 28 depending on la_rseq, i.e. claiming it would PIN
        kb_rseq, which the rules forbid.  Every key and every value literal below is the
        one the encoded string already carried (3, 0x10040, 4, 0x38, 5, 0xa, 16, EVar 38,
        6, 0x1000, 0xb, 0xc, 0x17, 0, 0x19, EVar 4); only the offsets moved.
        OFFSETS: word index i sits at byte 8*i, and pair p occupies words 2p and 2p+1.
        UNIT: BYTES. *)
     KWord (SA (EVar 3) 160) 8 (ELit 16);      (* pair 10 AT_HWCAP   key   *)
     KWord (SA (EVar 3) 168) 8 (EVar 38);      (*                    value *)
     KWord (SA (EVar 3) 176) 8 (ELit 6);       (* pair 11 AT_PAGESZ  key   *)
     KWord (SA (EVar 3) 184) 8 (ELit 0x1000);  (*                    value *)
     KWord (SA (EVar 3) 208) 8 (ELit 3);       (* pair 13 AT_PHDR    key   *)
     KWord (SA (EVar 3) 216) 8 (ELit 0x10040); (*                    value *)
     KWord (SA (EVar 3) 224) 8 (ELit 4);       (* pair 14 AT_PHENT   key   *)
     KWord (SA (EVar 3) 232) 8 (ELit 0x38);    (*                    value *)
     KWord (SA (EVar 3) 240) 8 (ELit 5);       (* pair 15 AT_PHNUM   key   *)
     KWord (SA (EVar 3) 248) 8 (ELit 0xa);     (*                    value *)
     KWord (SA (EVar 3) 304) 8 (ELit 0xb);     (* pair 19 AT_UID     key   *)
     KWord (SA (EVar 3) 320) 8 (ELit 0xc);     (* pair 20 AT_EUID    key   *)
     KWord (SA (EVar 3) 368) 8 (ELit 0x17);    (* pair 23 AT_SECURE  key   *)
     KWord (SA (EVar 3) 376) 8 (ELit 0);       (*                    value *)
     KWord (SA (EVar 3) 384) 8 (ELit 0x19);    (* pair 24 AT_RANDOM  key   *)
     KWord (SA (EVar 3) 392) 8 (EVar 4)].      (*                    value *)
  (* [comment removed for export] *)

  Definition kn_image : ltac2:(zQ "20!l9!klc@1$0$1") := ltac2:(zQ "a0!klc!ik9!kp9!kk5!km6!kmc!kkd!il6!knf!ko9@3$1$0@2$9@2$4@1$3Z+vpgg0+jkgg0@3$1$0@2$2+hggg0+vprr0@3$1$0@2$2+vprr1+hgpsm0@3$1$0@2$2+hgpsmc+hgpuu8@3$1$0@2$2+hgpuuc+hgrlu8@3$1$0@2$2+hirms0+hirmu0@3$1$0@3$5@2$4@1$3Z+hgrlv0N8@1$3+hgrlv0@3$1$0@3$5@2$4@1$3Z+hgrmh0N4@1$6N5@3$1$0@2$2+hgrmhc+hgrmm8@3$1$0@2$2+hgrmn0+hgrmo8@3$1$0@2$2+hgrmp0+hgrmq8@3$1$0@3$5@2$4@1$3Z+hgrmq8N8@1$6Ni7@3$1$0@2$2+hgrmr8+hgrms8@3$1$0@2$2+hgrmt0+hgrnk0@3$1$0@3$5@2$4@1$3Z+hirmv8N8@1$6Ni7@3$1$0@2$2+hirpj0+hirpj8@3$1$0@2$2+hirpk9+hirpl0@3$1$0@3$5@2$4@1$3Z+hirpl0N8@1$6N3@3$1$0@2$2+hirpl8+hirpm0@3$1$0@2$2+hirpn0+hirpn8@3$1$0@3$5@2$4@1$3Z+hirpn8N8@1$3+hgg0@3$1$0@2$2+hirpo0+hirpr0@3$1$0@3$5@2$4@1$3Z+hirpr0N8@1$6Ni6@3$1$0@2$2+hirqs0+hitgg0@3$1$0@3$8@1$6N5+1+jvvvvf@3$1$0@2$2Z+hgg0@1$7$0").

  (* [comment removed for export] *)
  Definition kn_main : ltac2:(zQ "20!l9!klc@1$0$1") := ltac2:(zQ "50!il0!klc!kq1!kqc!kr8@3$0$1$4@3$0$1$2$3").
End MainEntry.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition all_regs : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#5") := ltac2:(zQ "70!h9!jc!ik9!ks4!ks8!ksd!il6@3$2@1$1@1$0#5@3$4@1$0#5ZKv$3@2$5@1$0#5Z@3$2@1$1@1$0#5@3$4@1$0#5+1Kv$3@2$5@1$0#5+1@3$2@1$1@1$0#5@3$4@1$0#5+2Kv$3@2$5@1$0#5+2@3$2@1$1@1$0#5@3$4@1$0#5+3Kv$3@2$5@1$0#5+3@3$2@1$1@1$0#5@3$4@1$0#5+4Kv$3@2$5@1$0#5+4@3$2@1$1@1$0#5@3$4@1$0#5+5Kv$3@2$5@1$0#5+5@3$2@1$1@1$0#5@3$4@1$0#5+6Kv$3@2$5@1$0#5+6@3$2@1$1@1$0#5@3$4@1$0#5+7Kv$3@2$5@1$0#5+7@3$2@1$1@1$0#5@3$4@1$0#5+8Kv$3@2$5@1$0#5+8@3$2@1$1@1$0#5@3$4@1$0#5+9Kv$3@2$5@1$0#5+9@3$2@1$1@1$0#5@3$4@1$0#5+aKv$3@2$5@1$0#5+a@3$2@1$1@1$0#5@3$4@1$0#5+bKv$3@2$5@1$0#5+b@3$2@1$1@1$0#5@3$4@1$0#5+cKv$3@2$5@1$0#5+c@3$2@1$1@1$0#5@3$4@1$0#5+dKv$3@2$5@1$0#5+d@3$2@1$1@1$0#5@3$4@1$0#5+eKv$3@2$5@1$0#5+e@3$2@1$1@1$0#5@3$4@1$0#5+fKv$3@2$5@1$0#5+f@3$2@1$1@1$0#5@3$4@1$0#5+h0Kv$3@2$5@1$0#5+h0@3$2@1$1@1$0#5@3$4@1$0#5+h1Kv$3@2$5@1$0#5+h1@3$2@1$1@1$0#5@3$4@1$0#5+h2Kv$3@2$5@1$0#5+h2@3$2@1$1@1$0#5@3$4@1$0#5+h3Kv$3@2$5@1$0#5+h3@3$2@1$1@1$0#5@3$4@1$0#5+h4Kv$3@2$5@1$0#5+h4@3$2@1$1@1$0#5@3$4@1$0#5+h5Kv$3@2$5@1$0#5+h5@3$2@1$1@1$0#5@3$4@1$0#5+h6Kv$3@2$5@1$0#5+h6@3$2@1$1@1$0#5@3$4@1$0#5+h7Kv$3@2$5@1$0#5+h7@3$2@1$1@1$0#5@3$4@1$0#5+h8Kv$3@2$5@1$0#5+h8@3$2@1$1@1$0#5@3$4@1$0#5+h9Kv$3@2$5@1$0#5+h9@3$2@1$1@1$0#5@3$4@1$0#5+haKv$3@2$5@1$0#5+ha@3$2@1$1@1$0#5@3$4@1$0#5+hbKv$3@2$5@1$0#5+hb@3$2@1$1@1$0#5@3$4@1$0#5+hcKv$3@2$5@1$0#5+hc@3$2@1$1@1$0#5@3$4@1$0#5+hdKv$3@2$5@1$0#5+hd@3$2@1$1@1$0#5@3$4@1$0#5+heKv$3@2$5@1$0#5+he@3$2@1$1@1$0#5@3$4@1$0#5+hfKv$3@2$5@1$0#5+hf@1$6@1$1@1$0#5").

Lemma nth_all_regs : ltac2:(zQ "c0!h9!jc!kt4!ks4!n4!kue!lgb!ll6!lm2!ks8!ksd!htb>1n$2>0@2$5^1Ni0@3$4@1$1@1$0#5@4$6@1$1@1$0#5^2$7@3$9@1$0#5ZKv$3@2$a@1$0#5Z@2$b@1$0#5@1$8^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["FPX2"] "##^Dp'0h02Hnh11Hh22n0h31ni001nh44__p1h54__x1h62b1h72b2h83Hn0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1xp%0p;1p;2p;3p;4p;6p;<p;7p;8g0094R0j10Tg010GR1j21Tg004Lj1>Tg007Ij1QTg0051j1c!s/$Oj1;!sU$_j3[Tg00>>R2j1=Tg00OGj2CTg00@\j39!sg$nj2<Tg011Bj3M!s/$fj4@Tg00;ij1JTg00FPR3j2I!sr$^j2?Tg00EAj4YTg012Bj1XTg008Xj2FTg00GPj1VTg0062j1UTg00H0j2T!s/$Nj1P!s/$lj1OTg00J:j2BTg00IWj2NTg00bcj4G!tr$:j1R!t1$gj6STg00K@j2b!s/$bj2DTg00L<j2a!s/$hj3`Tg00MGj4_Tg00`Pl<KTg00a[l<^Tg00cNj7]!t1$@j3ATg002oj8\Tf4R4f3R5f2R6g013KR7f1R8C@f0R939p=W%=9,C8p=4g00hlR:1<89'Dp=2f5R;P4P5P7P6C@!sM%39p=3P6P8P7P9C@p=51?45/?6/?8/?9p=71D:9p=Hg00iJR<P<P:P:P0P2P2f6g014TR=P;P4P!sA0P5P=!s|$9M<KM<Kp=6!sE$1P2P3g0158!sZ$5!sJ'^p=ZP8g002PR;g00iiR3P3g00jIR2P9g00kPF]p=EAA:45=A:6=A:8=A:9p=8P5P;P3P3P2!su%G\p=L%09#0#0#0p=:g00n<R1#0R=#0R0#0R>#0R?#0R@#0RA#0RB#0RC#0RD#0RE#0RF#0RG#0RH#0RI#0RJ#0RK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[,19R\P<g00lWR]#>R^#Q#cR_#;R`P`!uu$hNRag015Z5[_Rb%=8Rc,C_DW^0\P8111[g0166R\%;9Rd%;8Reg00<d%;6?9891<561<5859:Rf[1<681<6959:%;5?968[Rg%;4?956\fAM689P9n20010!s#$12!s-%0W7W6W3RfPg^7e^6d^3\R\P9P_P`P1P7PbC@14_1R112_1O4b1W0P<%09R1/1[P`P`%08R7PbP_P7E3]0P911=[PfP!sk$A5`=b14_=R=12_=!sf,1!sf-7R=!sf$=!sf'0!sf/0b14_0R012_0!sf9=R0!sf$0!sf'>!sf/>b14_>R>12_>!sf90R>!sf$>!sf'?!sf/?b14_?R?12_?!sf9>R?!sf$?!sf'@!sf/@b14_@R@12_@!sf9?R@!sf$@!sf'A!sf/Ab14_ARA12_A!sf9@RA!sf$A!sf'B!sf/Bb14_BRB12_B!sf9ARB!sf$B!sf'C!sf/Cb14_CRC12_C!sf9BRC!sf$C!sf'D!sf/Db14_DRD12_D!sf9CRD!sf$D!sf'E!sf/Eb14_ERE12_E!sf9DRE!sf$E!sf'F!sf/Fb14_FRF12_F!sf9ERF!sf$F!sf'G!sf/Gb14_GRG12_G!sf9FRG!sf$G!sf'H!sf/Hb14_HRH12_H!sf9GRH!sf$H!sf'I!sf/Ib14_IRI12_I!sf9HRI!sf$I!sf'J!sf/Jb14_JRJ12_J!sf9IRJ!sf$J!sf'K!sf/Kb14_KRK12_K!sf9JRK!sf$K!sf'L!sf/Lb14_LRL12_L!sf9KRL!sf$L!sf'M!sf/Mb14_MRM12_M!sf9LRM!sf$M!sf'N!sf/Nb14_NRN12_N!sf9MRN!sf$N!sf'O!sf/Ob14_ORO12_O!sf9NRO!sf$O!sf'P!sf/Pb14_PRP12_P!sf9ORP!sf$P!sf'Q!sf/Qb14_QRQ12_Q!sf9PRQ!sf$Q!sf'R!sf/Rb14_RRR12_R!sf9QRR!sf$R!sf'S!sf/Sb14_SRS12_S!sf9RRS!sf$S!sf'T!sf/Tb14_TRT12_T!sf9SRT!sf$T!sf'U!sf/Ub14_URU12_U!sf9TRU!sf$U!sf'V!sf/Vb14_VRV12_V!sf9URV!sf$V!sf'W!sf/Wb14_WRW12_W!sf9VRW!sf$W!sf'X!sf/Xb14_XRX12_X!sf9WRX!sf$X!sf'Y!sf/Yb14_YRY12_Y!sf9XRY!sf$Y!sf'Z!sf/Zb14_ZRZ12_Z!sf%%01/1[%0Y!sj%c%J]RZP!s$$D7P!s0h%>^#>!s$$JR^'IS00P11?9ZX>:R1P!s$acO1S01O1S02O1S03O1R\O1RfO1RdO1ReO1RgO1RhO1RiO1RjO1RkO1RlO1RmO1RnO1RoO1RpO1RqO1RrO1RsO1RtO1RuO1RvO1RwO1RxO1RyO1RzO1R{O1R|O1R}O1R~O1P1PYP~P1PXP}P1PWP|P1PVP{P1PUPzP1PTPyP1PSPxP1PRPwP1PQPvP1PPPuP1POPtP1PNPsP1PMPrP1PLPqP1PKPpP1PJPoP1PIPnP1PHPmP1PGPlP1PFPkP1PEPjP1PDPiP1PCPhP1PBPgP1PAPeP1P@PdP1P?PfP1P>P\P1P0Q03P1P=Q02P1P7Q01P1P8Pc%HcF6!s$AP[P^%H^EZP9CYQ00%X6%=6,Fap-0R[g00o[Rc#V%Uc1T:8%P:%O:RcP:1B:ag00ji1N:]R]CG,Ec%R3R1PcP:P]1B:ZR]P!s$$D8P!s0hg00l01B:^!t;$P1Pc!#JC'5ESCLCL1bc2P9P6g00gNRcg00gnR2'D1a96=9c2dA`:a8C_b:b;b<X5:W41Fa9P8P!|$r/I^P5[[^5:^4[P9!}x$:4#:!s$/R`!~-$`E3%=4P8P6O4b9b=b8W0X3<P9O1n0110001020111100X2!s>/0!s>~!s>~!s>~!s>~!s>~!s>~!s>+0!s>~!s>uP9O1!{l$o"). Qed.

Lemma regs_ok_by_index : ltac2:(zQ "h20!h9!jc!lgb!kg6!l9!kt4!ks4!n4!kue!lp1!lt5!ll6!kk5!ltd!jp5!mic!ks8!ksd>1E$e>2sr@1$4$3>1R@2$9@1$0#5@1$1@1$0#k0>0>1i$5>0@2$8^1Ni0@3$7@1$1@1$0#k0@2$a^3@4$2@1$1@1$0#5^2$b@3$h0@1$0#5ZKv$6@2$h1@1$0#5Z@2$d^5@4$2$3^2^4@1$cZ@3$f^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["FPX2"] "##9pp'0h03Hr0h12Hxh21bi001bh32H0h44__x1h54__x2h62b1h72b2h81nh91rh:1Eh;1Hh<1Rh=7__arithh>4__ffh?8__varmaph@5__withA1ihB2srp;1p;2p;3p;4p;7p;5p;6p;8g0062j1HTg004Lj16Tg007Ij1[Tg0051j1=!s/$Oj14Tg016Tj2_Tg0094j12Tg010Gj2STg017@j2L!s8$_j3@Tg011fj41!sA$cj1jTg018jj38Tg00Kbj2;Tg00@\j30Tg019Wj1:!tL$nj27!se$Bj3\Tg01:\j1YTg01;:j2X!s/$[j2ATg01<Dj3W!s/$mj3VTg01=Vj2UTg00GPj1RTg00V]j3QTg00H0j2OTg00XHj1KTg01>Bj4M!sA$Nj1N!s/$lj1JTg00IWj2>Tg00bcj4PTg00cNj7?!s\$`j5ITg01?Dj6T!u<$:j1iTg002oj8h!uW$@j2gTg00L<j2f!s/$hj3eTg00MGj4b!se$hj2aTg00OGj2<Tg003nj7`Tg01@Ej1DTg01AVj2GTg00>>j1ETg01B]j2^Tg01Cjj6FTg01DFj1]Tg01E[j2cTg01Fbj3dTg01H0j2BTf0R0#2#2p=Z%2!s0$#2p=5f4R1f3R2f2R3'Bf1R4/G030p=3g00gNR5g00gnR6700p=91B34=020p=Cg01I1g01J7R7#Hg00lWR8#6R9#[#=R:%69#6!s$&=R;#4R<'_g00iJg00n<R=#2R>#2#Z#5!s$/,S0P<P3%4:R?P4g013KR@g00hNRAg015ZRB1L:Ad5@:RCC1P1P7P4P2%jARDC1D3[]AA@:ABRB98:0REP51;50A8:4B=050P5A8:2!s1%<f6RFP1f8RGP5!sm$DP7%:1RHf7RIPDC1RJn010!s#$20000D3]0P4A8:3BRK#9g0166RL%40RM%44RNg00<d%43?040g00hlRO1723172430RP[1734173050O%42?034[RQ%41?023\PA\340P0n20!tC'1!tD$000W7W6W8PQ^7N^6M^8LP0P:P1PBg00o[RL%Y8,XO1AO>5WO1AO=5VOg01K>'U%RL3Q%HLPO1OO3P4%KOCM%NO%JORLg002PR=g00iiR>P>g00jIRMPLP=P>P>!s-'g01KjRNPO1>O8g01LJ1>O9CPR9g00kPR8F?!sY+NDIET%i!sb+PMP9P8F?Gh1gLMP0P31;561f03#9dAeOA4Cbb>b?b@X4OX5O1a04#9A0O43[^4O^5OP017:Bf5RO,7:P3O3b=O4b3A0?2CP?PB%9EP<PGP4f:REPDD3]0X9?A8:BB#91<;A,;<P<PIPBf9RAPDD3eW0P1P0P4F`b3W0g01M1905KP1%:2RK%D2O2P<POP?PKP@PCC1PIP7PKPFP!y{$P?P?PHP@PBC1!t$$0P7%:ORBPGPDC1,GAR@CCX2?P0%EH,<:RK%D1,^HEFP<PFPKPGPJD3P?%EB,<:!u4$0PEP7%:FPA!t2%!sd$PO%]O!s[$IPOP@CCP0b1b1b1W0n01!y<%20101P0O1b0b2P<P3P0P11c20D3eX9?Ad234eW;W<WBW:o"). Qed.
End FPX2.

Section MainEntryProofs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!hj2$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!lp1!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = envv.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  Let E := E0 inp sp0 a0s path envv rdraw tid regs.


  (* LPS-revision port.  These six replays applied p0/p1/auxvp/rnd in their pre-revision
     4-argument form from inside the replay program; a KReplay blob is never re-encoded, so
     each replay is REPLACED BY AN EXPLICIT PROOF (rule 11, and this lane's brief).
     Statement AND tactic text: a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:223-250 -- the PLAIN-TEXT
     TWIN of this encoded file, hunk by hunk, with only the argument lists re-threaded to
     each definition's new generalisation set (p0/p1 lost sp0 because their base is now
     `ed_top rdraw`; auxvp lost a0s/path/envv because they come off inp).  Nothing else of
     beast's file is taken: its LATER sections are still pre-revision. *)
  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] ++ junk_vals regs ++ [a_hwcap; canary_w rdraw]) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma length_junk_vals : length (junk_vals regs) = 32%nat.
  Proof. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + i)%nat.
    rewrite app_nth2_plus. rewrite app_nth1 by (rewrite length_junk_vals; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma ev_38 : ev E 38 = a_hwcap.
  Proof.
    rewrite ev_vals. change 38%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + 32)%nat.
    rewrite app_nth2_plus. rewrite app_nth2 by (rewrite length_junk_vals; lia). rewrite length_junk_vals. reflexivity.
  Qed.

  Lemma ev_39 : ev E 39 = canary_w rdraw.
  Proof.
    rewrite ev_vals. change 39%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + 33)%nat.
    rewrite app_nth2_plus. rewrite app_nth2 by (rewrite length_junk_vals; lia). rewrite length_junk_vals. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!hj2$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!lp1!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!h9!jc!r2>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : ltac2:(zQ "10!oo8@1$0?3sp0").
  Hypothesis Htid : ltac2:(zQ "50!h9!op3!p6!mof!op8@2$3@2$1Z@2$2@1$0#k0?3tid@2$1@2$2@1$0#k0?3tid@2$4+2+h6").
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = envv.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  Let E := E0 inp sp0 a0s path envv rdraw tid regs.

  (* LPS-revision port: main_entry's register facts are now stated over the ProcInput --
     me_s1/me_a0 give `argcN inp` and me_a2/me_s3 `length (in_argv inp)`, where the
     pre-revision record gave them over `av`.  `Hargv : in_argv inp = av` is what closes the
     gap, so each of those four arms rewrites with it; the remaining arms are beast's text
     with one more underscore (main_entry gained an explicit argument).
     Donor, tactic text: a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:271-289.
     Found with the UNCLOSED-GOAL probe (rule 10), not by reading: the trailing `idtac`
     made every miss silent, and the goal it printed was `getr regs 9 = Z_to_bv 64 2`. *)
  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ unfold E; rewrite (spx_val inp sp0 a0s path envv rdraw tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk inp sp0 a0s path envv rdraw tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ ME); rewrite ?Hargv; f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ ME); rewrite ?Hargv; f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite ?Hargv; cbn [length Z.of_nat Pos.of_succ_nat]; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite ?Hargv; cbn [length Z.of_nat Pos.of_succ_nat]; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ ME); cbn; tauto
                | fail 99 "UNCLOSED-GOAL" ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
End MainRegs.

Section KnowProofs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!hj2$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!lp1!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!h9!jc!r2>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : ltac2:(zQ "10!ope@1$0?4envv").
  Hypothesis Hvsp : ltac2:(zQ "10!oo8@1$0?3sp0").
  Hypothesis Htid : ltac2:(zQ "50!h9!op3!p6!mof!op8@2$3@2$1Z@2$2@1$0#k0?3tid@2$1@2$2@1$0#k0?3tid@2$4+2+h6").
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = envv.
  (* LPS-revision port.  The revision's auxv_words takes the hwcap OFF THE ProcInput
     (`in_hwcap inp`), where the pre-revision one took the ambient `a_hwcap` directly, so
     the AT_HWCAP value bullet needs the same bridge Hargv/Hve' already give for argv and
     envp.  MEASURED, not guessed: the UNCLOSED-AUXV probe in a farm round
     printed exactly
       Some (word_to_le_bytes 8 (in_hwcap inp)) = Some (word_to_le_bytes 8 a_hwcap).
     IT IS NOT A PREMISE THE TOP CANNOT MEET, which is the test that governs: MainOpen and
     MainTop build their inp as `mkProcInputC [a0s; path] envv fs0 stdin0` (Amb.v:36-40),
     whose in_hwcap field IS a_hwcap, so there it is reflexivity -- the same discharge
     Hargv and Hve' already get. *)
  Hypothesis Hhw : in_hwcap inp = a_hwcap.
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  (* LPS-revision port.  The stack-reading helpers moved into RefLayout.v's Section Layout
     and ArgvEnv's, which thread the LAUNCH as well as the stack: their exported types, read
     off a farm round's About probe rather than inferred, are
       read_argc_w    segs v inp mbase ph entry sp brk draw  Hvl Hlau Hhi
       read_argv_ptr_w segs v inp mbase ph entry sp brk draw Hva Hvl Hlau Hlo Hhi k Hk
       read_argv_null segs v inp mbase ph entry sp brk rdraw Hvl Hlau Hhi
       read_auxv_word segs v inp mbase ph entry sp brk rdraw Hvl Hlau Hhi j Hj
       lay_bsb_len         v inp mbase ph entry sp brk rdraw Hvl Hlau
       rnd_facts      segs v inp mbase ph entry sp brk rdraw Hvl Hlau Hlo Hhi Hal
     so this section gains `brk`, `Hvl : valid_launch inp` and `Hlau`.  It does NOT need a
     `v` or a `ph` variable: `v` is Sv48, which valid_input pins (conjunct 11 of 17 at
     75d69e00:Run.v:4590) and which RefStartup.v:167 already uses, and `ph` is RPH, which
     main_entry's own me_mem names (RefStartup.v:118).
     BOTH NEW HYPOTHESES ARE DISCHARGED BY THE LAYER ABOVE, so neither is a premise the top
     cannot meet: `valid_launch inp` is conjunct 13 of valid_input (75d69e00:Run.v:4592), and
     `entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp` is already a Hypothesis of
     this tree's own ref_startup (RefStartup.v:132). *)
  Variable brk : word.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Let E := E0 inp sp0 a0s path envv rdraw tid regs.

  (* LPS-revision port.  These replays applied the pre-revision forms from inside the replay
     program; a KReplay blob is never re-encoded, so each is REPLACED BY AN EXPLICIT PROOF
     (rule 11).  Statement AND tactic text: boost-beast/http_request's
     proofs/lib/RefMainEntry.v:291-327
     -- the PLAIN-TEXT TWIN of this encoded file -- with the argument lists re-threaded to
     each definition's new generalisation set.  Nothing is taken from beast below :327. *)
  (* LPS-revision port.  The stack readers now state their argv premise over the
     ProcInput (`valid_argv (in_argv inp)`), where the pre-revision form took it over the
     section's `av`; `Hargv` is exactly the bridge (a farm round named this
     at line 415).  Stated once rather than inline at each use. *)
  Lemma kva : valid_argv (in_argv inp). Proof. rewrite Hargv. exact Hva. Qed.
  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 inp a0s path envv rdraw. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 inp a0s path envv rdraw. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp inp sp0. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd inp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
  Lemma ke38 : ev E 38 = a_hwcap. Proof. exact (ev_38 inp sp0 a0s path envv rdraw tid regs). Qed.
  Lemma ke39 : ev E 39 = canary_w rdraw. Proof. exact (ev_39 inp sp0 a0s path envv rdraw tid regs). Qed.

  (* LPS-revision port.  Replay replaced by an explicit proof (rule 11); the STATEMENT is
     untouched.  Tactic text: a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:329-364, the plain-text
     twin, with every argument list taken from the types the About probe printed in
     a farm round -- not inferred.  v is Sv48 and ph is RPH, as explained
     at the Section header. *)
  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    (* the KWr bullet's own range side: the window is now symbolic, so lia must be shown
       stack_window_reach and stack_max_size here too (a farm round put the
       first error at this line's `lia`, chars 14-17, after the window fix cleared the one
       below it).  Separate try-unfolds then a tactic that must close. *)
    - split; [try unfold stack_window_reach; try unfold stack_max_size; lia|]. intros d m Hd Hm.
      (* The lower bound moved with the revision: main_entry_store_ok_win now asks
         MemSplit.wok_lo sp0 <= bv_unsigned a, where the pre-revision form asked
         bv_unsigned sp0 - stack_max_size <= bv_unsigned a.  wok_lo is
         bv_unsigned sp0 + stack_window_reach - stack_max_size (MemSplit.v:137-138), so
         stack_window_reach has to be unfolded too or lia is handed a name it cannot see
         through and answers "Cannot find witness" -- which reads as an arithmetic failure
         about the node and is not one (a farm round, line 354 chars
         128-131, i.e. the trailing lia, counted against the line).
         Separate `try unfold`s followed by a tactic that MUST close, so a unfold that
         finds nothing cannot silently become the step. *)
      apply (main_entry_store_ok_win inp mbase entry sp0 rdraw tid regs mem ME);
        (* unfold in * , not just in the goal: Hd/Hm bound d against the window and were
           stated with the names, so unfolding only the goal leaves lia comparing an
           unfolded conclusion with folded hypotheses.  The probe printed exactly
           `0 <= bv_unsigned sp0 + (2244095 - 8*1024*1024) + d < 2 ^ 64`
           (a farm round), which is immediate from kp_lo once d's own
           bound is in the same vocabulary. *)
        rewrite u_small by (try unfold stack_window_reach, stack_max_size in *; lia);
        try unfold MemSplit.wok_lo, stack_window_reach, stack_max_size in *; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by lia.
      pose proof (read_argc_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hr. unfold wmem in Hr.
      rewrite Hr by (unfold sp_window_hi; lia).
      (* argcN is over the ProcInput at this revision, so the goal closes with Hargv
         rather than by reflexivity: a farm round printed
         Unable to unify "Some (word_to_le_bytes 8 (Z_to_bv 64 2))"
                    with "Some (word_to_le_bytes 8 (argcN inp))".
         Same move as reg_case's me_s1/me_a0 arms. *)
      rewrite n_to_le_8_spec. unfold argcN, len_word. rewrite Hargv.
      cbn [length Z.of_nat Pos.of_succ_nat]. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw kva Hvl Hlau
                    ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat
                    ltac:(rewrite Hargv; subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      (* read_argv_ptr_w's conclusion is over the ProcInput's own argv/envp at this
         revision, where p0 is stated over the section's av/ev
         (a farm round, line 424: p0 … vs cat_argv_ptr … (in_argv inp)
         (in_envp inp) …).  Hargv/Hve' are the bridge. *)
      rewrite Hargv, Hve' in Hr.
      rewrite Hr. unfold p0. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw kva Hvl Hlau
                    ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat
                    ltac:(rewrite Hargv; subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hargv, Hve' in Hr.
      rewrite Hr. unfold p1. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_null RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                    ltac:(unfold sp_window_hi; lia)) as Hr.
      rewrite w_add_nat in Hr. rewrite Hargv in Hr. subst av.
      change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  (* LPS-revision port.  Replays replaced by explicit proofs (rule 11); statement and
     tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:366-387, re-threaded.
     ONE STATEMENT CHANGE, and it is a STALE CONSTANT rather than a port artefact:
     auxvp_u's second conjunct read `auxv_off av envv + 160 <= 2240000`.  The 160 is the
     PRE-REVISION auxv size IN BYTES; at 75d69e00 the block is `auxv_size (kb_rseq …)`,
     16 * 27 or 16 * 29 (StackLayout.v:276-277).  Written parametrically, so kb_rseq -- one
     of recorded_kernel's five FREE fields -- is never pinned.  The bound 2240000 is
     unchanged and has ~2.2e6 of slack, so no consumer loses anything.  auxvp_u is
     file-private to KnowProofs, nothing published is touched, and no hypothesis is
     strengthened.  UNIT: BYTES. *)
  Lemma auxvp_eq : auxvp inp sp0 = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. rewrite Hargv, Hve'. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp inp sp0) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + Z.of_nat (auxv_size (kb_rseq (in_kernel inp))) <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    (* Helper arities read off the About probe (a farm round), not inferred:
         auxv_off_bound inp mbase ph entry sp brk rdraw
         lay_bsb_len  v inp mbase ph entry sp brk rdraw Hvl Hlau
       and both conclusions are now stated over the ProcInput's own argv/envp, so Hargv and
       Hve' bridge them to this section's av/envv. *)
    pose proof (auxv_off_bound inp mbase RPH entry sp0 brk rdraw) as Hb.
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl.
    rewrite Hargv, Hve' in Hb.
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.

  (* LPS-revision port.  `rnd` is this section's name for the AT_RANDOM pointer and
     rnd_facts now states every one of its facts over `in_argv inp` / `in_envp inp`;
     the bridge is stated once here rather than at each use. *)
  Lemma krnd : rnd inp sp0 a0s path envv
    = at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp).
  Proof. unfold rnd. rewrite Hargv, Hve'. subst av. reflexivity. Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd inp sp0 a0s path envv))%Z
    /\ (bv_unsigned (rnd inp sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rnd inp sp0 a0s path envv) mod 8 = 0)%Z.
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl.
    destruct (rnd_facts RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
      as (A & B & C & D & F).
    rewrite krnd. repeat split; try assumption; try lia.
  Qed.

  (* LPS-revision port.  a farm round named THIS STATEMENT, not its replay:
       "auxvp of type ProcInput -> word -> word cannot be applied to sp0 a0s path envv".
     A CDef/KReplay blob is never re-encoded, so the lemma is written out (rule 11).  The
     encoded string was decoded symbol by symbol before anything was written, and it says
       forall j, j < 20 ->
         rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
         = Some (word_to_le_bytes 8 (nth j (auxv_words RPH (rnd sp0 a0s path envv) a_uid a_hwcap)
                                       (Z_to_bv 64 0)))
     which is character-for-character boost-beast's plain-text twin at
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:389-402.  TWO things moved
     and both are read off the About probe (a farm round), not inferred:
       auxvp      ProcInput -> word -> word                     (was sp0 a0s path envv)
       auxv_words LaunchAuxv -> PhdrInfo -> word -> word -> word -> word -> word -> word
                                                                (RefLayout.v:110)
     The word list is written exactly as read_auxv_word's own conclusion spells it
     (RefLayout.v:354), so the two cannot drift apart.
     THE BOUND MOVES FROM 20 TO 50, and that is a WIDENING, never a narrowing: the
     encoded `j < 20` covered the pre-revision 10-pair vector, and the revision's table
     (printed by a farm round) puts the slots kn_auxv claims as far out
     as word 49.  50 is still a sound INSTANCE of read_auxv_word's own
     `j < 2 * auxv_count (kb_rseq (in_kernel inp))`, which is 54 when kb_rseq is false
     and 58 when it is true, so the instance is discharged below from kb_rseq's own case
     split and kb_rseq is never pinned.  Nothing published reads this lemma: its only
     consumer is know_auxv, in this section.
     UNIT: WORDS for j, BYTES for the 8 * j offset. *)
  Lemma auxv_word_at : forall j, (j < 50)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8
        (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp)
                  (in_hwcap inp) (rnd inp sp0 a0s path envv)
                  (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
           (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME)
      by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite Hargv, Hve'; rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
               ltac:(unfold sp_window_hi; lia) j
               ltac:(unfold auxv_count; destruct (kb_rseq (in_kernel inp)); cbn; lia)).
    rewrite krnd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  (* The auxv list the revision builds is a literal 26-pair cons list followed by an
     la_rseq-dependent tail and AT_NULL (printed by a farm round), so
     `nth j` reduces through the literal prefix for every j this file claims (max 49)
     WITHOUT touching the rseq branch -- which is why kb_rseq stays free here.  The cbn
     list has to name auxv_entries, app and flat_map, not just nth, or nothing reduces. *)
  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia;
    cbn [auxv_words auxv_entries flat_map app nth fst snd];
    rewrite ?ke38, ?Hhw;
    reflexivity.

  (* LPS-revision port.  Same series as know_stack (rule 11g): this replay constructs and
     destructures the same widened records, so it is converted in the same pass rather
     than left to fail on its own.  Statement unchanged; tactic text from the plain-text
     twin a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:411-425, re-threaded.
     One addition over the twin: kn_auxv's two KDisj entries now carry the window
     symbolically, so the names have to be unfolded IN HYPOTHESES TOO before lia -- the
     lesson a farm round..be135b paid four rounds for on know_stack. *)
  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4, ?ke38;
      unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4, ?ke38;
      try rewrite Hau;
      try (unfold stack_window_reach, stack_max_size in *; lia);
      try lia.
    - split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
        with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
    - kw_auxv 20%nat. - kw_auxv 21%nat. - kw_auxv 22%nat. - kw_auxv 23%nat.
    - kw_auxv 26%nat. - kw_auxv 27%nat. - kw_auxv 28%nat. - kw_auxv 29%nat.
    - kw_auxv 30%nat. - kw_auxv 31%nat. - kw_auxv 38%nat. - kw_auxv 40%nat.
    - kw_auxv 46%nat. - kw_auxv 47%nat. - kw_auxv 48%nat. - kw_auxv 49%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12b950) 8
    = Some (word_to_le_bytes 8 (auxvp inp sp0)).
  (* LPS-revision port.  a farm round named this replay: it applies
     `envp_w sp0 av`, and RefStartupDefs.v's Section Defs now exports envp_w/auxv_w over
     the ProcInput (`envp_w inp sp0`).  A blob is never re-encoded, so the proof is
     written out (rule 11); tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:434-439, with auxv_w
     added to the unfold list because `auxvp` is one indirection deeper here
     (RefMainEntry.v:120, `auxvp := auxv_w inp sp0`).  The statement is untouched. *)
  Proof.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    (* RULE 15: the donor's unfold list is checked against THIS cone before use.  beast
       names D_cx; boost-json's RefStartupDefs.v:181 declares D_cxx and no D_cx, and its
       D_main is D_cxx (D_fd (D_ssp (D_tls tid D_libc))) at :191. *)
    unfold auxvp, auxv_w, D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)

  Lemma wseg_data : ltac2:(zQ "e0!ns3!qb!rb!ns9!nsf!nt5!n4!nue!oh2!h9!om1!no7!htb!oqb@3$6$1@3$a$b@2$c@1$9#k0+vpgg0@1$7@1$8@1$d@1$4@1$0@1$0@1$0$5$2").
Proof.
vm_compute. reflexivity. Qed.   (* [comment removed for export] *)

  Lemma range_disjoint_sub : ltac2:(zQ "a0!s2!qb!kt4!rb!n4!omc!mp5!p1!oo1!lm2>2lo$0>1n$2>1c@2$8$0$2>1i$0>0@3$4$1@3$5^4^3^2$3>0@2$7^5^2>0@2$7@2$6^3+1@2$6^6@1$9^5@3$4$1@3$5^4N1^5$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["KnowProofs"] "##Eyp'0h01Hh12b1h22b2h35lemmah41xh52H0h62Hah74__x1h84__x2h94__x3h:4__x4h;4__x5h<1ih=1ni001nh>1yh?1Ah@1BhA3HhihB3HlohC7__arithhD4__ffhE6__sat1hF!s/%2hG8__varmaphH5__withI1chJ2c0hK4cstrhL5cstr0hM2lohN1mhO1wi011pi021zp&0p;2p;3p;1p;4p;8p;<p;6p;=p;7p;;p;Bg03S^R0k202Tg00A6j3ATg008XR1j20Tg00;ij1ITg00>^R2j21!s1$>R3j13Tg0094j1?Tg00]oj4MTg03emj2<Tg00[AR4j24Tg03fJj2\Tg00?;j26!s8$jR5j2>Tg03gCj4BTg000Sj4y!s8$jj2sTg03hWR6j2pTg03i5j4k!s/$Wj8GTg03jJj3eTg00C`j2CTg00D@j1_!s/$^j4^Tg00Kbj27Tg00a[l<ZTg00e\j3YTg00fBj6XTg012Bj1LTg004Lj1JTg007Ij1KTg00Ehk20!ui$FPj2WTg00<Gk20!v8$Flj3~Tg01;[j2;Tg01<mj3=Tg01=Vj2UTg00GPj1{Tg00V]j3TTg0062j1xTg00XHj1wTg00H0j2RTg01>Bj4E!s8$Nj1r!s/$lj1oTg00IWj2:Tg00J:j2nTg00b@j3HTg00@:j1j!ub$@j2iTg00L<j2l!s/$hj3mTg00MGj4h!tC$fj4gTg00^Oj3f!s/$lj3q!sn$\j3STg03k@j4tTg03l3l=dj7u!s2$bl;vTg00`Pl<c!vp$5lBb!tX$cj4zTg00cNj7a!vy$jj7|Tg002oj8}Tg00gNR7f0R8g00gnR93Sp=2p-0R:f1R;P5P8CBp=DP:f4R<P5P5f3R=f2R>P;P8GGp=Q16;8=S79p=5P:P5P;P8Ctp=@P8P;P4g03m]R?P>g00kPR@P=P<f5RAf6RBf7RCf8RDf9REM=dp=VP:!si$5P8P5P6g03nNGGp=`P=P>P4P?P;P@P8Fup=PP:PCP5PBP4PAP<!sG$;P8M;vp=Ng00iJR4g00hlR?P?P?P3P3!sN0<cp=]!s@$!s$'2!u#$>P2P=P<PAPBPCPDPEMBbp=[P?P;g00jiP8Czp=9!s4$2PR2g00iiR3P3g00jIRFP8P@Fap=8!sp$3P3PFP;P8F|p=OP=!s9+!v]%}p=F202?4P0P?P4AA<=;#210A;g00lWR0#IR2,1>R@%3A,1BRG'0g00n<RH#?RI=A=<#2[[[^<?P8P?P4P>P;CM9ACB#210D;%3D,1ERJ,0@g00<dR@1<;8#2%2>RK%2;RL'4RM[RN%28,4L1<>;#2RL[RO%2=/4K\L1\;8RLP;n20010!s#$12!s-%0X27X17PN^27^17P8f;RKf:RP#3RQ'1/6BRR16GKRGP=O3%2R%2G'4P@PNPO1<=>#2\MPLP8!t%>O!t%'%3IRO,1BRL/6DRM%3C,1DRN/6B%2M10LD'>P:^@:RM^?:R@P:\:!yb'CBRG'DRR!s6&!s>%6CyRSCBRT,DMRUPM1s:5RVPGPT!zA+VP5PSP:P51p8;X>:X4:g03o?CkGGDQRS11CORW/5E10WEP815JCRWPWg04059e:5RX/@WM:VW31CLDf=RLf<#3'1RY/5D10YDRZ'>P@P!tg'6CBR6,DMR5PMPVPGP6%`VDQRVf>RG%3L'1R@!t<$@ER@!t>$GR[P[1@X[!t4&YDP;O215NL,4Z10JC,>WPMPTPM\:RTPRPUPSCP11DORS/0PRU1@XU%3E,1PRE!tc$EDRWP8GNW31CJC10JGRC,>[PMP6PTPRP5PVCPf?RV%3GR5'1/0PRR1@XR15EV10EV!sc+GP8O214@C14UWRC11D2R@/0PRJ/4WPUPWPJPW!}-$1P8X4?RJP110;8#_X>?X4?PSP@PJ!s$$?P?g00n[11;8C^,7?XN?X=?PDPD17?DPOP2PJPJ%38,7?X44PIP217?2E]M:[PPPP17?PM<Z17:W9YWWEX%LGg00hNRG/05%LP10GQ%J0RQ#IRW%KQR:#K#J#IRJ+011WGW10GJ200WJRD,WG[[10GWR@g00o?RSA~WJ;UW610GD\S^6!s>$[R@%?IRS#?RD,;?1;?SRS1;?H5=?5=?g01K>RH'U%?!sE&I9=?S5=?/UH%{@5T@3T%x@P?P?%w?R@P>1R?ACEP;P?1R?<P=P@CECE%r?%o?R@1:?0RH1n?25H?RS1:?:R:%K0R0#J,:?5H?RD'9,8@%j3R3P@19:H,8@P3P@1:?QRQ,9D,8!sm$9H?QR0/9:,8@5O@P319SQ,8@190H!s9%CFCFCF1i@FP8P>17791l8>#2dAm?G;ChbDbGbHX7?X8?X9?X:?X;?118211=<RG'010<;11AB/0=10GA'411=2/0<11<A/0='4[[[^7?^8?^9?^:?^;?P8fC#3fD!}P$LPPPKPAO8bCbEbFbLbKCgPCeb0O2b0O2O3b5b0b511=OP?!#8q$CMR<9f?4RA'6Aq?4<#3,1A/6='<#2eAA=I<#2eWAWBW0X<?XO4XI?P;P8O2n2001101000121102100WJX=4XM?o"). Qed.

  Lemma missb_sub : ltac2:(zQ "90!qb!rb!n4!s2!hsb!mp5!p1!kt4!lm2>2lo$3>1n$7>1i$3>0@3$2$0@2$4^3^2$1>0@2$6^4^2>0@2$6@2$5^3+1@2$5^5@1$8^4@3$2$0@2$4^4N1$1").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["KnowProofs"] "##G,h01Hh14__x1h24__x2h31xh41nh51mh67__arithh74__ffh86__sat4h9!s/%5h:8__varmaph;5__with<4__x3h=2b1h>2b2h?4cstrh@1AhA2H0hB2H2hC2H3hD2HahE1fhF1lhG2H1hH2HchI3HhihJ3HlohK1chL1ihM2lohN1yp;2p;1p;3p;6p;4p;7p;<p;8p;Bg009Sj2RTg008XR0j22Tg00;ij1CTg00>^R1j21!s1$>R2j13Tg00=`j24Tg00<dR3j2?!s:$?j2\Tg03S^j2ZTg004Lj1:Tg007Ij1;Tg00?;j26Tg0094j1QTg00C`j2gTg0062j1OTg040ej3ATg029Xj3ITg041Aj3MTg00A6j2Ej3LTg01fhj6[Tg012Bj1DTg00Ehj2YTg00FPj2K!tl$Gj2X!s8$lj3WTg00GPj1VTg00H0j2JTg00XHj1UTg01>Bj4@!sA$Nj1T!s/$lj1STg00IWj2BTg00@:j1rTg00K@j2q!s/$bj2<Tg00L<j2p!s/$hj3oTg00MGj4lTg00J:j2HTg00b@j3G!uH$dj7hTg01;[j2FTg01<mj3PTg01=Vj2fTg00V]j3eTg02Mkj4NTg00D@j1b!s/$^j4cTg00a[l<`!u<$fj4i!tp$\j3_!t:$cj4jTg00cNj7kTg002oj8^Tg00`Pl<m!se$5lBnTg00gNR4f0R5g00gnR63_p=0f2R7f1R8/E5g0437R93Ap=5g00hNR:/65p=9%:5#:p==12:5p=7AA859p=]P7g002PR;g00iiR<P<g00jIR=g00hlR>P8g00jiP5Cjg00kPFkp=8f3R?P;P<P<P=P7P8P5G^p=>g00iJR;P>!s$$2P2f5R2f4R@P?!sL%M<mp=d!sF&!s$%1P5P8P7P1P?P@P2f6R1f7RAf8RBf9RCMBnp=a1R78#012?8g00lWRD#CRE,17RF%3?,1@'2P31485#0%07RG%08RH'?RI[RJ%05,?H1478#0RH[RK%0?/?G\H1\85RHP8n20010!s#$12!s-%0X>4X=4RGPJ^>4^=4RLP51Z>;RM?512%91RN'4RO%32,11%:DR2#:RP#;#:#;!s+&=!s$-CRQ'6RRP?O3%0O%0R'?P3A5MA1%9A'4#0%31,1A/6Q#0g00n<RA#QRR95M1/4N%3RRN,11/6Q'4#0P5A5MCB%9C'4#0f:RB%3C'1!sc$PGPLP5f<RLf;55MRG%9LROP7O3%0G%0O'?P3f=RG=5ML#0%9G#0A5MLR/4O11LN!t0+f?f>55M#0f@#9#0P31685#01278RL[RO1285RG16!vs$S[RT12?7\S1g85RS!vq:5>X4>RUPO^5>^4>RVP5P:fBRWP8O3%7WPUPVP5fDRVfC#3'1RUPQPCO312UQP3PJPK14?7#0\IPHP5!w|>HPK!w|&K!vJ$VR%9V'4RI11VN/6QRV%0I%0VPHPKP5fERK=5MRRH%9KRV%0H%0Vg044Gp4p710RVP4\5RH%O8RIP3AA785#0AI@57P@P8O1#0[^3?RJ[AI?58P?!s:+7AA?78#0[RUAA@!u1$JAM785!u49WFWEW@PU^FI^EH^@VP5PMfFRV/ERP9AIM59RHfJRIfIRUP8fHRJ1EIUR@,]M#0fMRWfLRX;L8#0\H^3M[fKRY=LX!s6'A5MYI#0[AMM@9PBP8P5E[%DURB%3U#7R@%C2R9%;2!{#$CRH'YRZ1K:9%7H1X9HR[,K:[[R\%79R]g00o?R^AW9H8UWDRH%7[\^^D]!sA%[R^#VR[%O^R9P>1J>7R_P8%U>R`C@%T>Ra%S>Rb1B>DRc1B>2R258bRd%r<R<PdC>1qb=R=P5P71<461p57#0dAo>:8ClR6b7b:b;X1>X2>12581287[^1>^2>P5PXfNR4PIO3b6b8b9b?PBP@PZP\PHP]P[P9P>P_P81J>?R@C@PaPb1H>E9G>cRB%;D,B>RD9G>!ta$2P<P2C>P=P!tD0X<>115E1187'2R2118E117?Rd'2!tW&^<>P5%3WP4PXPUO4!t['FhWHXKMO4b0P3POPT16!y2$LPS!{=:!|H%SPT!|H&TP5P:PVfGRL#D%3L#7!uS'%QR,F>1F>R1F>A5P>5P>g01K>'f=e^[R!ur%`P8P_!un%A8bDcP<!uw$:R:=8bDP<A8b:cC>!uk5%77R7P7[\G!w2,PIPJPC!uU,O3b0CNO3b0PSPTP511KNRTPQ12TQRS11KERC/2QP>P>P0P5X3>RJP0%bGXN>X3>PTPCPJ!s$$>P>g00n[1185Cc,<>!v#%PKPK1<>KPNPEPJPJ%35,<>X3;PRPE1<>EEdM:aPQPQ1<>QM<`%DV%3V!vC,!xp&>P@P?P`C@!v+,1B>P9G>DRD98bB!v5&QRP9!v5'BP!v57X<>12dQ12FQ[\2!xl0IPYPUPVP1O5!v?'CiPSe!vD,bCb0bBb0WBWGP8P5O2!xr0!s/&b0bAWCW0!sHA1R?R#0eWIWJW0XL>X4;XM>o"). Qed.

  (* [comment removed for export] *)
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x12d000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  (* LPS-revision port.  a farm round named this replay: it applies
     `D_main sp0 av envv a_hwcap rdraw tid`, the pre-revision 6-argument form, and
     RefStartupDefs.v:191 now reads `D_main inp sp0 rdraw tid`.  Written out (rule 11);
     tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:465-474, re-threaded to
     this file's OWN already-ported D_main_none (:55, whose argv premise is over
     `in_argv inp`, hence kva) and to RefStartup.v:351's main_entry_mem_data.
     The statement, including the 0x12d000 bound, is untouched. *)
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _].
      apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 rdraw tid regs mem ME)
      by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none inp sp0 rdraw tid i kva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  (* LPS-revision port.  a farm round named this replay: it applies
     `D_main sp0 av envv a_hwcap rdraw tid`, the pre-revision form.  Written out (rule 11),
     shape from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:487-507.  The bullets
     below are NOT transcribed from beast: boost-json's kn_image is a different list with
     its own addresses, so only the LEADING TACTIC is ported; the nine bullets were then
     read off rule 3o-FINAL's one-round all-goals probe (a farm round),
     which printed every remaining goal at once.  Every address below is this file's own. *)
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5, ?ke38, ?ke39;
      unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    (* The nine goals the probe printed in a farm round, in order, with
       boost-json's OWN addresses (RULE 22 -- beast's are different and are not used):
         1019904 .. +212992 the writable image window  (0xf9000, 0x34000, hi 0x12d000)
         1095152 D_main_self   1095184 tid   1095336 canary   1226488 guard
         1227088 auxvp        1227128 pagesize       1227184 hwcap      then tid's range.
       The helper argument lists are the generalisation sets RefStartupFacts.v's
       Section Facts produces (inp mbase entry sp0 rnd tid, then Hva, then regs mem ME),
       restricted to what each lemma uses -- read off the section, not guessed. *)
    - split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xf9000) (Z_to_bv 64 (0xf9000 + d))
                0x34000 m 0xf9000 0x12d000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data
        | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self inp sp0 rdraw tid).
      (* main_entry_tid/main_entry_guard generalise Hlo as well (their Section Facts
         hypothesis `0x7fff80000000 <= bv_unsigned sp0`); a farm round
         named the slot. *)
    - kw_mem (main_entry_tid inp mbase entry sp0 rdraw tid Hlo regs mem ME).
    - kw_data (D_main_canary inp sp0 rdraw tid); rewrite ?ke39; reflexivity.
    - kw_mem (main_entry_guard inp mbase entry sp0 rdraw tid Hlo regs mem ME);
        rewrite ?ke39, ?(canary_bytes_w rdraw); reflexivity.
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize inp sp0 rdraw tid kva).
      (* LPS-revision: the hwcap cell now holds `in_hwcap inp` (RefStartupFacts.v:149-150
         carries the same note), where kn_image claims the ambient a_hwcap.  Hhw. *)
    - kw_data (D_main_hwcap inp sp0 rdraw tid); rewrite ?Hhw; reflexivity.
    - lia.
  Qed.


  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
Proof.
ltac2:(KReplay.run1 (kr_t_RefMainEntry ()) ["KnowProofs"] "h01Ah11Hh21Ph32l1h42l2p;1p;3p;2p;4g0062j14Tg01Sfj31Tg04NKj30Tg00<dR0j22Tg04Nlj47Tg02Ehj36Tg02Mkj43Tg02lWj45Tg04OKp4p710R1f0R2p-0[R3f1R4#4R5f2R6#4R7P0f3R0A1042706f4R8?006A0804'2R9[A0064A0062'2A18649080[R:f5R;A1;06708\9P0P6P4P2C7P2n2001000000120000000W4W3W2W0R4P:^47^35^23^01R1P2g030IR3g032VR5p,1ER7p,3memR:36R6g03;SR0g03Y2R9g04MBR8513R;A0360A036;g04OhP4P1P2P3P6P9P8A0369A0368g04Q3g04R=C3O5b1C3O5b1P5P7P:g04SHC5eo"). Qed.

  (* [comment removed for export] *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z   (* [comment removed for export] *)
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  (* LPS-revision port.  a farm round named this replay at `lay_bsb_nw`,
     the last of the pre-revision argument lists in the file.  Written out (rule 11);
     tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:521-538.  Every one of
     the seven helper argument lists below is READ OFF the About probe in
     a farm round, not inferred, and they do not all take the same
     prefix -- argv_ptr_bounds_at takes no ph and no entry, struct_av_bound takes no
     launch hypotheses, argv_str_len takes only inp and its argv premise:
       lay_bsb_nw          v inp mbase ph entry sp brk rdraw Hvl Hlau Hsp_hi
       argv_ptr_bounds_at  v inp mbase sp brk draw Hlau k Hk
       u_cat_argv_ptr      v inp mbase ph entry sp brk rdraw Hvl Hlau Hlo Hhi k Hk
       struct_av_bound     inp mbase ph entry sp brk rdraw
       argv_str_len        inp Hva k Hk
       read_argv_cstr_k    v segs inp mbase ph entry sp brk draw k Hlau Hk
     All of them now state their conclusions over `in_argv inp` / `in_envp inp`, where
     this section's statement is over av/envv.  THE BRIDGE GOES ON THE GOAL, not on the
     hypotheses: `rewrite ?H in H1, H2, …` left them untouched and cost two rounds
     (a farm round and another farm round both printed the same unclosed
     side goal, and `exact B1` missed it because B1 was still in inp form -- `in_argv inp`
     is not CONVERTIBLE to av, only propositionally equal).  One `rewrite <- Hargv,
     <- Hve'` on the goal puts the whole statement in the helpers' vocabulary and every
     use then matches directly.  The statement itself is untouched. *)
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Hargv; subst av; cbn; lia).
    pose proof (lay_bsb_nw Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                  ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (argv_ptr_bounds_at Sv48 inp mbase sp0 brk rdraw Hlau k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                  ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound inp mbase RPH entry sp0 brk rdraw) as Hsb.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (argv_str_len inp kva k Hk') as Hlen.
    pose proof (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k Hlau Hk') as Hr.
    rewrite <- Hargv, <- Hve'.
    repeat split.
    (* The first side goal is B1's statement.  It takes BOTH branches in general and the
       `first` is not scaffolding: a farm round showed that after the
       goal-side bridge it is `lia` that fires here, while before the bridge only
       `exact B1` could have.  Measured by the UNCLOSED-MSTR probes in
       a farm round and another farm round. *)
    - rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME)
        by (first [ exact B1 | lia ]).
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw.
      unfold wmem in Hw. rewrite Hw by lia.
      exact Hr.
    - exact B1.
      (* The span bullet needs the stack image's LENGTH bound, which beast's context got
         from a differently shaped helper.  Here it is lay_bsb_len (RefLayout.v:387,
         length <= 2101782), and with Hu's equality, Hsb's layout bound and Hf's
         firstn <= total it gives cat_argv_ptr <= sp0 + 2101782 <= sp0 + 2107576.
         a farm round named this `lia`. *)
    - pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl. lia.
    - exact Hlen.
  Qed.
End KnowProofs.
(* [comment removed for export] *)
