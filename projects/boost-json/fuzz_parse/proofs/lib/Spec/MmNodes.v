(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the mmap decline premise (place_declined_b), the system-call robustness premise (sys_rob). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import AllocTop VmKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg RelSpec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MmNodes () := KReplay.lz_vm "#&+lC47Corelib7Classes9Morphisms6Proper!sI5?Relation!sY'Reflexive!sR-Program6Basics4flip!t;?Bpointwise_r!t+'!sU>:forall_def!sM?Krespectful_per_oblig!t'$_1C46Stdlib9micromega5Tauto5eKindK!sE;8GFormula08C5!sJ&6ZArith6BinInt1Z2leK!te,Numbers7BinNums8positive02!sK=1Z02!t,<3pow!tJ>tI!s}+4Init5Logic3and00!t@>N02C45stdpp9bitvector;defini!vQ#s7bv_wrap!t,82eq00!tc<4of_NK!s^;!wR7;Zify!x?&6eq_if!xX-!sf-8iff_refl!sjB3inj!sIB5mkre!snC9and_m!yw#!uc<>pow_pos_nonneg!sN<:!sN#!sJB7compare!vZ29Datatypes4list01I!sFA0!{566VarMap1t02I!sD?0!sD6=RingM!s4'7!{x'!t577Env!sT#5PExpr01!sIE2K!t?L!stF7!~$F5!v}<6op!{b#!|%#!sl;B!sl&!sH6:Z!u%+=Z!sT$CheckerC!w7<4find!sqAC!sq0_sou!sX8!zt/;rew_!|8%v!~CA:bv_modulus!sOA=!~l&_small!#3@AZ_to_b!tIB;bv_unsigned!sPA@!sv&!sU-!~y7eq_ind_r!~VEapp!#42B!sK$2!ycF4I!#6b>0I!#8B>0!}~=uni!}~9!tN%4kind!{v#!sf@1!#9h?1!#:SF3!vG68!vG#Inst7Inj_Z_Z!#8q74True!uY>:!#5B$ison!#3{7!{i-;!#5}$Proof!v38!#3603Op203!sMI5!wI=bool!#<1-!sF81C4ELinuxProcessSemantics?!s<22Fs4path!zz83!|b$!s?66!{;%!#A+4>!#A+'_PropMall!~P$m!s=&!#A31!t%67f_equal!u7N2FsC!v,;3!|c$!sq95Riscv7Prelude5bvmap!tEK5State7PipeBuf!#<$;8eqb_spec!#A}<eqb!x[<7reflect00!u:I6bv_!sv$!#4f>2bv!sv=!v}69!s{%_eq!y;9notc89OSSVerify6!{v$s:boost_json:fuzz_parse3!sb#Spec7MmNodes;!#6;&_wzC13~~~!#>c?1!#5QE7!tu89False!zt$5!uqI3Sys7Syscall5w_is0!tKF3!}OB2!~^I1!#4j75!u:$!x'#!xN?5!wv$!#6DF1!zT=sub!xC]5mminv!x=%!#4w<prod!zGM!}#%9m_vm_lazy!s^QA!s^$materializedI!sfP5Model!t|S?vm_forget_rangeK!tBW1!s\Q7Vm!s-$!#8QL!s^%=maps_subtract!sbQBpage_outside!ua%!#=6'5Lists4!s+#6filter!vbRwith!x'#backing!w~Q7Fd!v+%0I!vdY!s^SIo!s^YFs!s^X9!s7#!s`X8Li!uYY9Time!s`X6VmMaps00C6!s]I3Sys2Mm4Mmap@!|W&vm!yw%s!#QCA!#W_=add!#52\B!~22_id!#:V&!#5??1!#@1;8!t~#!#B,$!vlO;!|#&!}n#K!#CD8nd!#TB=!#Pc&!#5&Q8m_halted!s]T!ty%!s]Q6!~W#rk!yGW:brk_un!tB$!seV>!se#model_nex!#@p]A!#;S#_!wt-!yF%!sx]C!{q3!zB+!u_W=!th$!ud#!u^#!#;#T!#7>%_us!y&S=vm_live_bytesC!v-T5VmKitG!tR2_le!s|$!v0&!~d<div!sC=mul!sC<6!#W@#o!#^l<di!#Wd#!sG<=mod!#`%#b!#Y'#!sM@neg!sM25!#RK$PreO!s/#1Z;!t>#0_r_!x,#!sL=!st#!sL&!#EZC5Psatz!#F'E!sO&7!sOK!#]z<3nat!#hZA3!#_N=3Pol!#J<7!tU84!sOK6K!#UXL2!sRN3!#LT?!u_?!#b/%!sIF4!sIE5!#C,'!z;&4Zdiv:Z!z}#_mul!#5M]4pgup!#;`A!xb$1!vUN!#Kw=ltb!#<P;4andb!#50Q!#FQ#r!}0#_up_Z!#KmQalloc_top!u#>e!taR;vm_reserv!#6gR7!#Lj#!#<jR;region_free!#9OWbrk_budget_ok!z$+4Bool!s'$<!w]#_f!#TF#r!#n_<ltb_ir!#pl#!tTV;!tT#grow!tR$!x3P!xq$siz!utX7min!#@I#!{c<orbC7!|mN7Rel!|p#;!#Z-%!v0$!#?1a@!v<-_sam!#;|&!ws5:orb_true_r!t=]!#Br#result!#@?\8!sk$_ok!tV]2!#\[&!y$Q<vm_start!xG%!#Y{>D!#m-,_in!#Rs%!#>q;!x>#neq!uH]?!y'&!#nJ'!#A4@6!|c#ge!#f[;sym!|;Rerrno_re!#DpQ>!#6$'_roo!tCR6ENOMEM!t@Rstack_max!~:%!scP:two_pow_64!}'^!vJ+_!u7&!zJ&!#:]:negb!$$~9x00!}c68!}c#pro!$%\9or!s\8=!s\#!#75$iff!yRAlt!#g38iffK!tx;!#Ra<9!#8X#!u##!#vB;tran!#:_K3Run=!#3r$fusal_b!tc8!#rj$!#^gQ8in_sysno!s]Mpecs<s!#gp$!#l|$!#5MZ!sc$7!z7Pcfg8the_scfg!z#3!$4B5!$3s+!sM?Ir!$6+&_!s0,proxy!s\?F!sR0per!sY;!#sM1@and!#sM/!v^W9!v^#zeros!tq??eq!tj1!#=8V@!xZ/_214!#j%&!yGJMonad7outcome00!#>dYrk_!si&!xe;!$;J2?Equivalence_PER!|}ODspurious!}&+!z-#!tAD8symmetr!yN@N!~[$_sym_co_inv_impl!x|+!#`[]!#3&-!#?~/!#H-Pe!$-S#t!vNOCinjected_family_off!xWX6Ok_inj!u-Q!tP#9!#5s'!#3XT=!sb+!#AA#!tJ%!slTC!uq,!#\o#tru!zj+!#B;>!#z0$_dec!#:~16!v/#if7sum!$%]$!y1]=!#F%+_o!uX&K!stO3Lib5!#Ri$node09!uP&!sjY5nstep!si`:pure_inpu!{K&K!#4>X!#;vQ6in_arg!~>@R!#8f+artial_app!~>+!#uWP=!#}I%Effect!#?[-!tG5M!#3_$co_!$-O#!#3^1!w-UITree4resp!#6qJ>iff_T!tT#!#}%#I!ua_!#qEQ5even!$,1#!tsC=!ts#!wj+!#u0QMemCopy!$61=!#[M#!tUF?!tU#e!#:A+!u/JS!#9X$ic!u/Q<!v{&I!|?#!#3P^:pgup!#Og%!#3Md:!~b`6efferr!sj%!#L0]mmap_grant_conds!#;|V8!#lm#mi!#bC]=!tV$rw!#q_$!tS&!#DJV!sn$!#H'S!#Cv922!v,'!#c_39SatDivModC!#e;$!$MP$!s,&!v#]8!$3f#!$5Z'!u<X?!vk'!#Dd0!sqW<!sq$err!sr#!y2W;vm_noac!s;#!#ZBT!tL$bas!#U3Rvm_init_sp!#9iP!$$g&1!#L8E!$@_1!#:<>@sub!$\6&!$Ut%!#Mr=!sS1!#O''!x,WC!x,/_enomem!#:o:!uW2?or!uVLH!#M|#!#>/5!s[?B!u^/!#Nh$!~PWH!uY$no!#jo%!#y8#ed_ok!#FDT>!#G2+!s{#!|EV!sm$D!#G3,!tk$!#G4,!#Z%<eb_le!#Yh8or02!#81]!#8+$no!xo1!t9<1!wLWA!$#b#!}e&!#}Y#!u#]!#7j$off0!#:|b!#4l$anon_34!ssc!#6T$!#:>#ed_rw!|V4!$h21imp!~F@D!|l#!#E}#!{o-!#<0bna!#<0/!#3:VE!|_&!#7Z$!#9:0!v\kna!#@Gh!tt+!swe6mmsaf!#;r^K!ta$fix!uW#!v]8!|hWE!|h,replacemen!#BH]D!}`4_50!{2'!#4L%!$C1,2In!#=MQ!t$#contains!{5cfx!#D?bI!w[-destroy!we#ext!stWC!v[,!ss+!#zjW!si$!#mT#s!$_h<!$N^+0!#5Zg50!}|qfx!}|r!swe?!x],na!sv+!#Nf_;!z;];m!$?]#!#KVk15!#4M]D!t[&exact!#gw2!#H+O!#4:$move!#c+N<!#dV'arm!#B4TAnot_!#hi'non!u2X7!u2#has!|^_!ve%!#4F-!tQP9TASK_SIZE!#5t]!sj+_va!tT&I!wRN;I!wR&Arm!#nUQ!wS$E!x:/!wS$!z[,!|{`<!|{X8MprotectBm!s/&!$3u,!sqZ=!sq+!#VLk6!}t^G!t]+expose!#??_!vN6!#7z&!$48X@!tl,!#V%/!u`b!#Qn6!zjTB!#O<,!t$&!vSaC!vS1!#?3$!teTH!#P4-!sw'!#P8+!~z]>!tm1!suc<!su+gc3!ssc=!tj/3!#6<P!#u@#ia!#Al%!s\O=ret_in!s`V!t>#!wn%!s\O?!xI&may_fail!#7@OS!#;%%Cfg!$Z0L>!$r[#!sE+>ms_svc_pendingK!tNN6config01!u'O9sstep_c!u%O!s^%ys!#tv$!$J8;!$]3&!#tZQ4m_fs!#umY2I!w<[achine!#yc%!v%Q?mi_account_!vk#K!tRi1!xjO7!x4$to01!#v/Znre!#z1Q!u6B2!snj3!yUQ8m_kill!$MuRG!#>/&e!#wn#_!#LE$e!#ioQJ!$tL,!#9Y%!so'!$s>Q!#xf$3!s\X4!#IROapply!um&!s_O@advance_past_svc!#3}N!#4Z&0I!{KW0!|%X!~{[=!zO'st!$p?#!#xEY7at_nod!#yvf1!#<m%!sjZareg!shZ8PropExec7seg_rom!#>GP!vx26ms_me!#n%,!#982length!ttT3Mem8!$h_#_at!w6f2!w6`;iovec!$j?%!vM&!$&d:snd!sC=fstI!#`v57F!%Q9#2!%Ld=6of_na!%NM3Peano2le!$Jh,!$~%-concat!xJ^rom!w>`!#E=&!uM;5ldiff!t1`4!xIZ!yy#5wr!yvi!#T,f6!sjf8!#>?&!%91B1I!t5_!#i&&!%7&M4Uapi9O_CLOEXEC!saT;O_LARGEFILE!vA`7!#AZP!$4561!#3NY8in_a5_si!#4<_!sl$4!slh3!slh2!slh1!slc:!xM#!$B8-!$:8D;!$Ri&ity!u2_0!u2+!#rz]!%'Y&!%$3n@!%#=/_eq!ttd!#tp4!#}tdE!%&{$!%1J1!s|cH!vo+!t#8!#\pZ?!#^a-no!#iD]Amm!zm%!#c&$iff!zv;!$4n2not!$2>/!x>^!$V/3!tU+!s{];mm_ra!%c?#t!src=!$N1#!{%$!v?,!stT8AllocTopH!$i`+!%2y0!t$dE!t$,!}wnA!uu%!$#i$w!wcg!sx/na!sxgD!sx-!#~'$!s{f@!s{&!#rO$!swfB!sw&!}t'!ydY3Lib?P!$+8&Search>!$+H#_in!#tF/!$|8=_l!sT#cl!tHdI!tH1_admissible!uQZ6M!#@}#C!%dC&!%dF-!vKiG!u%2complet!#k@em!$L{'dec!wKB8le!%Zp$!$Rm;8Boo!#oy#!#V,[5nexi!#5Vd!#f]$svc_!%T<'!#7@`!#9c:!$?1,5proj1!t5]:!#=g$!%U8#!t4&!#H<NR!#_k<_no!%V7UI!#b1&_of_!#>U'none!uZ]?!#[T%!#lW&!xWd!#6D&!#;},!wc=2!#_#N!#m9,4!yRaprogres!#:u%!#NFT!#hx#!#Hw$!%sr#!#^G&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z37Corelib4Init5Logici23andi22eq46Stdlib6ZArith6BinInt1Zk12lek12ltk13pow35stdpp9bitvectorbdefinitionsm97Z_to_bvm9bbv_unsigned37Corelib4Init9Datatypespe4bool4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Syscallrd5w_is0k13eqbm92bv3h5LinuxProcessSemantics5Riscv7Preludehg46bv_eqb3h5LinuxProcessSemanticsfLinuxProcessSem5Statehj46ENOMEMhj49errno_retk13subhj45Modelpe4listpe3nilpe4prodhj49m_vm_lazyhj4h1m_vm_materialized79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes~~~~~~hrf5mminvhj4fvm_forget_range5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapihah0forget_vm_rangeshj46VmMapshj4bwith_vmmapshj48m_haltedpe6optionhj48m_vmmapsihaebrk_model_nextihadwith_brk_nexthj4fvm_backing_usedhj4dvm_live_byteshj4fpage_round_up_Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~iv74nodehrf2wzi25Falsehrf4pguppe4truehj4cmap_containshj47vm_mapsk13addk16moduloi22orhj49TASK_SIZEhj49alloc_tophj47map_hashj4bregion_freehj4bvm_noaccesshj4bvm_reservedk13ltbpe3orbhj46vm_brkihabbrk_grow_okiha7min_brkiha8brk_r_okhrfabrk_resulthj4cvm_start_brkpe5false3h5LinuxProcessSemanticsfLinuxProcessSem3Runkjbdbrk_refusal_bi22exi23iffi23nothj45event79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~kp24resppe3nathj47MemCopyhj49mkEffectUihaabrk_unmapsiha9brk_zerosiv74NBrkiv75nstepihah2mmap_off_aligned_bihabmmap_anon_bihaemmap_modeled_bihafmmap_noaccess_bihah5mmap_fixed_noaccess_bihah1with_mmap_backingpe3apphj49page_sizepe4conspe4pairhj4cmkVmMapsFullhj4avm_init_sphj48vm_limithj4cvm_mmap_base89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes6Shapes~~~~~~lv6h0mmap_grant_condsiv75NMmapiv76efferrlv6dmmap_rw_modellv6dmmap_na_modelhj4dmaps_subtractlv6dmmap_fx_modelhrf6mmsafehj4amap_removeiv77NMunmaplv6cmunmap_model5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm8Mprotectmtbh9mprotect_grows_conflict_bmtbh2mprotect_modeled_bmtbh2mprotect_budget_okiv79NMprotectlv6emprotect_modelkjbh4spurious_refusal_cfg3h5LinuxProcessSemanticsfLinuxProcessSem5Specsnp7csyscall_spechj4dSyscallEffecthj4cSyscallInputhj46in_arghj48in_sysno3h5LinuxProcessSemanticsfLinuxProcessSem5Monadogc7outcomekjbbSpuriousCfgkjb9sys_inputkjb7step_tope4Someogc2Okkjb5mkCfgpe4Nonekjb5SNext69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~op28the_scfgkjb6SErrorhj44m_fshj4hamaterialize_model_accesseshj4h7syscall_effect_accessesogc9Unmodeled3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticspifdmachine_statepifems_svc_pendingkjb9sstep_cfghj46ExitEvhj46KillEvhj48m_killedkp24nretiv77at_nodeiv7anode_inputhrfh0mmap_grant_condskp2anode_soundiv75nexit3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeqg37Segment" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unsigned_wz : ltac2:(zQ "90!h9!hf!j6!jc!l9!le!m3!o6!p0>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##6%h01xh12Hah26__sat1h34__x1h41zh52Hzh67__arithh74__ffh8!sP%0h98__varmaph:5__with;1mh<1nh=1yp;2p;1p;3p;4p;<p;6p;7p;8p;Bp-1R0p10000p4p710p9P!s6%S!s611?R1!s8,P!s2$2!s3/31!sS-]!sE-p1002L!st133!s6'g003kR!tK%1g004J!t6%3101p8g004nj23Tg005Jj12!s/$oj17Tg006MR2j25!s1$jR3j21Tg007Fj24!s/$aj1JTg008?j2C!s/$ej36Tg009?R4j1;!s1$]j20Tg00:7j3=!s/$]j1<Tg00;;j4_!s/$^l<MTg00<Cj6L!s/$lj2KTg00=Tj3ITg00>8j2H!s/$Yj1FTg00?9j1B!s/$Yj2DTg00@7j1E!s/$Uj1ATg00A@j28!s/$cj2GTg00BFj49Tg00C1j3@!s/$Tj7?Tg00D8j1>TP1j8N!s5$Zj2OTg00E<j2P!s/$hj3QTg00FGj4RTg00G9j4S!s/$dj1TTg00HMj3^Tg00I9j2]!s/$_j2\Tg00JIj2WTg00K8j6X!s/$Vl<YTg00L;lBZ!s/$aj7[Tg00MER1g00McR5P5P5P4P4f5R4f4R6f3R7f2R8f1R9f0R:M<Yp=V!sL$!s$'2P:P9P8P2P7P6P4f6f7f8f9MBZp=UP9P0g00NAR7P7g00NaR2P:g00OAF[p=!s0$aR;/3:g00P?R<#2R=#7R>%2=#2!s$%!s7$?'5R@,1:'4RAP5%J=R=/C9A65:8X4513;9RB%;=RC,5>RD,19RE'4119@RF,4BRGPBPEPBPFp-0/0B9=BB!u3$3P:X05RFP3119:#<X=5X05P9P91059PDP@PF!s$$5P5g00Pd159:C_,05X;5X<5P>P>105>PCP?PFPF%;:,05X01P=P?105?EVM:UM<MEL1K>?11;>R113;?11;@[RF[13;>RCg00QHRDAI>?9UW113;@\D^1CP9g00Qd1H;>'0P1eO1PFg00RJRF#F%BF1D59%E5%A5RFP0P7P7P2P!s0,5185;g00S61G5<R<C9,:FP5P<g00S]185>=@5=!s<$F?R>%>7P>GN1OF2P:P8g00TDRFg00TdR2'01P:8=6F2dAQ5;9CRb7b9b:X35PG\A^35P:P4P6O2b6b2b8b2CS%T=,19,4Be9^=91]=9,\=1W=9EXW5X45o"). Qed.

Lemma w_is0_wz : ltac2:(zQ "b0!r6!j6!jc!h9!hf!v1!v9!l9!le!m3!o6>1z$4>0@2$1@2$7Z^1@2$8^1@2$9+2+k0@3$2$0@1$5@2$a@1$3#k0^2@2$6^2Z").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##?ep'0h01Eh16__sat1h21bi001bh34__x1h41ah51zh62Hzh77__arithh84__ffh9!s]%0h:8__varmaph;5__with<1Hh=2Hah>4__p1h?4__p2h@2NEhA1ei011ehB1ri021ri031np;1p;2p;3p;7p;6p;4p;8p100UDp4p70R0p100V4p4p710R1p8P!s8$00!s8&2p8P0g00VMR3!s9&4!sK'Vi!s8&5!sK&WhR6!s9&7!sK'1]!s8&8p8P0P!sF$210R9!sG'2L!sG&:!sl&K8R!tL';p!t{$XE!t{%<P1p8P<P2!s+$4!s+$5!s+$7!s+$8!s+$9!s+$:!s+$;p8P<p100Y!u4&!sw%YP!tU'!sm'7!sa-!tD&Z<!tD^g005Jj13Tg005oj1ATg006Mj2I!s/$jj2:Tg007FR;j2<Tg00[2j2X!s/$Tj2@Tg00\1R<j2O!sN$aj1HTg00I9j21!sC$Tj32Tg008ej30Tg004nj2CTg00]Aj1[!s/$dj3YTg009]j28TP0j7WTg00^Yj1V!st$_j1Uj2>TP6j6TTg00<lj2STg00=Tj3RTg00>8j2Q!s/$Yj1PTg00?9j1N!s/$Yj2LTg00@7j1J!s/$Uj1KTg00A@j2?!s/$cj2MTg00BFj46Tg00C1j3GTg00D8j1F!s/$Zj2fTg00E<j2e!s/$hj3dTg00FGj4cTg00_2j2ETP3j6DTg00`>j1]!s/$\j6\Tg00a@j2Z!s/$_j1^Tg00Laj7_!t@$Tj7`!vA$Jj8aTg00bYj6bTg00OaR3f0R6'Cp=5g00McR0?063p=7g00TDR:g00TdR9706p=4f1R8g003kR7g00NAR5P5g00NaR4P6g00OAF_p=9f2R2P7P5P5P4P8P6F`p==f3R1!s;+2P8P6Gap=;P8!s;+6Ebp=B%56g00P?R=#3R>#AR?%3>#3!s$%!s7$@'IRA,:6'<RB1X83%78RC1@83RD'O1@23P:P<%71%H>R>f5R<,1>11>3RE32RF=0:8P8f4RG#7RHP0P311>8RI=2>E#4^6BX501C331:3ARJ'<RK%[>RLP;A2>86#4A0L28RM[RNA0L86A2>28#4RO[RPA2>12#4\MAY>86RMP6n20010!s#$12!s-%0X2LW4PP^2L^4LP6PEPE18LEO3b<W6P<P6PGFWWAP6O1%VHPFP:18:6f6,1>=2>E=0:6P:f8!s5-g00c=RF90:8]0P8f7!sB&RH#4A0:9FP;PNPPA0L12\OPMP8!tf:X4LPN!tg'f9,1>RNPEP8O3A0LNEPLP0%U>f:,1>RLPEP6ET1>>L1>>ERE500P0f;RL,1>,>>A006EX50P6PL1S?@RN1:3?RM%5@PJ[RJ[RO%5?RPg00QHR;AR?@8UW=R@%5A\;^=PRPP8g00Qd1Q3?'8PMeO1RMPJg00RJR;#PRQ%N;R;1L08RR%J0RS%K0RTP01?03RUg00S6RV1M0=R=C6,9TRWP0P=g00S]RX1?0?=G0>R>!sB$5=TR?%F5RYP?C;1fT4R?P6P218:91e62#4dAd038CcR9b8b:b;X30%581:8A'<\B^30P6f?f>O2b7b1b9b1,ELEDA00LEP0PEf==006!v/%3PNPOP@PPPMPJPQP;%]0PSP0PUPVPU!t^$!s3$XP!tk+P?P!tF&PKP6!t1,3EDf<R3#7!sy/p-0R!s~$PRPSPT!ul&c]!t&&RUPYPTPT!}0+UE\PYPT1BT19=TWPY1BTGC;C;C;!tF,X30X>JW?%76g00dDR9\C%52/<1P<[[[^30^>J^?JP6P9fAR9/:AP9PGP3f@O!u#+b0!s$&<'ZW0A0:HF18:FW0n01!zO%20100P6O1b0b2W@P6O1n10210010200021110111103b2bB%^I=0:DeW6X50o"). Qed.

Lemma bv_eqb_unsigned : ltac2:(zQ "70!h9!vf!p0!r6!jc!hia!v9>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$4$3@3$5@1$0#k0^2^1@2$6@2$2@1$0#k0^2@2$2@1$0#k0^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##0tp'0h01Eh11ah21bi001bh31Hh42NEh52b0h62b1h72b2h81ni011nh91ri021ri031ep;1p;2p;3p;7g005Jj15Tg007aj1@Tg00]Aj14Tg00I_j21Tg00[2j2?!s/$Tj29Tg00\1R0j2<!s1$Tj33Tg008ej30!sg$dj3;Tg00daj3:Tg00^Yj18Tg009]j27Tg00K8j7>Tg00a@j2=Tg00McR1f1R2f0R330p=2g00TDR4g00TdR5703p=6g00P?#5!s$-@R6#4R71162R81163R9'?12891989'<f2R:,16R;/98P4P0f3R0,16R8/2;f5R;f4R<536R==042P2116</28R8g007FR>A3623#6A07:2R?[R@A0723A36:2#6RA[RBA360:#6\?A;623R?P3n20010!s#$12!s-%0X27X17PB^27^17P3f6RCP;g00MERD%43RE%42RFP>%4:?023110:1102'2RG[11:211:3'2%40?0:2[RH%4<?00:\GA::23!tC9W7W6W8PH^7F^6E^8DP3P6f7RDPCP:O4b3O3b3W0P3O1%88P=P41743A36C;=043P4f8R==36D=043g00c=R89042]0P2A36DCRD#6A0458P>P@PBA070:\AP?P2!uz>@!uz+9R@P=P2O3A07@=P7P@f:R=,16R2,29#8g00dD]4X17116@R@/2@#8P31712O1W4P=P3P;F>b0b3'=W0A04D81748W0n01!tL%2010!uW$b0b5W4P3O1n10210010200021110311101b5b9X27W1o"). Qed.

Lemma errno_ret_ENOMEM : ltac2:(zQ "80!jc!h9!hf!hm2!hmc!m3!hn9!p0@3$0$2@2$7@1$1#k0@1$4$3@2$6@2$5+2+k0+c").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##$:p;1p;2g005Jj10Tg005oj11Tg006Mj23Tg00eEj12!s/$jj25Tg009]j24Tg00Mcg00P?R0#0R1#1%01#0!s$&1'3%2!s1'5'4o"). Qed.

Definition mminv : ltac2:(zQ "10!hnf>2mo$0P") := ltac2:(zQ "a1!h9!vf!ho8!hof!hp5!jc!j6!hnf!hpc!hq9&@2$4@1$1@1$0#k0@1$1@1$0#k0\2mo$7@2$6@3$5@1$2~0@1$8^1@1$3~0@3$5@1$2@1$1@1$0#k0@1$9^1@1$3@1$1@1$0#k0").

Lemma mminv_lazy : ltac2:(zQ "91!h9!vf!hp5!ho8!hof!jc!hnf!hpc!hve&@2$2@1$1@1$0#k0@1$1@1$0#k0>2mo$6>0@1$8^1@3$5@1$3~0@1$7^2@1$4~0").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##%xh01Hh12H0h22_Hh32mop;1p;2p;3g00fGj19Tg005Jj10Tg007aj17Tg00]Aj16Tg00gMj28Tg00?9j15!s8$mj12Tg00>Yj13Tg008ej31Tg00hej14Tg00ief0R0#9g007Fg00P?#0!s$-7#6R1/81R2#5R3f1R4#2%32R231%51R5%44%31R131f2#2=132P0f3!s0%f4#4=151P4W2W0P4P0O2n20010!s#$12!s-%0W1W3o"). Qed.

Lemma vm_forget_range_id : ltac2:(zQ "50!hf!hnf!jc!ig7!hve>2lo$0>2hi$0>1m$1>0@1$4^1@3$2$1@3$3^4^3^2^2").
Proof.
  intros lo hi [fd [maps lazy mat] io fs proc lim tm] [Hl Hm]. cbn in Hl, Hm. subst.
  unfold vm_forget_range. cbn. reflexivity.
Qed.

Lemma forget_vm_ranges_id : ltac2:(zQ "80!h9!hnf!vf!ho8!hp5!jc!ike!hve>2us@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0>1m$1>0@1$7^1@3$5$1@2$6^3^2^2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) [] "p'0h01mh12ush22Hmh32IHh41ah52a0h61lh71ni001bi011pp;1p;2p;3p;4p;6p;5g005Jj10Tg007aj1@Tg00]Aj17Tg00gMR0j25Tg00?9j1?Tg00fGj1:Tg017aj21Tg008ej32Tg009]j26Tg018fj33Tg00I_j24Tg019Fj28Tg00j[j39Tg019cj4>Tg00K8j6=Tg01;6j4;Tg01;Vj5<Tg00P?#0#0#0#0#0#0#@R1#7R2/52R3#?R4P3g00ieR5f0R6#:R7f2R8f1R9'1=259[]0R:X141659X27X05P0P2P2f4R0f3R;533/19=259\7^05\:^64P6P5P91106=258X05P8P9P6O2f5R8,41R<1410,8<R1;99P<P1P9P6C>E=P2P2P8P0C;=33;/19=259eX27X05X3:X14X72X42P9P6O2n2001101000121100100X53P6D<W1o"). Qed.

Lemma mminv_with_vmmaps : ltac2:(zQ "40!hve!hnf!im3!imd>1h$2>1m$1>0@1$0^1@1$0@2$3^3^2").
Proof. intros h [fd [maps lazy mat] io fs proc lim tm] [Hl Hm]. cbn in *. subst. split; reflexivity. Qed.

Lemma m_halted_with_vmmaps : ltac2:(zQ "80!inc!io8!jc!h9!hnf!im3!imd!vf>2hh$5>1m$4@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##$@h02hhh11mp;1p;2g005Jj10Tg007aj15Tg00]Aj12Tg01=Mj11!s/$oj14Tg009]j23Tg016jg00ieg00P?#0!s$-5#2#1f0#4'3W1W0o"). Qed.

Lemma with_brk_next_eq : ltac2:(zQ "90!h9!hnf!vf!jc!ip1!imd!ipd!iqf!hve>2mo$1>3req@1$2@1$0#k0>1r@1$2@1$0#k0>0@1$8^3@3$3$1@3$7^4^3^2@2$5@3$6@1$4^4^3^2^4").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) [] "h02MIh12moh21rh33reqp;1p;2p;3g005Jj10Tg007aj1<Tg00]Aj12Tg00fGj11Tg01>fj1;Tg01?]j1:Tg01@Rj23Tg01AQj34Tg01<8j25Tg01BTj36Tg01Cfj37Tg01E:j38Tg008ej39Tg00ieR0g00P?#0#0#0#0#0#0#<#2R1f2R2#1f1R3f3R4#;R5#:'3A4523R5/54R6f0965437A8423=906eW0X21W3W1o"). Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live' : ltac2:(zQ "60!hnf!ip1!is0!it3!hve!l9>2mo$0>0@1$4^1@2$5@1$2^2@1$3@1$1^2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) [] "h01Hh12Hlh22Hmh32mop;1p;2p;3g00fGj1>Tg005Jj10Tg007aj17Tg00]Aj16Tg00gMj2=Tg00?9j15Tg00gmj13Tg00>Yj12Tg008ej31Tg00hej14Tg01F<j18Tg01>fj19Tg01G:j1:Tg004nj2<Tg01H6j3;Tg00ief0R0#>g007Fg00P?#0#0#0#0#0#0#7#6R1/=1R2#5R3f1R4#3%22R231%51R5%44%21R131f2R6#8%96#:'<P0f3#3=132f4#4=151f5?;40W2W1P4P0O2n2001000000120000000W0W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wz : ltac2:(zQ "30!h9!hf!vf>1z$1@1$2@1$0#k0") := ltac2:(zQ "30!h9!hf!o6\1z$1@2$2@1$0#k0^1").
Definition pgup : ltac2:(zQ "10!hf>3len$0$0") := ltac2:(zQ "20!hf!iu4\3len$0@1$1^1").

(* [comment removed for export] *)
Definition mmsafe (n : node) (mo : Model) : Prop :=
  let h := m_vmmaps mo in
  match n with
  | NBrk req => 0 <= req < 2^64
  | NMmap addr len prot flags =>
      (* the length bound is main's [2^63] ([LEN_MAX]), which the [KLBM] chain, carrying no
         budget, can supply; nothing below needs more than [pgup len <= 2^63] *)
      (addr = 0 /\ flags = 34 /\ (prot = 3 \/ prot = 0) /\ 0 < len < 2^63)
      \/ (flags = 50 /\ prot = 0 /\ 0 < len < 2^63 /\ addr mod 4096 = 0 /\ 0 < addr
          /\ addr + pgup len <= alloc_top h
          /\ region_free (vm_reserved h) (wz addr) (wz (pgup len)) = true
          /\ map_contains (vm_maps h) (wz addr) (wz (pgup len)) = true)
  | NMunmap addr len =>
      addr mod 4096 = 0 /\ 0 <= addr /\ 0 < len /\ addr + pgup len <= TASK_SIZE
      /\ map_has (vm_maps h) (wz addr) (wz (pgup len)) = true
  | NMprotect addr len prot =>
      prot = 3 /\ addr mod 4096 = 0 /\ 0 <= addr /\ 0 < len /\ addr + pgup len < 2^64
      /\ map_contains (vm_noaccess h) (wz addr) (wz (pgup len)) = true
      /\ map_contains (vm_maps h) (wz addr) (wz (pgup len)) = true
      (* 08b1429's vDSO/vvar gate: a range meeting the pair is unmodeled, so the
         node only speaks about ranges that miss it (Sys/Mm/Mprotect.v:279) *)
      /\ region_free (vdso_reserved (m_kernel mo) (vdso_top h))
                     (wz addr) (wz (pgup len)) = true
  | _ => False
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pgup_range : forall len, 0 < len < 2^63 -> len <= pgup len <= 2^63 /\ pgup len mod 4096 = 0.
Proof.
  intros len H. unfold pgup, page_round_up_Z, page_size.
  split; [| apply Z_mod_mult]. Z.div_mod_to_equations. lia.
Qed.

Lemma TASK_SIZE_val : ltac2:(zQ "40!jc!hf!jo7!m3@3$0$1$2@2$3+2+if").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) [] "p;1p;2g005Jj14Tg005oj11Tg00eEj10Tg006Mj22Tg009]j23Tg00Mcg00P?#4R0#1%00#0#0#0#1'2'3o"). Qed.

(* [comment removed for export] *)
Definition brk_result : ltac2:(zQ "30!h9!vf!hnf>1m$2>3req@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "d0!h9!r6!vf!p0!jt9!jtf!hnf!im3!ip1!ju5!juf!jve!v1\1m$6\3req@1$2@1$0#k0=1h$7@1$8^2=1b@1$2@1$0#k0@1$9^1M1\0$1@1$2@1$0#k0@2$5@1$c^3@2$4@2$3@1$0#k0^3@2$3@1$0#k0@1$b^2^1M1\0$1@1$2@1$0#k0@2$4@2$3@1$0#k0^3@2$3@1$0#k0^1^3M1\0$1@1$2@1$0#k0@3$a^4^3^3^3^1").

Lemma brk_grow_ok_same : ltac2:(zQ "90!r6!jl1!jc!h9!hnf!ip1!ju5!juf!vf>1m$4>3req@1$8@1$3#k0@3$2$0@3$7^2^1@1$6@1$5^2$1").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##-@h01bh11mh23reqp;1p;2p;3p;6g005Jj11Tg007aj1JTg00]Aj1GTg01>fj18Tg01?]j1BTg00I_j2;Tg01X[j22Tg01Y8j20!s/$Vj1@Tg01ZTj17Tg01[Lj25Tg00gMj2C!s8$ij19Tg01\cj1ATg00Y3j3?!t$$9j24Tg019Fj2<Tg00ejj2=Tg01]Yj3>Tg01^Sj2:Tg009]j2ITg01_Uj1FTg00K8j66Tg01`5j1E!s/$Yj3DTg008ej3HTg00TDR0f0R1g00TdR23Hp=3g00ieg00P?#1!s$-JR3#GR4P0g00c=R5P0!s1$OaR6f2R7#8R8#BR9,;3R:'2/01P0P0%@:R:/2:%78,5:1C44R4%98%A83?143:g01aYR8,<:/=:,433>'0P2n010!s#$200001:79'0R9!s>3#3X00P0P!tX$P1P!sG91I02f1R9#8R7#BR:,;3R;,26R6/05%F6E612;;R5%E;E6P0P0106!sx$%@;R;/2;%77,5;%97%A75?4143;1<;8/=;!t~<9:!s<5#3eAD91:#3eW2W1o"). Qed.

Lemma brk_result_ok : ltac2:(zQ "80!r6!jl1!jc!h9!hnf!kg9!kh5!vf>1m$4>3req@1$7@1$3#k0@3$2$0@3$5^2^1@2$6^2^1$1").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##5ap'0h01bi001bh12E1h22E2h31Gh41mh53reqp;1p;2p;3p;6g005Jj1;Tg007aj1ITg00]Aj1DTg00a_j1<Tg00I_j28Tg01>fj14Tg01bQj1=Tg01cMj22Tg009]j2ATg01?]j17Tg01`Yj33Tg00\Tj30Tg01Y8j26!s\$jj2>Tg01e1j2HTg01fBj1G!s/$`j2FTg01gkj3CTg01X[j2ETg008ej3?Tg00K8j6BTf2R0f1R1f0R2'8'Ep=5g00TDR3??12p=9g00TdR49?32p=1g00c=!s2%@P3P4f3R5P0P1P2EBp=:g00ieg00P?#;!s$-IR6#DR7%<21862R8%41R9#=756'2R:P31A32R;%<11861%40!sA&/92P3%<51865R<f4R=#4R>!sC/P3P1P3P7P1f5R?#4#7R@P3P7186=?56@RAP=P3P7A3?==P=P@n010!s#$20000!s4?RB=06@!su$3PAA06B=/2@R@A3?=B,6!sp11!s41#1]1P1%<01860%45!ua'5#1%7>R>,>6W1%@5A5<6>P3P;19A2P3f6RA,86f7R>#4#7756!u[2P>P3P7f8R<?3>>R5P>%4<#7R!u?A@=06>A06@0'2RBA3<>@,6B!sK1#1]2P1186?%4A!tI$R?#1A06>0,22#1X031A34R0A06AA1>6AC:W2%@?A3>AA!u9%52P3f:R5f9R;;3;R>!u4%7P1P5f;RA!we$?!w+65A06B?'2A3A5B'6#1]3P1A3;<<R<!tS$5?RB,2!sF$5'6!t\%24B/6!th%P0P>P2C:A06;;1>6;C:W3%@<A06?5/!s^%?R?!s`'62?!s/&4!sf'%45#7R0935;1H5;!sq$0;R;/24%G!s5&01>60C:W3n011!u8,P2O1b3b0W2!s>&1!xr%!s>$2b0W1!s>61b0!xF$:!v>$:%79R9!zf$5869R8P!vV$A3122P2P9!zsN7=06!sr%3P8A0672/29R9A3127,6!sp/1!zs5e1F129C12#1eW5W4o"). Qed.

Lemma brk_result_query : ltac2:(zQ "80!jc!h9!hnf!ip1!ju5!kh5!jjb!vf>1m$2@3$0@1$7@1$1#k0@2$5^1@1$6Z@1$4@1$3^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##+Gh01Hh11bh21mp;1p;2p;3p;6g01hhj1?Tg00a_j1>Tg009]j28Tg008ej33Tg005Jj10Tg007aj1;Tg00]Aj1:Tg00I_j21Tg01>fj14Tg01bQj17Tg01X[j22Tg01cMj26Tg01?]j15Tg01`Yj39Tg00VMj6=Tg01f`j2<Tg00ieg00TDR0g00Oa#?R1#>R2'8g00TdR3=302P0P3g00P?#0!s$-;R3#:R4P0P4f0R51131R6f2R7#4R8#7,13'2'6%58R8P0P41138,26P1P0P4A9711P1P8n010!s#$20000!s4?;38X10f1#4#5,84P2P5E=b0P0P4%45!t@&,26,62!tB;5!tBS=348e1<51!s/$W2o"). Qed.

(* [comment removed for export] *)
Lemma brk_result_grow : ltac2:(zQ "d0!h9!ip1!p0!ju5!vf!r6!jc!hnf!ki3!juf!kh5!l9!le>1m$7>3req@1$4@1$0#k0>0@2$b@2$2@1$0#k0@1$8@1$1^2@2$2@1$0#k0@1$3@1$1^2>0@2$c@2$2@1$0#k0@1$3@1$1^3@2$2@1$0#k0^2@3$6@1$4@1$0#k0@2$a^4^3M5\0$5@1$4@1$0#k0@3$9^4^3^3^3@1$3@1$1^4").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##BHh02H0h14__x1h24__x2h37__arithh44__ffh58__varmaph65__with71bh81xh91yh:2Hah;4__p1h<6__sat1h=4__x3h>1Hh?3Hlth@3HsbhA!sF%0hB1mhC3reqhD1zp;1p;2p;3p;4p;6p;7p;8g005Jj1:Tg007aj1wTg00]Aj1bTg01>fj17Tg01ikj1<Tg00I_j20Tg01?]j16Tg004nj28Tg006jj24Tg01jfj2OTg00Gdj1W!t$$FR0j2@Tg00a_j1K!sp$9j2uTg00[Tj2BTg008ej31Tg00^Yj1GTg01kYj2eTg01O\j1QTg01Maj2ITg01Qcj3TTg01RLj2_Tg00>Yj1^Tg018fj3]Tg00?9j1\Tg00`>j1[!s8$Yj2PTg01Sdj4DTg00@7j1Z!s/$Uj1YTg00A@j2NTg00eEj1X!s8$cj2CTg00bYj6VTg00D8j1UTg00BFj4L!t1$\j6v!sA$Zj2tTg009]j2JTg00E<j2p!s/$hj3oTg00FGj4nTg005oj1STg00<lj2l!vd$Mj2kTg00=Tj3j!uN$8j2iTg00C1j3hTg00_2j2gTg00K8j6RTg00\Tj3fTg01l:j2dTg01X[j22Tg01cMj2ATg01`Yj3>Tg01mJj2cTg01f`j2mTg00Laj7a!t1$Tj7`!xD$Jj8q!sS$jj4rTg00VMj6sTg00OaR1f0R2'8p=9g00TDR3g00c=R4712p=5g00McR5f1R6g00S6P2CLp=?P6g003kR7g00NAR8P8g00NaR9P2g00OAFap=3f2R:P7P8P8P9P6P2F`p=MP5!sb$S]!sp%=f3R;!sK+:P6P2Gqp=;P3P6P4P2Crp=FA1342p=HP3P4P;!sL%Esp=Eg00ieg00P?R<#:R=#:!s$'R>#wR?#bR@%76RA#<,0?%6A,0?'8%7:#6,0?10?6'41O?:10?:RA#9%W?RB,4A'@%K;RCP310?;1u?1RD,0?RE'B%52X73P01B62#5A15:6#GRF[A1562#G1B:6#5[RG1B;:#5\F1e62P2n20010!s#$12!s-%0X95X85PG^95^85P2f4RG,0?RFPEP5P1f5RH,0?RI=152#GXD5%7HRJ#6RK,O?10?KRK#914KB'@p-0RKg00RJRLg01WPRM#QRN#Q,I51I5N1I5M5T55T5g01Wo'_%^LRM3]RN%\LRLP5%[5ROP61P5:RPCD%Z5RQ%Y5RR1N51RS%X<,C5RT'?,3RPR!wu+GEV5MR%U8RUPR1C5<R<,=T,3RPU!sL-5P<g00c]PSCL,3REvC;C;1tR9R9P2P:g00TdR8,J31p2:=138dAo516CnR8b4b5b6X15X25W;%96/@:14:6R7A15:1g00dD[[[^15^25^;KP2f7RK#7RV#6RW,0?RX/4BPXf6RB,0?RYP6PGO5b3b0PE%S=RE%S>R>'l141ERZ%9>1kE>R[,41R\[R][%9ER^g00QHR_AjE>6UW:%9[\_^:^!{-$Qd1i1E'JPZeO1P]PMPLPOPQ1?SS,3R1N5E=h5?,=S,3R5MRP9P!uK&1811/@\P2b3b<bAb<,g1ERO3b0Af?;D1d;DER%5Ce'F%HCP3P@%7BRC!{/$RD,2IR1,A2%6CR!sC$10?C,2IR\PHP3P@A>BHHPHPCn!z6'!z5$R!s62!s41=1@CX73%<J,0?,2FRFP01262#5186:R0[182612!{H%J12!{H$01c!{HARCPJ!{J%RJP2PIPDPNPLP5PP!z/$;CDPQ!yT$=R=!yT,1?<!s1%1?<=,3RRTC;C;!v],!y&%X=5186;18:;[\7!xu&=5P2PXPY%<V,0?PGPHO5b3O3b0'F%HF!vL$A42PW!s0$2YXRFPB!vS%KBBPBPW!vS2W!vSBWX73PCPJP2PYPX!xq$!uT$PO!uR&=!u9$PUPT!u951426P0!{%&P210?Kf8R5#7#6R0,0?PHO3!u4%,F\%H\!u5&4P0P3P@P2PK!u1%5KKPKP!tk2R0!u1B0X731J@WPFP2CEb0P1!s-%%KG!s/%b>!z9$K:%7;R2!z<$,2A'A%62R2!z7&2,2AP:!tU%;::P:P2!tU22!tUB2e1m;:!s/$W?W@WCWBo"). Qed.

(* [comment removed for export] *)
Lemma grant_not_enomem : ltac2:(zQ "f0!h9!r6!kj3!jc!hf!hm2!im3!jp4!hmc!hia!jn3!l9!le!vf!p0>2hh$6>1a@1$d@1$0#k0>2nZ$4>0@2$cZ^1>0@2$b@2$a@2$e@1$0#k0^3^2@1$7^4@3$3$1@3$9@1$0#k0^4@1$8$5$2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) [] "h02Hah11Hh26__sat1h34__x1h44__x2h54__x3h61xh71yh82Hnh97__arithh:4__ffh;6__sat0h<8__varmaph=5__with>1ah?1bh@2hhhA2nZhB1zp;1p;2p;3p;4p;6p;7p;8g005Jj10Tg007aj1iTg00]Aj1UTg006jj22Tg00I_j21Tg019Fj2:Tg01ZTj1@Tg004nj25Tg01nFj1TTg00[Tj24Tg005oj16Tg006Mj2ITg00eEj1hTg00ejj2fTg008ej33Tg00^Yj1BTg01kYj2ZTg01o>j1YTg00<lj2XTg00=Tj3WTg00>8j2VTg009]j2DTg01O\j1?Tg01Maj2<Tg01P;j1STg01PYj2RTg01Q:j3QTg01Qcj3>Tg01RLj2NTg00>Yj1MTg018fj3LTg00?9j1KTg00?Yj2CTg01Sdj4JTg00@7j1OTg00@Uj1PTg00Acj2=Tg00A@j28Tg01UHj3FTg01TBj3HTg00C1j3gTg00BFj49Tg00D8j1eTg01Tej3`Tg00`\j6^Tg00DZj2]Tg00E<j2\Tg00Ehj3[Tg00FGj4_Tg01Iij2ETg00K8j6GTg00\Tj3aTg01l:j2bTg00Laj7cTg004Jj8dTg00TDR0f0R1g00c=33p=7f1R2g003kR3g00NAR4P4g00NaR5P1g00OAFcp=;f3R6P3P4P4P5f2R7P2P1Gdp=Ag016jg00P?R8#0R9#0#0R:#0#0#0R;#iR<#Ug00McR=g00OaR>/2111<7/:2%@6'5P011<6g020;#TR?,1<R@'4%71X?0P=%69RA%6;RB'IRC%h8RD#0#0#6RE'fRFf4RG,1<RH/41#7XB=g007F1421#7A3=72#BRI[A3=21#B1472#7[RJ1467#7\I1Z21P1n2001000000120000000X7=X6=PJ^7=^6=P1PHPFf5RH#Y%@Hg0210':g021m'21XAB12>ARJ15>B12>C[RI[15>ARKg00QHRLAWAB2UW015>C\L^0KP2g00Qd1V>A'DPJeO1PIg00RJRIg01WPRJ#?RK#?RL#?,<=1<=L1<=K%S8,R=1<=J5Q=5>=5>=5>=g01Wo'N%MI3L%KIP=1C=7P21C=6CJ%O=%P=RIP=1==DRD%6:R:,8=%0;#0#0#0#6R;,8=RJ5F==F=J5H=g00S]RJ18=A=g=<RAC9,;I%e4RKPIP=1==8R81==9R95H=g00S6PDC9,;IPKPIP=18=>PJP9C9,;IPKPIP3P4P4P5P=P8g00c]18=E9`=AC9,;IE^CACACA1]I5P1P7g00TdRI,D01\17=30IdA[=>2C_b:b<b=X3=X4=X5=1E:;/E;,:7/2C1:27/5612>6A3=6Fg00dD[[[[^3=^4=^5=P1f:#@f8f9,1<PGf6f7O6b9b2b;b211<H=3=F#Beb1O3b1P@g022fEGAa<6?1b6?EGW0W8WAW>W@o"). Qed.

Section Shapes.
Context {SC : StepCfg} {AF : AllocForced SC}.
Variable mo : ltac2:(zQ "10!hnf$0").
Let h : ltac2:(zQ "10!im3$0") := ltac2:(zQ "10!ip1@1$0?2mo").

(* [comment removed for export] *)

Lemma brk_refusal_result : ltac2:(zQ "d0!jc!h9!vf!r6!jl1!j6!km7!kg9!kj3!kn8!knd!ko3!kh5>3req@1$2@1$1#k0>1r@1$2@1$1#k0>0@3$0$3@3$7?2mo^2^1$4@2$a@2$5@3$0$3@3$6?2mo^3^2$4@2$9@1$2@1$1#k0\2r2@1$2@1$1#k0@2$5@3$0$3@3$7?2mo^4^1$4@3$0$3@3$6?2mo^4^1$8@1$b@3$0@1$2@1$1#k0^2@2$c?2mo^3").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) ["Shapes"] "#$%Tp'0h02r2h11Hh21bi001bh32Hrh43Hokh51Gh62_Hh72E1h82E3h91Fh:2E2h;3Hr2h<2G3h=2NRh>2b0h?1rh@2G2hA4OKEQhB4__x1hC4__x2hD1EhE4Hok2hF2H0hG2NEhH7__arithhI4__ffhJ4__p1hK8__varmaphL5__withM1ahN2b1hO2b2hP1ehQ1mhR1nhS3reqhT1xi011xhU1yhV3E1ahW3E1bhX2RFp%0p&0p;1p;2p;3p;6p;4p;8p;7g005Jj1YTg007ak10JTg00]Ak109Tg01>fk10ITg01?]k10FTg00a_j1BTg00I_j23j1yTg01bQk101Tg01X[j27Tg01cMj2:Tg009]j2STg00\Tj30Tg0247j1;Tg01`Yj39Tg008ej31!tJ$dj3zTg01Y8j26!sS$US00j2>!s2$oj3\Tg025KR0j2[Tg01_Uj1s!u7$FR1j24Tg00VMj6V!t{$@j2GTg01=2j4DTg00K8j6Ij8hj7i!so$ek20HTg01gkj3NTg00[Tj2aTg00^Yj1KTg01kYk20ETg006jj2TTg026Fk20DTg01O\k10CTg01Maj2oTg01P;k10B!s0$Yk20ATg01Q:k30@!s0$ck30?Tg01RLk20>Tg00>Yk10=Tg018fk30<Tg00?9k10;!s0$Yk20!vj$`>k108Tg01Sdj4mTg00@7k107!s0$Uk105Tg00Acj2eTg00BFj4`Tg00D8k103!si$\k602!s:$Zk200Tg00E<j2~!s/$hj3{Tg00FGj4|Tg01l:j2}!uh$fj2!y5$Whk60!w,$eEj1xTg00bYk606!xd$jj2XTg027?j4l!s/$Yj3kTg01mjj4wTg028<j6v!s/$Zj3qTg01f`j2uTg00Laj7tTg004Jk80GTg00TDR2f2R3f1R4f0R53Ng00TdR631p=CA1245p==f3R7?034/:5p=bA9345,67p=RA1256p=2A0345#;p=L1634/65p=E%;!s/%Z%;5,64p=f1645g00c=R8512p=UAN734=126/45p=?f6R9f5R:'6=126f4R;/>7'4A1345#K'Jp=O!t7$=126p=@A1258,44p=<16:;!sn%7!sT-j!sH$p=8P2P6P7P3P4P5EIp=M!sK&p=516;7=1261>34'4/J5p=W1>45,43p=cP2P8!s_/HA0:;7!tS$':p=Q!s0$,:7p=rP4g003kR<g00NAR=P=g00NaR>P5g00OAFtp=_P7P<P=P=P>!sz%L0Gp=d1>34,47!tK$^!uX'8p=A14;!uF/]A124!vJ%P16!u~'n!wV$!s2%F%K5,J4p=g!ui$4g029TR?P8P5EVp=pg00P?R@#YRA#Y!s$'$0JRB$09RCp,2moRD?C45&0IDRE$0FRFPC%B7S0113B7RG&01E,3BRE'7S02':P21S25RH%B;13B;RI/7E':/=5P2%B913B9RJ!s9,P2P4A0B9;RKP2P2f7RL,3BRM/7IPBP9PLPKCbRKPKPDPLP9CRn010!s#$20000!s41#2f8RK#BRI#;13BKRN/7ERO#;ALBK:3EA0BL:PCPDf9RPP5%BPRQ13BP/7ERR#;'ZRSA0BP9'fA0B59'UC?X0CPCPLP2PCP3P:P2PC13B:RT,7NPKP2PCA9DKKPKP:!th?!s41FO]4]7P4%B:17TE':RT#2A0B:7RN#2P1A@B45A1C34[RUA1C45A@B34RV[A1C73\VAzB45P4n20!s~'1!t#$000X2CXMCRVPU^2C^MCRUP5PLP:P4O3A1C!uv$9f:RW#BRX13BWRY/7ERZ!uu$[ALBWLR\'6R]A0B5Lf;R^=CD5R_%B^R`13B^Ra/7ERb!sV$cALB^KRdA0B5KRe3E'<X0C,>CRfPCP5PLEjX?CA\QR7%2Q%2R'[P0%2X%2Z%8cP5%2`%;5Rcf=RZ,3BRX/7ES03#;'UX221S28S04%;6Rgf<Rh,3BRi/7ERj#;'Ue%BhRkP5CMW7P5O1%2b%BZS05#;/UcX22%;kRk#s1UkgePj!sO,!vT-2!s-$!s'$b7%8S165dA0BKKPCACDh5RSALBhPA0B5P5E4!uT$A5CKKRkDWX22A1286RbA1288Rl,4_X0C7cCRmPk[A5CLLRk14Sl!v2&S,4bRn[P1PbPSA5CPPP5f?RS!w#$o/4!sN&P2P8P2p-0RpP5g00dDRqg00QHS06n011!y^,XP2P?P6P4EVR?PqA5CZZ/G5b1W6X9bP4P5O2!y:81mP51SCKO1,GnXGkCD168\A0BLLPCAE8de,<_X0CPkDWeP[P5CHbXPKP5EIb4b1W4W7%8TP2P217JGPBP:P9PNCbRNPNPDP9P:!}_3#2P11:45#8%83RN%84RJ'4[RG%85RT,4J1:34#8RJ[%87/4N\J20H!{J<O2XN2PG^O2^N2P5PIPOP3O3%8I/<OP1%8Q%8RP]A0BPLPfPCPP!}o$7YMPW!}j&WWPWPL!}\?EjP5%8`%8jf>Rj,3BR`/7ERM#;ALBj^Rf5EcA0BZ^R]PC%;4RR13BSRQ/7ERO'fALBShRIA0B5hRG3E,<oX0C!tV%`aRaPj!tX&jjPjP^!tX?95CZRJ!z0$%;8RN?EcfP]PC16NR?EIG!t%&!sH%!w\$:5OA0B4hRO!wk%QiRQPBP4PSPOCbRiPiPDPSP4!wm3Ri!s61/=i!sy+85POP!sF<PaA0B5jRiA0B5^S07':ROA9Dj5RJ,6O!t52O,S2PMP4CH%BjRoP3CH!t3%oMA0B5FRo!s5$3BFS08,7`1:ioRi16iJ!vF?/=ORiePieANDj5S09/=OROeX0CPO^0CPaP2PH1=Q5P2fARQ,3BRa/7`!#:#'PBPQfBR`PBPQPSEQROPOPDP`PQ!{55fDRO=ND!s`%7A0B5ORiPBP5PQCrRJPJPDPOP5!s_3'=^0CA0BOQS0:#;fCRJ=0BQRMPCfERG=CD5S0;ALBG`S0<A0B5`S0='6'<!#:$$JP2PCP7PO!yS&OOPOPQ!#9cAA]4]:P4f@RI,3BR]/7XS0>#2PBPIPQ!s+$jEQS0?#2ANDJ5S0@A0B5JRj!uG$ICrS0A!u0$!wZ$J/a]PTX22S0Bg00McR]P11a45#8A5]34R[[A1]45S0C#K1a34#8[Rk1a73#8\[20E45P5!~68U]WTPk^U]^T]P513BORkPaP11745#21T34[Ra1T451734#2R[[1T73\[20D!#32;Q]XR]R[Pa^Q]^R]Ra!t#$GR_13B`ReP;O31T_eg00RJReg01WPR_$0C,o]&0B@-0A]1o]_60@]60?]g01Wo+0>&0=eS0D40<&0;eS0EP]20:]3S0FP4&08]S0GCm&07]S0H&05]ReP]1e]@R_g00S]S0I1e]ARAC`,_e&03=RdPe!#D<']P_g00c]S0JP!sI%J02Cd200e>S0KP5P31S26RA1~53#2dg00Oa={]4C|S0LbIbKbLXB]XC]1T54A1]43Pq[[^B]^C]P5PkfGRk,3BP4O3bHb:b1O3b1A0BJIR\1}JIEI%8\PcA0BO`RcPCfFR\!z\%M16Rj!zN'OPGFOX22A0BJORn?\M3%2n%2M'[P0A@BOG%2cA0BGJS0N#2S0OPCPDPkP5%8iC?!#<>$G\C^P5A0BG\S0P#2PVPU!tr$HRi!#@F%kiPCfIRmA0B5kRr#2PDfKRsP5AAB5!so%S0Q,>CRtPCP5fJRuD]X?CRv%25Rw/4tRxA5CuuRy'JX22PDPuP5%8r!sa$,>CRr,4bRzPy[A5CmmRy14btR{!#=D$tA5CssP5PDfNR|!tC%s!s`'S0RP?PqfOR}=5C}!#<oHzP51SCuO1,G{X9yCDA0Bm\RyP:CHPiP5EIb3b1W3P5O1Q0O!v0'PG!v-'GPCP\PvA1CkuRv#KR{,Jx!#?y$66Rx/4rRrP{[A5C\mRz14xt[PCP]%yBPiPsP5J0413Bi13Bs51]P[PaP5fMRa,3BR[13BuR~PhO31T[~Q0DQ0EP]Q0GP4Q0FCmQ0HPeP]%x@,e]R@Q0JP_!zc$PdPeP]P_Q0IP@!s8,!{<';J06CdCdQ0KQ!zd1XJpQ0C1T43P;!ze'^JpP5PqfLR],3B13B}P7P4O5!zn%bDXDvP{eX6rPxPtPAPCQ0QPuP2A0BuuRtA0BukRr':A0BsiR{#8Rv,4wX221:5{/Pv!s0$65Rv/PT!s2%8R>#2PlPAQ04CDPrP9CHPt1XBuCMANDuuPLPuO1EIClCDX6z!w}$\\1XB\CM!w}3!#E>/100!#CA$b4PNPMPCQ0;Q0=,6N!#8$+OFOeQ0:P5CHbGWAW4W:Q0>#8Q0?A9DQI'nQ0@Q0APDPJP5CR!#78$BP`PJ!s+$IEQRQA9DJ`Rz;k4%2z,PQP11:nM#2AFDOJQ0<PcPCQ0MA0B\J/Z!}~-!#9F$GGPGP`!#982P5Q0PQ0N':!so$k\A0BiG!#<<$y5P21={5PRA0BsmRR!~?$aP5%;3A0B5uR{!#M_+s!t5&]]P]Pm!t53]8P4%2r!{S&]Pm!{S&]mA0B]aRyA0B]uRG;\9%2yRy%2GRG!#3o%a|A@BasA1C|}R\P5A@B|}!sp%fPRkfQRO!|I'OP5!wl,A@B|]!|m+|!sJ'|!v2$}fRRjP5PCPjP}P:CwEv!xND3b8b1A1CusPCP]PBP5PaP{Cb!vX$|4Pb!#5W&Pl!v4%!v0%}}P}P]!#C~33C^]5]3X?CPBP]!sv$]PmEQ#2A9DaaR{!#6+'}P]P;!u3$}]PCPkPbPCACDj5RJ!#Jy$!#>p'RcPOP5!t94OC^X2CA9DkkRnP2P2PDfTRM!tw+,>CRQ,4bRzfSRtP2PCP4PtPt!so151C'g^5wP5ACDt5R=!tK%9cbCR<A5CttRe[A5CjjRdPz!#6]$QA5CMMP5PDfWRQ!t?/P?PqfXR@=5C@!#6WH<P51SCtO1,GzX9dCDRzX5xPzX5b!#MS,101P7O1b>PaP5EVb8b1W5W3PsP5P:P;Ghb1PgA0BuiRz!ve$]5R<A0B5mRm,6g!|D%!vn%ssPs!#G=295CuRiDWeW8%8rA0BusRr?\z;%2r%2z!zq&s]%2RPGQ0R!y@$2PCP{PaPu!sr1D]P5!xQ&|P}P4O3P\PCPkAFDO5A@B4}A0B5k,<=!wj&=!w_$!#Jz&R\PjP}!sy1R{D]]5X?CRR%2nA@Bj}P=!{K$2PCP5!sW5D]X2214w=Rn/Jd!#>,$5},<J!xH'JPd[A5COORs14b=Rr!xG%=Pe!xD$VR=!#;{$t!xG$Rg,>CR@P!#Qj$QQR_!xJIJ!xJ$jO1RJ,GrX9sCDA0BO|P9CHPcP5CMW5P}P5PKFib3b1X3yP5O1!v\+]!~<&|]PCPaPRAFDkaA1C}{,gnX22Pc!#5%$\5P2A9DMM/=514x@R\!{T%fURHPj!xY21Cj'g]@P4A9DttRc#2PDPH!ue%j!ue$9cxCRnA1CjHR{#KRk!vI$MROP\[PCP=AAB5MXSCP^PtP5EIAABttP2A0BMMQ0BP5P61XBMEVA1268RMP2PpP5Q06Pq!#Uf3Rp/p5Pq1Gq5Rab1b8b8XD{PkeX6nPxP@PAPCPgPH!t,$HHRgA0BHjRj':A9DHHRk'6A0B=tRt#8R{!#;u'tPDP=P=CR/P{!s8$6t/65!s3&6v6!#<0%n>6!#<++jPWCHPkP4CMPg1XBHCMANDHHP`PH!#<2+OCDW@%8cPd\nP\\sP1!tu$!yN%YRe!vg%=!~o'Q00PCPDfZ!yh'Q!s@$P_!sV$\!s:%eC?P1f]Re=CD4AAB4=f[R==5C=P5f_R==CD7AAB;eP2faRe=ND:PwX22RwP4PBP:PePBP:f^EQPDPeP:CRR;P|P:O1EV%2;PBP9fbR!s-$P=EQR=A9D;9R9;k5%29,P=P1PBPLfcR!s-%`EQ#2AFD1LA5CeeP5PBPPfeRePBPPP;EQ#2ffR;=FDWfg90B^R1fd!s-$L;\4%21%2L'[P0fhR09@BhA@BheA5C;;P5fiRe9@BZ!{K&SfkRL!{M&SLPCflR1fmR==FD5AAB4LA1C11R9#KR_]=]<X0CRQAFD11fjR@9AB=P2fnR==9D=PwP4P8PuEVPbP?PqPabFX19P_eb<W=W<PIP5P:P^Ghb;b1W;!#<=%Z;!tZ'P0!tX'0PCPeP!t7$eAAB@@!z>$LL!{E,LEVPM1pp4!t60=!t6;!#<k9;W<W;!#3I5!s/&bEbEW=WE!sH=W1X0C!sE71!s2$W1X6x!sd=X1n1G\JX9sCDW@!#9f15O1b@b>A0B||1XB|!#4\4G!uP>3PNPzPC16Nm,<<X0CP!#9V$!t368b>W5W3!u}>4!#E4$!sb&1!sb'PPP3O3b:b>bA16NNRNA0BZW'fA0BhWPCQ0916NfQ07'U'P!#CX$h!#]h$XYPZ!#9j%ZZPZPW!#W9@eQ03P5CHQ05P4CHWWWV!t}21!t}-7!#bQ$!t}47O2b7b>b2%B3RW#;13B3RZ/7ERE#;ALB3F3EA0B4FPCACD75RXQ01Q02#;'ZALB7F;Eo!#G#&4!u>$:WEPFP2PCQ08,7ZP3!uJ&33P3PF!#lPNeAqD34#2PCAqD75,<XX0C1uD395C4C^eW4X?CWSo"). Qed.

Lemma nstep_brk_iff : ltac2:(zQ "ha0!hof!h9!vf!ho8!j6!jc!ko9!jjb!hp5!hnf!ju5!kse!kt6!knd!hf!ktc!ku7!kv4!lg2!iqf!lgf!lh7!kh5!l9!le!m3>3req$e>3eff$b>3mo'$9>3evs@1$3$6>0@2$4@2$h7Z^4@2$h8^4@2$h9+2+k0@2$d@6$h5?2SC@1$h4^5?2mo^4^3^2@2$4@3$5@1$3$6^2@1$0$6=1r@1$2@1$1#k0@2$h6?2mo@1$7^5@2$4@3$5$b^5@6$h0^1@1$0@2$8@1$2@1$1#k0@1$3@1$2@1$1#8@3$h2@1$7^6^1@1$a?1h@2$h1^1@1$a?1h@1$0$f@1$0@2$8@1$2@1$1#k0$c@3$5$9^4@3$h3?2mo@1$7^6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) ["Shapes"] "#$4>p'0h01Hh11rh24evs'h32r2h42m'h54eff'h61Eh72NRh82SPh93reqh:1ih;1mh<1oh=2NSh>2_Hh?1bh@3effhA3evshB5lemmahC3mo'hD3HokhE2RBhF1BhG4Hok'hH4Hok2hI2HrhJ2NEhK2SNhL4SPURhM3_H0hN1dhO2r'i001ei011ni021si031xp%0p&0p;1p;2p;3p;4p;6p;7p;8p;;p;9g00?9k100Tg004nk20JTg005Jj1O!s/$oj1oTg006Mk20I!s0$jk20ETg007FR0j25Tg00eEj1eTg009]j2X!sC$aj1zTg00]Aj1}Tg00I9j26Tg00>Yj1_Tg02:0k10G!sB$_k20FTg008ej31!sC$gj3MTg02;bj4ETg026fR1j2NTg02<_k10=Tg02=`k40<Tg02>Gk30;Tg02?=j4vTg02@0R2j6uTg01hhj13Tg01f`j2<Tg00gMj2sTg01?]j1b!sU$bj39Tg02A`k20!tT$BLj4gTg02CXk10HTg01>fj1fTg01@Rj27Tg024UR3j20Tg02DPj4~Tg028Zj3CTg00^Yj1DTg02EWk30!s0$FIj4QTg02GJk60BTg02H5k70ATg02I0k30>Tg02JCj1KTg02K9j2VTg01E:j38Tg02L9j8yTg02M;j3[Tg02N1j4kTg00VMj6wTg01=2j4!t&$7?j4^Tg00K8j7rj6UTg02O7k40:Tg02PCk30!s|$PkS00k207Tg00a@k206Tg02QKj2|Tg02RYk105Tg02S]k604Tg018fk30?Tg02T`k20@Tg02Uhj4TTg02V`k203Tg02WUm;0CTg02XPj6iTg02YNm902Tg01gkj3pTf3R4f2R5f1R6f0R740?+0@p=4g02ZHR8P5P6P7CTp=ng01WP-037p=RP4!s?&Q#Dp=@p-0R9f6R:P1f5R;P0P2f4R2!sL'N;0Cp=tf7R<P:P;P2174!s?$Ei518p=Sg00ieR=A8567714p=:1567,55p=;P9P1g02[JP;P!sx,902p=qP<P:A9;2!s<&Eip=2g02\;R>P2A845!u2$91:;p=Hg00TDR?Ap456g00TdR@31/57p=GAp567=1?@p=?g00c=RA91?7,56p=]AC456=1?@!sR$FAC!sR+WA1?7@p=\P>!vF,=AM;24A[!sL%A'5p=>10=7p=L10>7p=PAp;24=1?@!sq'!sK$J!sk,9M24p={%K79[!tI$Ap=dA1>67p=ZA1=67p=aA!vA%4p=xA1?7Ap=l!sv+p=mA1?6!u$%h!tZ+p>09P>P!wK&P4P5Ei!u,'AA1856!sW$YP8!w-%CT=127,5;p=I10!sD&j!sD1p=`A1867p=cg00McRAg02]9R@$00RBg00Oa00J4g00P?RC#ORD#o%OD!s/$O#O#ORE#o+0I-0E4'5%eC#O#e!s&$e#O#oRC,XA%zEREPC%}ERF16E2%_FRGC4$0G+0F=1ACPCPF16E;RAPGC4RHp,2moRIAn245RJ3M%RHPHPIPJCES01'N%_@R@91B4RK!sa&:RL!sa$MAn;24RN7MIROp,2SCS02$0=RPPMPIP;C@RQ'5RR'5%RM!s9$NCERS/5QRT,5KP9^F9RUP9P9P1P1H0<RVPK!{%&]o:0;91RWPKCvRXPRPTPOPSP7PQPQ!sW$WPQCvRWEuFtP;%3:RS,<IRO%zD#}$00,sF#_RDp,1h#bRT99SOPOPTg02^_#_RRg02_W!sK%YGSP2PIPSPOC:S035;KRZPZ2019ZR[EqWB!v/%P7CgPA!v;'PIPLP7&0H>R\PNP7PDPLP7%fI#bR]177]R^PRPYG2!sO%P@FHCGX1F,0FS04'NPL!v1+N/5QRM,5KPI16E<RLP7P\An:;2S05!t$'P]P!sw<R_/5QR`,5KPUPVPKPXPMP`PNP_!vO&!vE%ZPZP!uF%!u<'~A?IS7S06PI%3<RJP6f8RA#3R[=?I7S07ACI[7']X3F,0FCFRZ1<IJRW91F6#DS08'N!ww&`6:0D91PPPCPFP[PGC4S09PIP5PDP[P5P]175]!u7%CQ1<I[RQ91F5#DR_AWI[5S0:f9RN#3R`!tJ%;ACI`!tJ+S0<'5RM!t<'hPMP_P7J0BK0AWBB0>J67P?!tK$!z\$S0=#RP6PDPJP6P]176]S0>!tN%S0?#KS0@5CIS0AQ09,VP#\R_%\7PCPFf;R1#3R9!sm%BPIA=567RXQ0BPI%K5RVE>X2B,0BX4=#LX5>#PRU3;/NMX?!tQ%J!sb%C!t#$S0DAWIL6!t&$:RL#3Ra!sF%EPIPXQ!s,$!sz6S0F3;RbPM[!y-$AP5PUCFRU,5_\ZP0P_PUPIP`P4PIPaP7!s+%EJ!wr'P7Q0E!tO$!se$1P;!tO$>RU#3R_!}x%PI!yA$!tM8CFP0f<RM,6E=WI:!sc$?Rc#3Rd!u4%G!u4%G!se9PIf=Re#3RfP<A?I_7S0HACI_!yd-P716EU=WIA!t'$BRg#3Rh!th$i!th$i!t%:3P>!sX$CRi#3S0I!t^%J!t^%J!s[7PIfARj#3RkP1PIPh!vM$h!vM1!sy$ERl#3Rm!tS$n!tS$n!sv4P3P=!sS$FRo#3Rp!sS$qPIA=467PqPI%K4!sW-PIPmPcPIPp!tD$p!tD6HS0K#3S0!zy$RrPIA=;67PrPI%K;!sq'P3PB!sT$IRr#3Rs!sR$tPIA=:57PtPI%K:!sR$PIPsPiPIfJRt#3S0MP7PIQ0M!tG6KS0N#3S0O!va%PPIA=A27Q0PPI%KAE>P0!sN$LS0Q#3S0R!sN%SPIPNP;P6D{Q0S?dINPIfMS0T#3S0UfGRuPIfNS0V#3Rv!ul$v!tK5PvPGC4PIP1P<P4D{!t7$O#3S0WPGC4?dIMfPRw#3S0X=WItPIfQRx#3Ry!sx$y!sx,Pj!tu%16Ew!v4$wA=eN;Rz7MI!s>&x!s>$x#RPxPIA=UL:R{CER|[R}%RwPwPIPzCEAMxI{R{[!tY$RS0Y,6E!s_1c1<CE\{!sW%Q0NCgP6n20010!s#$12!s-%0P}P7P5O1P|g02aXR|P0!#D7'EP4P;P7P\P!#8+$;P7%f4#bR}177}!#83%!sI%!#9+/Z[S0[P5P2!sb$6!sb$2P7%f5!sb2!sI%!sb-!#D<&CER}[S0\P2P:!sk$4!sk$:P7%f2#bRz177z!sk&!sI%!sk-\}!u8+~S0]!un9X<\X;=W:X9FQ0[^<\^;=^:|^9FP7fSS0^,6ER}!xm$}!xm%f@R}?=MAP6O5PIfTS0_,6ERzP7P\A=je!#<J$z!#;H1z!uW23PFPIfUS0`!sc-gUL!scDPIfV#3S0a!|3%!#6A,P7PIfW!su+fDRw?=}M!sxAP0fX!sY$=?I6P\A=ljeP6!sX$6P]Q!#9y&!sY$6P@FHPIfZRz#3R{!{<${!tN/16Ez=?I4P\Q0K?=w}P2PDf[!ta%2P]172]S0b!sy-2!sy$>PrP;PDf\!sP%;P]17;]S0c!sP%R{PlA8Iz;RzPjP@P7Gy1Zr{1alzA1Bj@3;P0P:PDf]!sf%:P]17:]S0d!sf%,ZtPo!t=$:C:PBPgP@CxPIf_!u>;Q0QPAPD16EzPAP]17A]S0e!ss%'ZP>PNPDf`Rz,6EPNP]17N]S0f!t{+CPFfaRx#3!~u&7Q0NPIfb,6EP1C:S0gA1Bu@S0h'5PIfdR~#3S0i!x?%i!tW,S0i[]7X5>PCPF%3z!su&{PtPI16ExPL!uE$o!uE$0Q0gQ0h!sg$Q0T!sH$~PeC:A1Bt@!#?Q$ff,6ER~PGC4R{PcPDP~PcP]17c!#@x%#KR~7[I%l7X??S0iP;%R{=CI~RzP{PIP~PxCkEw%lz!z}$h#3!z&$!yf$!u+$P}fg#3!yd$}AmIz}PMP7CBC^b7WMW>P6P7O2!}>0!s/&W0W!u,$7P}FrW0!sO=b6W6WG!so?XOF!sE7103000b8b!s&$CBW7W8!sm@2B!sm=W0X4=!sE@5>!sE?WE!v%@!vG>X0bP0Q0:Q0<PCPFP`PGC4,VP!x_$NP4!yB%MRb!#;@$<!#?K$<!#Aj:'hP7AWIa2A?Ib7S0:ACIb!#A&'P3PFA?If7S0hACIf!s?%!tF$f!tF/eP!t[$%3}R!zd$S0g!tF%g!tF@?Id7S0jACId7']P0A?Iz6AmIz6!t1$k!sq%k!t4'jP1!t4%wR!#;e$~PIPXP~!t2Bh4Q0I=mI21VP~#\16EwS0I=WIUS0l!sw%uR{!t:%m!u,%m!sy7RV#PRX'5Q02p,2AFP~PcH0:Q0lPXPNP>PVP;PDPxP;P]Q!#4j'VP=PqPIP<PDPpP<P]17<!#51,p?=!#Bb&p!t?-Q0I=8I;S0lPBPnPIP:PDPmP:P]Q!#5+&RX16ElS0m=8I:S0n;=7PnPI%KX!sn$P@Q0l==V@Rn9M~I%KVRV:09~I!#?a$Q!#E\$R~?MIn!s7%m!uy&#R!uw$Q0n==X@RXCES0n[%R~S0I!w3$nCEQ0m?MIX[S0mQ0!sf$16EoRX!si%lA8IX<S0o==p@Rp7MI[!s_%PcCgP7n211!{4$1!#<v+Q0mP7P0Q0[Q0\Q0Z!#Wl&CE[Q0]P7!#=R<X:|X9FQ0\!#=S0PXQ0lPIPpPF!yS$uR|P7P\PAPDA9{A]Q!#7w$A8I|AP@GAP7PDP|!#;m1|!#<g-<A?IX<P<PDA9X<!xQ'Q0oP@GARX91\pP41X\XCBC^O5b0Q0neO1b0P?Q0I=CIVR?Q0iP7%l?eA[~IV!zy%PcCkEUCBC^!s$$BCBW7WH!~~?X3F!#3cZX0ZCBQ0DQ0A#\Q0F3;/NZeQ0=Q0@7[IQ0=PIQ0@P5CkEUPPQ0CPIQ0?CQRV/NZeO2WDX1FQ06Q08,NV[^1F!#Vj$P\Q!#US%J!vc2J!#A11!#Sy$S!#Gs%;C@5;KRVA1B2@RZPW!sh$WP]17W!#:4%P;!sl$WC:5Y:RW'5[P;POPDA9SO]POP!sM%SQ!#XY$KQ07P\!#^H%7PDA9[7!t]&A8I[7P@GAEIX1F!uT&P:C@5jFRO,5Z[P0PZPOA1B;@ROP<PQ!sf$Q]PQ!t4'P:PIP[PQC:3;P7A1B:@RQP!|}$:P\P1PL!#Fh$A9b!tE-b!tE$R[!tG+BPIPLC@RS5jFA1B6@RJ1<IbR~PDPbP~P]17~!uu'LPIPbP~C:5Y1R~'5[XABPIP9!{6$LPNP@!t?%9!t?-9!t?$D`!zy%P!#Tc$N!u`$P0!ty,@P!ta%,0FPSA1B@@RS/5~P7Q0HP\PePM!t''_!t'-_!vc,!#8s%Q0jP\PUPe!sU'd!sU-d!w:1GPIPUC@1<IzR3PDPzP3P]173!ue&R~,ccA8Iz3R[,aU5;S[P7A?Ik7RbP\P}Pc!t2'k!t2-k!w#%?EIP0A?Ih6P\PjP}P@P6PDA9h6!#FJ&A8Ih6!v:%PP!#T+$gC@Pi1<IxRXPDA9xX]PX!x]+gPIPxPXC:!tW+x4P\PwPiP@P2PDA9m2]Q!#FS$A8Im2!t&'PqPIPlC@P>PoP:PDP{!#7e0qPlA8I{:R{P@P@P6Gy1Zoq1al{;;SP0P<PDQ0LP<!#9C,,ZuPoPI!s=$C:/5SQ0K1<IsRoPDA9so]Po!u-+uPIPsPo!u-$P7PNPDQ0MPNP]Q!#F$&,ZrP>PLPDQ0OPLP]17L!wI'rPPQ0SPIP7C@Q0NPIQ0UPMC:Ro/5S1<IvRsPDPvPsP]17s!s\'u,c5Q0QPIPvPsC:Rs5;S[]=X@>PPQ0PPIPrC@PtPIQ0RP1!u7$P0PoPSPe!st$eP]17e!st&/cu=;Ss!#FK%Q0WPUC:P=Q0X=8IcPjPDQ0Y#3RUPjP]17j!tS's1<IURuPDA9Uu]Pu!v/+6PIPUPu!v/$\SXC=PSP}PDPyP}P]17}!sg&1<IyRv!s>$vP]17v!s>&A8Iy}PIPyPvC:3Y1XB@RyB08E}vA1F}vRv%Dv+07Q00A1FjuR}%D}Q0^#3R},<I91FgREP7P7X6EP7O1%DEQ0_#3RE!sD%iRoPAP0!#5t%E!#5t%iPDPEPiP]17i!#bl'Q0`!s^,w#DRr[%Do!s`2w!s`$wP]17w!s`+[Rw!sM%Q0a!sN&lPDQ0aPlP]17l!sO+\rQ0VPiPcO2!#<j8PwP7P6O1Rwb0O1+06WJP7O1!sQ$10200021010011101bNPvPFPjPgPDP}PgP]17g!t:&P7!s:$!#9%,A8I}gPIP}P7C:3YX?F1cssA8IUjRU/aU1X8s1X=UCBPuP7Ewb0CBX>SQ0VP7EU!#JZ>W0W=PtP7P2!#K&C=W6WD!sp?X1!#<r?!sa?P<!twCX0VP0PZPWQ0;P\PAP<P:!#5J$`!#5J,`!#7,0PQ09PIP<C@5;OP7PBP@PL1<I9ROPDA99!#;r-R`PNPIP9POC:RO'5Q0hP\PMP1!#[%$A9f!t6-f!t6$R9!t8/<PIP1C@R:5;J[XAB1<IaRWPDPa!#=R1APIPa!#=R$NP0P`PO!t:,@P!sz+=;S:P7PM1<IfR:!tP$:]P:!}t+81<I_R:PDP_!#U6&!}f+dRf98IdR9,aePbP\P5PcP@P?!t~/gPIP6C@5;S[X@8PMPIP_P:C:P=P9PbP\1<IkRbPDPkPbP]17b!t,&RkP6!sr7~CQR?#D5;!#3P%!#YI$\P~P[!#:=&z!va-z!#<}-R^,0FR[!#;R&fPDPdPfP]17f!tD']CQR~#DRS'5PyP[PSPFP^PfA?IdfP\P]P9P@A=]9@R]D`1|Id1X\]CBC^P0A1Fbb#DRb\?R?A1F33#DPPQ0kPIPkCQRk[1<IhRh=1Fh#D\kPLP31|IzO2!#aP9?PwPbP71XFhO1b8b0X8~PSeCBCBPe!{0&e!}1E!{\%X0Q!{]?KCBbLA1B5@R@Q04PPPHPIP2C@RH3;P2%3;R;,<IRPPDA9;PTPPPT!y8&4PIP;PPC:5;@RP'NeO2Q01=;@H/NPeO2bKQ02&052PI!#aN$J04%32,<IPF!#c]&PT177T!#cX'IP;P7C:5Y2b1,5J'NeWIWAXC=X@8W9o"). Qed.

(* [comment removed for export] *)
Lemma mmap_off0 : ltac2:(zQ "50!r6!jl1!jc!li0!jjb@3$2$0@1$3@1$4Z$1").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00Td'0o"). Qed.
Lemma mmap_anon_34 : ltac2:(zQ "50!r6!jl1!jc!lj7!jjb@3$2$0@1$3@1$4+i2$1").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00Td'0o"). Qed.
Lemma mmap_anon_50 : ltac2:(zQ "50!r6!jl1!jc!lj7!jjb@3$2$0@1$3@1$4+j2$1").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00Td'0o"). Qed.
Lemma mmap_modeled_rw : ltac2:(zQ "50!jjb!r6!jl1!jc!lk6@3$3$1@3$4@1$0+3@1$0+i2@1$0Z$2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00Td'0o"). Qed.
Lemma mmap_modeled_na : ltac2:(zQ "50!jjb!r6!kj3!jc!lk6@3$3$1@3$4@1$0Z@1$0+i2@1$0Z$2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00c='0o"). Qed.
Lemma mmap_noaccess_na : ltac2:(zQ "50!jjb!r6!jl1!jc!ll8@3$3$1@3$4@1$0Z@1$0+i2@1$0Z$2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00Td'0o"). Qed.
Lemma mmap_modeled_fx : ltac2:(zQ "50!jjb!r6!kj3!jc!lk6@3$3$1@3$4@1$0Z@1$0+j2@1$0Z$2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00c='0o"). Qed.
Lemma mmap_noaccess_fx : ltac2:(zQ "50!jjb!r6!kj3!jc!ll8@3$3$1@3$4@1$0Z@1$0+j2@1$0Z$2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00c='0o"). Qed.
Lemma mmap_fixedna_fx : ltac2:(zQ "50!jjb!r6!jl1!jc!lmb@3$3$1@3$4@1$0Z@1$0+j2@1$0Z$2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00Td'0o"). Qed.
Lemma with_mmap_backing_34 : ltac2:(zQ "60!h9!hnf!vf!jc!lo5!jjb>1a@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1@3$3$1@4$4@1$5+i2^3^2^1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) ["Shapes"] "##$0h01ah11mh21np;1p;2g005Jj10Tg007aj13Tg00]Aj12Tg009]j21Tg00P?#0!s$-3#2R0g00ieR1f0,11W1X20W0o"). Qed.
Lemma with_mmap_backing_50 : ltac2:(zQ "60!h9!hnf!vf!jc!lo5!jjb>1a@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1@3$3$1@4$4@1$5+j2^3^2^1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) ["Shapes"] "##$0h01ah11mh21np;1p;2g005Jj10Tg007aj13Tg00]Aj12Tg009]j21Tg00P?#0!s$-3#2R0g00ieR1f0,11W1X20W0o"). Qed.

(* The model places a hint-0 grant by Linux's rule ([Placement.linux_place_is]); the four
   admissibility facts are kept beside it because every consumer reads them. *)
Definition mmap_grant_conds (a : word) (nZ : Z) : Prop :=
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h
  /\ region_free (vm_reserved h ++ vm_maps h) a (wz nZ) = true
  /\ linux_place_is h (kb_thp (m_kernel mo)) (wz 0) nZ a = true.

Lemma mmap_grant_conds_of_place : forall a nZ, 0 < nZ -> nZ mod page_size = 0 ->
  linux_place_is h (kb_thp (m_kernel mo)) (wz 0) nZ a = true -> mmap_grant_conds a nZ.
Proof.
  intros a nZ Hn Hal Hp. pose proof (linux_place_is_admissible _ _ _ _ _ Hn Hal Hp) as (C1 & C2 & C3 & C4).
  unfold mmap_grant_conds, wz. auto.
Qed.

Definition mmap_rw_model : ltac2:(zQ "40!h9!hf!hnf!vf>1a@1$3@1$0#k0>2nZ$1$2") := ltac2:(zQ "h10!h9!vf!lqe!lr5!hp5!hf!lrc!ju5!lsc!lta!jm8!lu6!jrb!jsa!ki3!imd!jjb\1a@1$1@1$0#k0\2nZ$5@2$f@8$6@1$d?1h@3$2@2$4@1$1@1$0#k0@1$1@1$0#k0@4$3@1$1@1$0#k0@1$1@1$0#k0^2@1$h0^1@1$a?1h@1$c?1h@1$e?1h@1$7?1h@1$9?1h@1$b?1h@1$8?1h?2mo").
Definition mmap_na_model : ltac2:(zQ "40!h9!hf!hnf!vf>1a@1$3@1$0#k0>2nZ$1$2") := ltac2:(zQ "h12!h9!vf!lqe!lr5!hp5!jjb!hf!lrc!ju5!lsc!lta!jm8!lu6!jrb!jsa!ki3!imd&@2$4@1$1@1$0#k0@1$1@1$0#k0&@4$3@1$1@1$0#k0@1$1@1$0#k0^2@1$5^1\1a@1$1@1$0#k0\2nZ$6@2$h0@8$7@1$e?1h@3$2~0~1@1$b?1h@3$2~0~1@1$d?1h@1$f?1h@1$8?1h@1$a?1h@1$c?1h@1$9?1h?2mo").

Lemma nstep_mmap_rw_iff : forall len eff mo' evs, 0 < len < 2^63 ->
  let nZ := pgup len in
  nstep (NMmap 0 len 3 34) mo eff mo' evs <->
  evs = [] /\
  ((eff = efferr ENOMEM /\ mo' = mo
    /\ ~ (exists a, mmap_grant_conds a nZ /\ vm_backing_used mo + nZ <= vm_limit h))
   \/ (exists a, mmap_grant_conds a nZ /\ (vm_backing_used mo + nZ <= vm_limit h)
                 /\ eff = mkEffect a [] [(a, wz nZ)] /\ mo' = mmap_rw_model a nZ)).
Proof.
  intros len eff mo' evs Hl nZ. pose proof (pgup_range len Hl) as [PG1 PG2]. fold nZ in PG1, PG2.
  assert (HnP : 0 < nZ) by lia.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 3; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0])) = 222) by reflexivity.
  rewrite (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [mmap_spec _ _ _ _ _ _ ?i mo _] =>
  pose proof (fun o => mmap_rw_outcome (wz 0) (wz len) (wz 3) (wz 34) (wz (-1)) (wz 0) i mo o
                mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_rw
                (place_declined_b_null _ _ _)) as R end.
  cbv zeta in R. unfold wz at 2 in R. rewrite unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  setoid_rewrite mmap_err_out_enomem in R.
  assert (BK : forall m, mmap_noreserve_backed_ok (wz 34) m nZ = (vm_backing_used m + nZ <=? vm_limit (m_vmmaps m))) by reflexivity.
  unfold wz in R, BK |- *. rewrite R.
  assert (RB : forall ret, Run.refusal_b (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 3; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo ret = bv_eqb ret (errno_ret ENOMEM)).
  { intros ret. apply refusal_b_mmap. exact SN. }
  unfold mmap_grant_conds, mmap_rw_model. subst h.
  change (with_mmap_backing (Z_to_bv 64 34)) with (with_mmap_backing (wz 34)) in R |- *. rewrite ?with_mmap_backing_34 in R; rewrite ?with_mmap_backing_34.
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [E|(a & (Hpl & C5) & E)]; try apply (linux_place_is_iff _ _ _ _ _ HnP PG2) in Hpl.
    + apply Ok_inj in E as (-> & -> & _). left. split; [reflexivity|]. split; [reflexivity|].
      intros (a & (C1 & C2 & C3 & C4 & Hpl) & C5). apply NS. split; [apply family_off_mmap_true; exact SN|].
      rewrite !RB. cbn [eff_ret]. split; [apply bv_eqb_refl|].
      eexists (mkEffect a [] [(a, Z_to_bv 64 nZ)]), _, []. split.
      * apply (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input]. apply R. right. exists a.
        split; [| reflexivity]. rewrite BK. split; [exact (proj1 (linux_place_is_iff _ _ _ _ _ HnP PG2) Hpl)|]. apply Z.leb_le. exact C5.
      * cbn [eff_ret]. rewrite RB. eapply grant_not_enomem; [| exact C3]. lia.
    + apply Ok_inj in E as (-> & -> & _). right. exists a. rewrite BK in C5. apply Z.leb_le in C5.
      destruct (linux_place_is_admissible _ _ _ _ _ HnP PG2 Hpl) as (C1 & C2 & C3 & C4).
      repeat split; auto.
  - intros (-> & HO). split; [reflexivity|].
    destruct HO as [(-> & -> & NG)|(a & (C1 & C2 & C3 & C4 & Hpl) & C5 & -> & ->)].
    + split; [left; reflexivity|].
      intros (_ & _ & (eff2 & m2 & evs2 & SP & NR)). apply NG.
      apply (syscall_spec_222 _ mo _ SN) in SP. cbn [in_arg in_args nth pure_input] in SP. apply (proj1 (R _)) in SP.
      destruct SP as [E|(a & (Hpl & C5) & E)]; try apply (linux_place_is_iff _ _ _ _ _ HnP PG2) in Hpl; apply Ok_inj in E as (-> & _ & _); cbn [eff_ret] in NR.
      * rewrite RB, bv_eqb_refl in NR. discriminate.
      * exists a. rewrite BK in C5. apply Z.leb_le in C5.
        destruct (linux_place_is_admissible _ _ _ _ _ HnP PG2 Hpl) as (C1 & C2 & C3 & C4).
        repeat split; auto.
    + split.
      * right. exists a. split; [| reflexivity]. rewrite BK. split; [exact (proj1 (linux_place_is_iff _ _ _ _ _ HnP PG2) Hpl)|]. apply Z.leb_le. exact C5.
      * intros (_ & RF & _). rewrite RB in RF. cbn [eff_ret] in RF. rewrite (grant_not_enomem (m_vmmaps mo) a nZ) in RF by lia. discriminate.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_na_iff : forall len eff mo' evs, 0 < len < 2^63 ->
  let nZ := pgup len in
  nstep (NMmap 0 len 0 34) mo eff mo' evs <->
  evs = [] /\
  ((eff = efferr ENOMEM /\ mo' = mo /\ ~ (exists a, mmap_grant_conds a nZ))
   \/ (exists a, mmap_grant_conds a nZ
                 /\ eff = mkEffectU a [] [] [(a, wz nZ)] [] [] /\ mo' = mmap_na_model a nZ)).
Proof.
  intros len eff mo' evs Hl nZ. pose proof (pgup_range len Hl) as [PG1 PG2]. fold nZ in PG1, PG2.
  assert (HnP : 0 < nZ) by lia.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0])) = 222) by reflexivity.
  rewrite (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [mmap_spec _ _ _ _ _ _ ?i mo _] =>
  pose proof (fun o => mmap_noaccess_outcome (wz 0) (wz len) (wz 0) (wz 34) (wz (-1)) (wz 0) i mo o
                mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_na mmap_noaccess_na
                (place_declined_b_null _ _ _)) as R end.
  cbv zeta in R. unfold wz at 2 in R. rewrite unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  setoid_rewrite mmap_err_out_enomem in R.
  unfold wz in R |- *. rewrite R.
  assert (RB : forall ret, Run.refusal_b (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo ret = bv_eqb ret (errno_ret ENOMEM)).
  { intros ret. apply refusal_b_mmap. exact SN. }
  unfold mmap_grant_conds, mmap_na_model. subst h.
  change (with_mmap_backing (Z_to_bv 64 34)) with (with_mmap_backing (wz 34)) in R |- *. rewrite ?with_mmap_backing_34 in R; rewrite ?with_mmap_backing_34.
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [E|(a & Hpl & E)]; try apply (linux_place_is_iff _ _ _ _ _ HnP PG2) in Hpl.
    + apply Ok_inj in E as (-> & -> & _). left. split; [reflexivity|]. split; [reflexivity|].
      intros (a & (C1 & C2 & C3 & C4 & Hpl)). apply NS. split; [apply family_off_mmap_true; exact SN|].
      rewrite !RB. cbn [eff_ret]. split; [apply bv_eqb_refl|].
      eexists (mkEffectU a [] [] [(a, Z_to_bv 64 nZ)] [] []), _, []. split.
      * apply (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input]. apply R. right. exists a.
        split; [exact (proj1 (linux_place_is_iff _ _ _ _ _ HnP PG2) Hpl)| reflexivity].
      * cbn [eff_ret]. rewrite RB. eapply grant_not_enomem; [| exact C3]. lia.
    + apply Ok_inj in E as (-> & -> & _). right. exists a.
      destruct (linux_place_is_admissible _ _ _ _ _ HnP PG2 Hpl) as (C1 & C2 & C3 & C4).
      repeat split; auto.
  - intros (-> & HO). split; [reflexivity|].
    destruct HO as [(-> & -> & NG)|(a & (C1 & C2 & C3 & C4 & Hpl) & -> & ->)].
    + split; [left; reflexivity|].
      intros (_ & _ & (eff2 & m2 & evs2 & SP & NR)). apply NG.
      apply (syscall_spec_222 _ mo _ SN) in SP. cbn [in_arg in_args nth pure_input] in SP. apply (proj1 (R _)) in SP.
      destruct SP as [E|(a & Hpl & E)]; try apply (linux_place_is_iff _ _ _ _ _ HnP PG2) in Hpl; apply Ok_inj in E as (-> & _ & _); cbn [eff_ret] in NR.
      * rewrite RB, bv_eqb_refl in NR. discriminate.
      * exists a. destruct (linux_place_is_admissible _ _ _ _ _ HnP PG2 Hpl) as (C1 & C2 & C3 & C4).
        repeat split; auto.
    + split.
      * right. exists a. split; [exact (proj1 (linux_place_is_iff _ _ _ _ _ HnP PG2) Hpl)| reflexivity].
      * intros (_ & RF & _). rewrite RB in RF. cbn [eff_ret] in RF. rewrite (grant_not_enomem (m_vmmaps mo) a nZ) in RF by lia. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mmap_fx_model : ltac2:(zQ "20!hf!hnf>4addr$0>2nZ$0$1") := ltac2:(zQ "h30!h9!vf!hf!jjb!lqe!lr5!hp5!mo6!lrc!ju5!lsc!lta!jm8!lu6!jrb!jsa!ki3!imd!jn3\4addr$2\2nZ$2@2$h1@8$8@1$f?1h@1$c?1h@3$4@2$6@1$1@1$0#k0@1$1@1$0#k0@4$5@1$1@1$0#k0@1$1@1$0#k0@1$3^2@1$3^1@3$7@1$e?1h^2@2$h2^2^1@1$h0?1h@1$9?1h@1$b?1h@1$d?1h@1$a?1h?2mo").

Lemma nstep_mmap_fixed_iff : ltac2:(zQ "h82!h9!vf!hof!hp5!ho8!jc!hf!ko9!jjb!j6!hnf!kse!ml1!lqe!kt6!lr5!knd!ktc!ku7!lh7!mp7!hve!mq8!jk9&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4addr$6>3len$6>3eff$b>3mo'$a>3evs@1$4$7>0@1$h5?2mo>0@2$h6@4$c^6^5Z+j2?2mo=2nZ$6@1$h7^6@2$h0@6$h3?2SC@4$c^8^7Z+j2?2mo^6^5^4@2$9@3$5@1$4$7^4@1$2$7@2$9@3$5$b^6@6$h2@1$8^8@1$2@2$3@1$1@1$0#k0@1$4@1$1@1$0#8~1@3$d~0@4$f@1$1@1$0#k0@1$1@1$0#k0@1$8^8@1$8^1~1@1$2$h1@1$2@2$3@1$1@1$0#k0$e@3$5$a^5@2$h4^8^1").
Proof.
  intros addr len eff mo' evs MI SF nZ.
  destruct SF as [(_ & F & _)|(_ & _ & Hl & AL & A0 & AC & RF & MC)]; [discriminate F|].
  pose proof (pgup_range len Hl) as [PG1 PG2]. fold nZ in PG1, PG2, AC, RF, MC.
  pose proof (alloc_top_room (m_vmmaps mo)) as TOP. unfold two_pow_64, stack_max_size in TOP.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0])) = 222) by reflexivity.
  rewrite (syscall_spec_222 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [mmap_spec _ _ _ _ _ _ ?i mo _] =>
  pose proof (fun o => mmap_fixed_noaccess_outcome (wz addr) (wz len) (wz 0) (wz 50) (wz (-1)) (wz 0) i mo o
                mmap_off0 mmap_anon_50 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_fx mmap_noaccess_fx mmap_fixedna_fx) as R end.
  cbv zeta in R. unfold wz in R. rewrite !unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  pose proof (fun o => R o AC ltac:(unfold page_size; exact AL) A0 RF MC) as R2. clear R. rename R2 into R.
  setoid_rewrite mmap_err_out_enomem in R.
  unfold wz. rewrite R.
  assert (RB : forall ret, Run.refusal_b (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo ret = bv_eqb ret (errno_ret ENOMEM)).
  { intros ret. apply refusal_b_mmap. exact SN. }
  unfold mmap_fx_model. subst h. unfold with_mmap_replacement in R |- *.
  change (with_mmap_backing (Z_to_bv 64 50)) with (with_mmap_backing (wz 50)) in R |- *.
  rewrite ?with_mmap_backing_50 in R. rewrite ?with_mmap_backing_50.
  rewrite vm_forget_range_id in R by exact MI. rewrite vm_forget_range_id by exact MI.
  rewrite !unsigned_wz in R by lia. rewrite !unsigned_wz by lia.
  assert (OKNR : Run.refusal_b (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo (Z_to_bv 64 addr) = false).
  { rewrite RB. rewrite bv_eqb_unsigned, errno_ret_ENOMEM, unsigned_wz by lia. apply Z.eqb_neq. lia. }
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [E|[E|(e & He & E)]].
    + exfalso. apply Ok_inj in E as (-> & -> & _). apply NS. split; [apply family_off_mmap_true; exact SN|].
      split; [rewrite RB; apply bv_eqb_refl|]. eexists _, _, [].
      split; [apply (syscall_spec_222 _ mo _ SN); cbn [in_arg in_args nth pure_input]; apply R; right; left; reflexivity | exact OKNR].
    + apply Ok_inj in E as (-> & -> & _). auto.
    + exfalso. apply Ok_inj in E as (-> & -> & _). apply NS. split; [apply family_off_mmap_true; exact SN|].
      unfold mmap_errnos in He. destruct He as [<-|[]].
      split; [rewrite RB; apply bv_eqb_refl|]. eexists _, _, [].
      split; [apply (syscall_spec_222 _ mo _ SN); cbn [in_arg in_args nth pure_input]; apply R; right; left; reflexivity | exact OKNR].
  - intros (-> & -> & ->). split; [reflexivity|]. split; [right; left; reflexivity|].
    intros (_ & RF2 & _). cbn [eff_ret] in RF2. rewrite OKNR in RF2. discriminate.
Qed.

(* [comment removed for export] *)
(* 08b1429: munmap cuts the range out of both ledgers ([mmap_fixed_destroyed_next]). *)
Definition munmap_model (addr nZ : Z) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) addr (addr + nZ))
                 (maps_subtract (vm_noaccess h) addr (addr + nZ))
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.

Lemma nstep_munmap_iff : ltac2:(zQ "h82!h9!vf!hof!hp5!ho8!jc!hf!ko9!jjb!j6!hnf!kse!ms0!lqe!kt6!lr5!knd!ktc!ku7!lh7!msb!hve!mq8!jk9&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4addr$6>3len$6>3eff$b>3mo'$a>3evs@1$4$7>0@1$h5?2mo>0@2$h6@2$c^6^5?2mo=2nZ$6@1$h7^6@2$h0@6$h3?2SC@2$c^8^7?2mo^6^5^4@2$9@3$5@1$4$7^4@1$2$7@2$9@3$5$b^6@6$h2@1$8Z@1$2@2$3@1$1@1$0#k0@1$4@1$1@1$0#8~1@3$d~0@4$f@1$1@1$0#k0@1$1@1$0#k0@1$8^8@1$8^1~1@1$2$h1@1$2@2$3@1$1@1$0#k0$e@3$5$a^5@2$h4^8^1").
Proof.
  intros addr len eff mo' evs MI (AL & A0 & Hl & AH & MH) nZ.
  assert (PG : len <= nZ /\ nZ mod 4096 = 0) by (unfold nZ, pgup, page_round_up_Z, page_size; split; [Z.div_mod_to_equations; lia| apply Z_mod_mult]).
  fold nZ in AH, MH. rewrite TASK_SIZE_val in AH.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len])) = 215) by reflexivity.
  rewrite (syscall_spec_215 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [munmap_spec _ _ ?i mo _] =>
  pose proof (fun o => munmap_exact_outcome (wz addr) (wz len) i mo o
                ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
                ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)) as R end.
  cbv zeta in R. rewrite !unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  specialize (fun o => R o ltac:(rewrite TASK_SIZE_val; lia) MH) as R'. clear R. rename R' into R.
  (* 08b1429: munmap also admits the injected ENOMEM; under AllocForced it is a
     spurious refusal, since the cut (return 0) is a non-refusal outcome. *)
  assert (OKNR : Run.refusal_b (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo (Z_to_bv 64 0) = false)
    by (vm_compute; reflexivity).
  unfold wz in R |- *. rewrite R. unfold munmap_model, with_mmap_destroyed, mmap_fixed_destroyed_next. subst h.
  rewrite vm_forget_range_id by (apply mminv_with_vmmaps; exact MI). rewrite !unsigned_wz by lia.
  split.
  - intros [-> [E NS]]. destruct E as [(e & He & E)|E].
    + exfalso. apply Ok_inj in E as (-> & -> & _). apply NS.
      split; [apply family_off_munmap_true; exact SN|].
      unfold munmap_errnos in He. destruct He as [<-|[]].
      split; [vm_compute; reflexivity|]. eexists _, _, [].
      split; [apply (syscall_spec_215 _ mo _ SN); cbn [in_arg in_args nth pure_input]; apply R; right; reflexivity | exact OKNR].
    + apply Ok_inj in E as (-> & -> & _). repeat split; reflexivity.
  - intros (-> & -> & ->). split; [reflexivity|]. split; [right; reflexivity|].
    intros (_ & RF2 & _). cbn [eff_ret] in RF2. rewrite OKNR in RF2. discriminate.
Qed.

(* [comment removed for export] *)
Definition mprotect_model : ltac2:(zQ "20!hf!hnf>4addr$0>2nZ$0$1") := ltac2:(zQ "d0!hf!mo6!lrc!ju5!lsc!lta!jm8!lu6!jrb!jsa!ki3!imd!jn3\4addr$0\2nZ$0@2$b@8$2@1$9?1h@1$6?1h@3$1@1$8?1h^2@2$c^2^1@1$a?1h@1$3?1h@1$5?1h@1$7?1h@1$4?1h?2mo").

Lemma mprotect_gc3 : ltac2:(zQ "50!r6!kj3!jc!nh3!jjb@3$2$0@1$3@1$4+3$1").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00c='0o"). Qed.
Lemma mprotect_mod3 : ltac2:(zQ "50!r6!jl1!jc!nj1!jjb@3$2$0@1$3@1$4+3$1").
Proof.
ltac2:(KReplay.run1 (kr_t_MmNodes ()) ["Shapes"] "p;2g009]j20Tg00TDg00Td'0o"). Qed.

Lemma nstep_mprotect_iff : ltac2:(zQ "he2!h9!vf!jc!jjb!hof!hp5!j6!ho8!hf!hnf!ko9!kse!r6!nk8!nlf!lqe!kj3!kt6!lr5!jl1!knd!jo2!hm2!ktc!ku7!mla!lh7!nmc!mq8!jk9&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>4addr$8>3len$8>3eff$b>3mo'$9>3evs@1$7$a>0@2$hc@3$e^5^4+3?2mo=2nZ$8@1$hd^5@2$h4@6$ha?2SC@3$e^7^6+3?2mo^5^4^3@2$6@3$2@1$7$a^3@1$4$a@2$h5@2$6@3$2$c@3$d?2mo@1$3^7@1$3^1$h0@2$6@3$2$b^5@1$h9$h6@3$2$9^4?2mo@2$6@3$2$c@3$d?2mo@1$3^7@1$3^1$h3@2$6@3$2$b^5@6$h8@1$3Z@1$4@2$5@1$1@1$0#k0@1$7@1$1@1$0#8@3$f~0@4$h2@1$1@1$0#k0@1$1@1$0#k0@1$3^7@1$3^1~1~1@1$4$h7@1$4@2$5@1$1@1$0#k0$h1@3$2$9^4@2$hb^7^1").
Proof.
  intros addr len eff mo' evs (_ & AL & A0 & Hl & AH & NC & MC & VD) nZ.
  assert (PG : len <= nZ /\ nZ mod 4096 = 0) by (unfold nZ, pgup, page_round_up_Z, page_size; split; [Z.div_mod_to_equations; lia| apply Z_mod_mult]).
  fold nZ in AH, NC, MC, VD.
  cbn [nstep node_input pure_input].
  assert (SN : bv_unsigned (in_sysno (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 3])) = 226) by reflexivity.
  rewrite (syscall_spec_226 _ mo _ SN). cbn [in_arg in_args nth pure_input].
  lazymatch goal with |- context [mprotect_spec _ _ _ ?i mo _] =>
  pose proof (fun o => mprotect_expose_outcome (wz addr) (wz len) (wz 3) i mo o mprotect_gc3
                ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
                ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)) as R end.
  cbv zeta in R. unfold wz at 1 2 4 6 7 9 12 13 in R. rewrite !unsigned_wz in R by lia. fold (pgup len) in R. fold nZ in R.
  specialize (fun o => R o ltac:(unfold two_pow_64; lia) mprotect_mod3 VD NC MC) as R'. clear R. rename R' into R.
  setoid_rewrite mprotect_err_out_enomem in R.
  unfold wz in R |- *. rewrite R.
  assert (RB : forall ret, Run.refusal_b (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 3]) mo ret = bv_eqb ret (errno_ret ENOMEM)).
  { intros ret. apply refusal_b_mprotect. exact SN. }
  assert (OKNR : bv_eqb (Z_to_bv 64 0) (errno_ret ENOMEM) = false) by reflexivity.
  unfold mprotect_model, mprotect_model_next. subst h. rewrite !unsigned_wz by lia.
  split.
  - intros [-> [HO NS]]. split; [reflexivity|].
    destruct HO as [E|(B & E)]; apply Ok_inj in E as (-> & -> & _).
    + left. destruct (mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) eqn:B; [| auto].
      exfalso. apply NS. split; [apply family_off_mprotect_true; exact SN|]. split; [rewrite RB; apply bv_eqb_refl|].
      eexists _, _, [].
      split; [apply (syscall_spec_226 _ mo _ SN); cbn [in_arg in_args nth pure_input]; apply R; right; split; [reflexivity || exact B| reflexivity]
            | rewrite RB; cbn [eff_ret]; exact OKNR].
    + right. auto.
  - intros (-> & HO). split; [reflexivity|].
    destruct HO as [(B & -> & ->)|(B & -> & ->)].
    + split; [left; reflexivity|].
      intros (_ & _ & (eff' & m' & evs' & SP & NR)).
      apply (syscall_spec_226 _ mo _ SN) in SP. cbn [in_arg in_args nth pure_input] in SP. apply (proj1 (R _)) in SP.
      destruct SP as [E|(B' & E)]; apply Ok_inj in E as (-> & _ & _); cbn [eff_ret] in NR.
      * rewrite RB, bv_eqb_refl in NR. discriminate.
      * rewrite B in B'. discriminate.
    + split; [right; split; [exact B| reflexivity]|].
      intros (_ & RF & _). rewrite RB in RF. cbn [eff_ret] in RF. rewrite OKNR in RF. discriminate.
Qed.
End Shapes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma spurious_refusal_iff : ltac2:(zQ "d0!jc!knd!h9!nne!ns5!nt5!nu6!nv6!og0!vf!oja!ok5!hnf>3cfg$b>1i$6>2i'$6>1m$c>3eff$5>0@3$0@1$9@1$2#k0@1$8^4@1$8^3>0@3$0@1$9@1$2#k0@2$7^5N0@2$7^4N0>0>1o@1$a$5@2$1@3$4^7^5^1@3$4^6^5^1@2$1@4$3^8^7^5^4@4$3^8^6^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_MmNodes ()) [] "##OHp'0h04evs'h12m'h24eff'h31Hh41bh51oh61Ah71Bh81Rh91Sh:1eh;3evsh<3reth=2FOh>3Ha0h?3Hnoh@3HsphA2RBhB3cfghC3effhD1ihE2i'hF1mi001ai011xp%0p;1p;3p;2p;6p;4g005Jj1;Tg007aj1]Tg00]Aj1WTg02:0j1ETg008ej36Tg02V`j2BTg02CXj1Y!sJ$gj34Tg026fj2DTg00I_j2JTg00eEj1CTg005oj1UTg00[Tj2HTg028Zj3GTg03_aj1MTg048ej1ZTg049[j2RTg009]j2QTg00K8j6@Tg02M;j3<Tg04:Uj1XTg04;Kj2PTg0247j1OTg02K9j2ATg02JCj13Tg00?9j1V!sJ$UR0j21!ub$FR1j28Tg01=2j4>Tg00VMj6\Tg027?j4?Tg02FIj4STg02Uhj4[Tg00TDR2f0R3g00TdR436p=Lf2R5f1R6;<3=624p=7g02\;R7P5P6P3C[p=9f5R8f4R9f3R:34A<563g00c=R;562'8p=0g00ieR</13p=21173p==1863,85p=N1A6!t'&:1173,86p=I!s0&!sH$5!sz$=62;p=FA623;p=KA4:56/83p=Tg04<Gg02aXR4g00P?R=#;!s$-]R>#WR?%E:%E536g01WPR@,B91B:@56?%Y7RAf6RB?493A4893'D]5P?%EBRCP2P21J>3RD%C=#;#C!s&$C#;#UR='Hf8RE/B@=GB6g01=MRFg03emRGP2%MDRD%Z3RH/R5RIP;n1011010002!s,%0n!s,%0020000P2P2f7RJ#ERK,J>RL/H=RM1BJ@RN=GB6PFP!s}$LRLP!su8RI!sw1RO562X4?P?1BB@R@P2P2PMAGB36P!sQ2=62OX4?!ud&CR>/H=AG8@3!tC'>R>1RH6!u<E,Q2PNP5E@PKP:E@A<J83A<B83562RNeX<?PN^<?P?PC!t&%PDf:RD%X3RC'P#ORN!t27!sQ&LP!sD8!u]&!sJ%>f9R>/PC#O!sQ7,Q2!tg%1AEJ1AEB562RKePKP21A>JRK%L3R;%3BRC97>Jg02]9#VRGf<RFPDA9563R?PFPD%35RNE0X0G'1X1<#2X27#=RL3N1:DERHA7EJCR@f;R=PDP?P=PDP!sV%,1G!sW''IS00'8RO'DX42P2%38RI9<JBRMANH;L/DOX42%LKRK%LMRMP=P>!sr$>!sr535R;PO[PD!sI$D!sI795KMRM18@LR@,8H[P1PHP@1:=>R@%3J97>ERLPFP=P?!s+$!t26P31:FDRK%3>RO97=DRPf?RQf=RRP?PQPR!u[7P1%3D97F=S01f@RSf>RTP?PSPT!sT5#=1:QRRU%3=97RFRVPSPQ!sS$Q!t^9%3FRF97TRRWfCRXfARYP?PXPY!t&7P0P7fDRZfBR[P?PZP[!sL51:XYR\%3QR]97YSRSPZPX!sS$X!tP9fFR^PZP?P^PZ!sH2P0P<fGR_fER`A9:63S02P_P`%3:S03!sQ-1:_`Ra%3X97`ZRbfHRcP_P?PcP_!tC:IRdP_A9863S04PdP_PI!sN'P0PGfJRePcA9B53S05PePcPC!sF$fKRf/:dRg%3_97dcRhfLRiPfP?PiPf!t;9PiPeA9E93S06PiPe%3ES07E0P1fMR9A9>86Rj74fAF9fOfORk/:9Rl%3f979iRmfPRnPkP?PnPk!t/9A9=J:R:94k9fNRo=FnFfRRp/:nS08%3o97nkRqfSRrPpP?PrPp!sn5Rs#=Rt'8P`PqPtPYP7PsPRP<PpfQRsA9Q63S09PpPsP]!sb-P>PGPsPnA9TD3S0:PsPn%3TRt!sJ$P8P2%3RRu9<skRv!sO'BRD%K3RwCTX42A9R>8Rx94nk%KvP1A4pn3A4ps6Ry[RzA4sn3A4rs6R{[R|A4rp5\{PiP3O1R{P6n20!#6@&12!s-%0X5APz^5AP3PDP5O2R}b3P3C>A<nkuR~PePuO1RuE\C?!s$$>C>W8W9P6P3O2!sw0!s/&W3X;G!sE7!#5n$W3X1<!sE@:7!sE?W7!tI?W6!sD=X3;P1PHQ00PRP=P?!s+$!#4h5@LP3PTPRP?!s+$!sH4,IPP1Q01PQPTP?!s+$!~^7YPQP?!s+$!t26UVP3P[PYP?!s+$!#3F9PXP[P?!s+$!sH4P`PXP?!s+$!t-6\SP3P`PZ!sH$!#316P^P`Q02!s,%!~}/!~>$?!s+$!s~6abP3PcP_Q04Pc!~g3PdPcQ05Pd!~`+P9!~L$9!~L795ghP3PfPeQ06!s,%!~F$A4ifjAFifOPs!~%$s!~%795lmP3A4o9:AFkoFQ08fTRo!}j$o!}j8N#=R?,8q!}k$?!}k$N!}k$rPsQ09Pr!}d7pPnQ0:PpPnP!}\,P~!s7$DP!}K&4skx%K~P1PzP|A4op5\yP{P3!|};|^5AP!|u&PvPuE@!|j~!|jOX7W!tJ@6K!|l?MC>A<EBIP6PIO1E@1A>EP3E@P>PEPBP8CSP>PJ!s0%'Deb=bAW@W>W?XC7XF<XE4WDWBo"). Qed.

Section Sound.
Context {SC : StepCfg} {AF : AllocForced SC}.
Variable segs : ltac2:(zQ "20!ho8!qj8@1$0$1").

#[local] Notation SSTEP := (sstep_cfg segs the_scfg).

(* [comment removed for export] *)
Lemma sstep_svc_inv : ltac2:(zQ "i64!ko9!j6!jc!h9!hnf!vf!kn8!nt5!ho8!io8!ol4!om1!ns5!omc!hof!jo2!on3!on9!oo2!oo9!inc!os9!lpb!lqe!ko3!ot5!nne!otf!ou7!pg6!pi2!pm6!pn7!po9!pp6!pq0!pqa!pr6&@4$ha@1$h5?2SC@3$a?4segs^a^8^9^3&@1$h8~0&@3$2@1$9@1$5@1$3#k0@1$h4^2@1$h2@1$5@1$3#k0&@3$c@3$a?4segs^b^9^a@4$h0$7^4^3^2>2ms$hf>2mo$4>2x8@1$5@1$3#k0>3evs@1$8$0>1X$b>0@3$2@1$9@1$5@1$3#k0@1$i0^5@2$d@1$5@1$3#k0^3>0@5$i1?4segs@1$h5?2SC@2$h1^6^5^3^2@2$f@2$6$7\3eff$7@2$6$4\3mo'$4@2$6$4\4mo''$4@2$1@3$c@3$a?4segs^a^8^9@4$h0$7^3^2^7@2$1~1@2$1~2@2$1@3$2@1$9$4@2$hc^2@1$hd^3@2$d$4^1@3$2$b^6@1$h3@2$h1@2$i5^a^3^1@2$f@2$6$7\3eff$7@2$6$4\3mo'$4@2$6@1$8$0\4evs0@1$8$0@2$1@3$c@3$a?4segs^a^8^9@4$h0$7^3^2^1@2$1~1@2$1~2@2$1@3$2@1$9$4@2$hc^2@1$hd^3@1$h2$4@2$1@3$2@1$8$0^7@1$e$0@3$2$b^6$h9@2$f@2$6$7\3eff$7@2$6$4\3mo'$4@2$6@1$8$0\4evs0@1$8$0@2$6@1$5@1$3#k0\4code@1$5@1$3#k0@2$1~3@2$1@3$2@1$9@1$5@1$3#k0@1$h4^3@2$d@1$5@1$3#k0^1@2$1@3$2@1$8$0^8@3$h6$0^2@3$h7$0@2$i2^1@1$hb^3@1$e$0@3$2$b^7@1$h3@2$h1^b^3@2$f@2$6$7\3eff$7@2$6$4\3mo'$4@2$6@1$8$0\4evs0@1$8$0@2$6@1$5@1$3#k0\3sig@1$5@1$3#k0@2$1~3@2$1@3$2@1$9@1$5@1$3#k0@1$i4^3@2$d@1$5@1$3#k0^1@2$1@3$2@1$8$0^8@3$h6$0^2@3$h7$0@2$i3^1@1$hb^3@1$e$0@3$2$b^7@1$h3@2$h1^b^3@2$1@3$c@3$a?4segs^7^5^6@1$he$7@2$1@3$2@1$8$0^4@1$e$0@3$2$b^3$h9").
Proof.
  intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _, _. eauto 6.
  - right; left. eexists _, _, _. repeat split; try eassumption.
  - right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; right. auto.
Qed.

Lemma at_node_pending : ltac2:(zQ "a0!h9!vf!oo2!io8!jc!ko3!pm6!pn7!pre!jj3>1n$9>2ms$6>0@3$8?4segs^2^1@1$5@3$4@1$3@1$1@1$0#k0@1$7^2@1$2@1$1@1$0#k0").
Proof.
  intros n ms H. destruct n; cbn [at_node] in H;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try match goal with H : _ \/ _ |- _ => destruct H end; congruence.
Qed.

(* [comment removed for export] *)
Lemma mm_input_spec_iff : ltac2:(zQ "h60!h9!vf!jc!ol4!nu6!omc!io8!j6!ns5!nv6!og0!knd!oja!pm6!pn7!hnf!nt5!pre!jj3!ps9!hve!mq8>1n$h2>2ms$d>2mo$f>2x8@1$1@1$0#k0>1i$4>0@1$h4^3>0@2$h5^6^4>0@3$h1?4segs^7^6>0@3$2@1$6@1$1@1$0#k0@1$e^7@2$5@1$1@1$0#k0^5>0@3$2@1$6$4@1$h3^9@2$5$4^5@2$7>1o@1$c$h0@2$b@3$8@3$3?4segs^a^8^9^1@3$8^7^9^1@2$7@3$2@1$1@1$0#k0@1$a@3$3?4segs^9^7@1$a^6@3$2@1$1@1$0#k0@2$9@3$3?4segs^9^7N0@2$9^6N0").
Proof.
  intros n ms mo x8 i MI SF AT SV NI.
  destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-.
  - (* [comment removed for export] *)
    cbn [at_node] in AT. destruct AT as [SV' A0]. rewrite SV in SV'. injection SV' as ->.
    split; [| split; [reflexivity| rewrite in_a0_si, A0; reflexivity]].
    intros o. rewrite (syscall_spec_214 _ mo o) by reflexivity. rewrite (syscall_spec_214 _ mo o) by reflexivity.
    rewrite in_a0_si, A0. cbn [in_arg in_args nth pure_input]. rewrite !brk_outcome. reflexivity.
  - (* [comment removed for export] *)
    cbn [at_node] in AT. destruct AT as (SV' & A0 & A1 & A2 & A3 & A4 & A5). rewrite SV in SV'. injection SV' as ->.
    split; [| split; [reflexivity| rewrite in_a0_si, A0; reflexivity]].
    intros o. rewrite (syscall_spec_222 _ mo o) by reflexivity. rewrite (syscall_spec_222 _ mo o) by reflexivity.
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, A0, A1, A2, A3, A4, A5. cbn [in_arg in_args nth pure_input].
    pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as [(-> & -> & PR & Hl)|(-> & -> & Hl & AL & Ap & AC & RF & MC)].
    + destruct PR as [-> | ->].
      * rewrite !(mmap_rw_outcome (wz 0) (wz len) (wz 3) (wz 34) (wz (-1)) (wz 0) _ mo o mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_rw (place_declined_b_null _ _ _)). reflexivity.
      * rewrite !(mmap_noaccess_outcome (wz 0) (wz len) (wz 0) (wz 34) (wz (-1)) (wz 0) _ mo o mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_na mmap_noaccess_na (place_declined_b_null _ _ _)). reflexivity.
    + pose proof (pgup_range len Hl) as [PG1 PG2].
      pose proof (alloc_top_room (m_vmmaps mo)) as TOP. unfold two_pow_64, stack_max_size in TOP.
      rewrite !(mmap_fixed_noaccess_outcome (wz addr) (wz len) (wz 0) (wz 50) (wz (-1)) (wz 0) _ mo o mmap_off0 mmap_anon_50 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)
                 mmap_modeled_fx mmap_noaccess_fx mmap_fixedna_fx);
        unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len); [reflexivity | lia| unfold page_size; exact AL| lia| exact RF| exact MC | lia| unfold page_size; exact AL| lia| exact RF| exact MC].
  - (* [comment removed for export] *)
    cbn [at_node] in AT. destruct AT as (SV' & A0 & A1). rewrite SV in SV'. injection SV' as ->.
    split; [| split; [reflexivity| rewrite in_a0_si, A0; reflexivity]].
    intros o. rewrite (syscall_spec_215 _ mo o) by reflexivity. rewrite (syscall_spec_215 _ mo o) by reflexivity.
    rewrite in_a0_si, in_a1_si, A0, A1. cbn [in_arg in_args nth pure_input].
    cbn [mmsafe] in SF. destruct SF as (AL & A0' & Hl & AH & MH). rewrite TASK_SIZE_val in AH.
    assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    rewrite !(munmap_exact_outcome (wz addr) (wz len) _ mo o ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
               ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia));
      unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len); [reflexivity| rewrite TASK_SIZE_val; lia| exact MH| rewrite TASK_SIZE_val; lia| exact MH].
  - (* [comment removed for export] *)
    cbn [at_node] in AT. destruct AT as (SV' & A0 & A1 & A2). rewrite SV in SV'. injection SV' as ->.
    split; [| split; [reflexivity| rewrite in_a0_si, A0; reflexivity]].
    intros o. rewrite (syscall_spec_226 _ mo o) by reflexivity. rewrite (syscall_spec_226 _ mo o) by reflexivity.
    rewrite in_a0_si, in_a1_si, in_a2_si, A0, A1, A2. cbn [in_arg in_args nth pure_input].
    cbn [mmsafe] in SF. destruct SF as (-> & AL & A0' & Hl & AH & NC & MC & VD).
    assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    rewrite !(mprotect_expose_outcome (wz addr) (wz len) (wz 3) _ mo o mprotect_gc3 ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
               ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia));
      unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len); [reflexivity| unfold two_pow_64; lia| exact mprotect_mod3| exact VD| exact NC| exact MC| unfold two_pow_64; lia| exact mprotect_mod3| exact VD| exact NC| exact MC].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma m_halted_vm_forget_range : ltac2:(zQ "80!hf!inc!io8!jc!h9!hnf!ig7!vf>2lo$0>2hi$0>1m$5@3$3@1$2@1$7@1$4#k0@1$1@3$6^3^2^1@1$1^1").
Proof. reflexivity. Qed.
Lemma mminv_vm_forget_range : ltac2:(zQ "40!hf!hve!hnf!ig7>2lo$0>2hi$0>1m$2>0@1$1^1@1$1@3$3^4^3^2").
Proof. intros lo hi m MI. rewrite vm_forget_range_id by exact MI. exact MI. Qed.

Lemma mm_raw_post : ltac2:(zQ "h30!jc!nu6!ko9!ho8!io8!j6!hnf!nt5!inc!hve!omc!hof!h9!on3!ns5!jj3!ps9!mq8!vf>1n$f>2mo$6>1i$1>3eff$7>3mo'$6>3evs@1$3$2>0@1$9^5>0@2$h1^7^6>0@3$0@1$4$1@1$h0^8@2$a$1^6>0@3$e^7^8@4$d$7^6^5^4@2$5@3$0@1$3$2^5@1$b$2@2$5@3$0@1$4@1$h2@1$c#k0@1$8^6@1$8^9@1$9^6").
Proof.
  intros n mo i eff mo' evs MI SF NI H.
  destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-.
  - apply (proj1 (syscall_spec_214 (pure_input 214 [Z_to_bv 64 req]) mo _ eq_refl)) in H. cbn [in_arg in_args nth pure_input] in H.
    apply brk_outcome in H as (r & _ & E). apply Ok_inj in E as (_ & -> & ->).
    rewrite with_brk_next_eq by exact MI. rewrite m_halted_with_vmmaps. auto using mminv_with_vmmaps.
  - apply (syscall_spec_222 (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo _ eq_refl) in H.
    cbn [in_arg in_args nth pure_input] in H.
    cbn [mmsafe] in SF. destruct SF as [(-> & -> & PR & Hl)|(-> & -> & Hl & AL & Ap & AC & RF & MC)].
    + destruct PR as [-> | ->].
      * apply (proj1 (mmap_rw_outcome (wz 0) (wz len) (wz 3) (wz 34) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_rw (place_declined_b_null _ _ _))) in H.
        destruct H as [(e & _ & E)|(a & _ & E)]; apply Ok_inj in E as (_ & -> & ->); [auto|].
        change (with_mmap_backing (wz 34)) with (with_mmap_backing (wz 34)). rewrite with_mmap_backing_34, m_halted_with_vmmaps. auto using mminv_with_vmmaps.
      * apply (proj1 (mmap_noaccess_outcome (wz 0) (wz len) (wz 0) (wz 34) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_na mmap_noaccess_na (place_declined_b_null _ _ _))) in H.
        destruct H as [(e & _ & E)|(a & _ & E)]; apply Ok_inj in E as (_ & -> & ->); [auto|].
        rewrite with_mmap_backing_34, m_halted_with_vmmaps. auto using mminv_with_vmmaps.
    + pose proof (pgup_range len Hl) as [PG1 PG2].
      pose proof (alloc_top_room (m_vmmaps mo)) as TOP. unfold two_pow_64, stack_max_size in TOP.
      apply (fun X0__ Q1__ Q2__ Q3__ Q4__ Q5__ => proj1 (mmap_fixed_noaccess_outcome (wz addr) (wz len) (wz 0) (wz 50) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_50 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)
               mmap_modeled_fx mmap_noaccess_fx mmap_fixedna_fx Q1__ Q2__ Q3__ Q4__ Q5__) X0__) in H; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
        [| lia| unfold page_size; exact AL| lia| exact RF| exact MC].
      destruct H as [(e & _ & E)|[E|(e & _ & E)]]; apply Ok_inj in E as (_ & -> & ->); [auto| |].
      * unfold with_mmap_replacement. rewrite with_mmap_backing_50, m_halted_vm_forget_range, m_halted_with_vmmaps.
        auto using mminv_vm_forget_range, mminv_with_vmmaps.
      * unfold with_mmap_destroyed. rewrite m_halted_vm_forget_range, m_halted_with_vmmaps.
        auto using mminv_vm_forget_range, mminv_with_vmmaps.
  - apply (syscall_spec_215 (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo _ eq_refl) in H. cbn [in_arg in_args nth pure_input] in H.
    cbn [mmsafe] in SF. destruct SF as (AL & A0' & Hl & AH & MH). rewrite TASK_SIZE_val in AH.
    assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    apply (fun X0__ Q1__ Q2__ => proj1 (munmap_exact_outcome (wz addr) (wz len) _ mo _ ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
             ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) Q1__ Q2__) X0__) in H; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
      [| rewrite TASK_SIZE_val; lia| exact MH].
    destruct H as [(e & _ & E)|E]; apply Ok_inj in E as (_ & -> & ->); [auto|].
    unfold with_mmap_destroyed. rewrite m_halted_vm_forget_range, m_halted_with_vmmaps.
    auto using mminv_vm_forget_range, mminv_with_vmmaps.
  - apply (syscall_spec_226 (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo _ eq_refl) in H. cbn [in_arg in_args nth pure_input] in H.
    cbn [mmsafe] in SF. destruct SF as (-> & AL & A0' & Hl & AH & NC & MC & VD).
    assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    apply (fun X0__ Q1__ Q2__ Q3__ Q4__ Q5__ => proj1 (mprotect_expose_outcome (wz addr) (wz len) (wz 3) _ mo _ mprotect_gc3 ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
             ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) Q1__ Q2__ Q3__ Q4__ Q5__) X0__) in H; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
      [| unfold two_pow_64; lia| exact mprotect_mod3| exact VD| exact NC| exact MC].
    destruct H as [(e & _ & E)|(_ & E)]; apply Ok_inj in E as (_ & -> & ->); [auto|].
    unfold mprotect_model_next. rewrite m_halted_with_vmmaps. auto using mminv_with_vmmaps.
Qed.

(* [comment removed for export] *)
Lemma mm_spec_iff : ltac2:(zQ "h80!h9!vf!ol4!hnf!nt5!omc!ho8!io8!j6!jc!knd!ko3!on3!pm6!pn7!nne!ns5!ko9!pre!jj3!lh7!os9!hve!mq8>1n$h3>2ms$d>2mo$3>2x8@1$1@1$0#k0>3eff$4>3mo'$3>3evs@1$6$h1>0@1$h6^5>0@2$h7^8^6>0@3$h2?4segs^9^8>0@3$9@1$7@1$1@1$0#k0@1$e^9@2$5@1$1@1$0#k0^7@2$a@2$8@3$h0@3$2?4segs^a^8^9@4$c$4^7^6^5@1$b@4$f@1$h5?2SC@3$2?4segs^a^8^9^7@6$h4?2SC^b^9^7^6^5").
Proof.
  intros n ms mo x8 eff mo' evs MI SF AT SV.
  destruct (node_input n) as [i|] eqn:NI.
  2:{ exfalso. destruct n; try exact SF; discriminate NI. }
  destruct (mm_input_spec_iff n ms mo x8 i MI SF AT SV NI) as (SP & NO & A0).
  rewrite (spurious_refusal_iff the_scfg _ _ mo eff NO A0 SP). rewrite SP.
  split.
  - intros [H NS]. pose proof (mm_raw_post n mo i eff mo' evs MI SF NI H) as (-> & _ & _).
    destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-; cbn [nstep node_input]; auto.
  - intros NS. destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-; cbn [nstep node_input] in NS;
      destruct NS as (-> & S & N); auto.
Qed.

(* [comment removed for export] *)
Lemma nstep_mm_post : ltac2:(zQ "h41!h9!vf!jc!oo2!io8!j6!ko9!ho8!hnf!jp4!inc!pqa!ip1!hve!hof!hf!kse!jj3!lh7!mq8&@3$2@1$4@1$1@1$0#k0@1$b^7@1$3@1$1@1$0#k0>1n$h1>2mo$8>3eff$h0>3mo'$8>3evs@1$7$6>0@1$d^4>0@2$h3^6^5>0@3$2@1$4@1$1@1$0#k0@1$a^6@1$3@1$1@1$0#k0>0~0>0@6$h2?2SC^9^8^7^6^5@2$5@3$2@1$7$6^6@1$e$6@2$5@3$2@1$4@1$1@1$0#k0@1$a^7@1$3@1$1@1$0#k0@2$5~0@2$5@1$d^7@3$2$f@1$9@1$c^7@1$9@1$c^9").
Proof.
  intros n mo eff mo' evs MI SF HH HK NS. destruct n; try (exfalso; exact SF).
  - apply (proj1 (nstep_brk_iff mo _ _ _ _ SF)) in NS. destruct NS as (-> & _ & ->).
    rewrite with_brk_next_eq by exact MI. split; [reflexivity|]. split; [exact HH|]. split; [exact HK|].
    split; [apply mminv_with_vmmaps; exact MI|]. rewrite alloc_top_with_vmmaps. apply alloc_top_brk_model_next.
  - pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as [(-> & -> & [->| ->] & Hl)|(-> & -> & _)].
    + apply (fun X0__ Q1__ => proj1 (nstep_mmap_rw_iff mo _ _ _ _ Q1__) X0__) in NS; [|lia]. destruct NS as (-> & [(_ & -> & _)|(a & _ & _ & _ & ->)]); (split; [reflexivity|]);
        [auto| split; [exact HH|]; split; [exact HK|]; split; [apply mminv_with_vmmaps; exact MI| unfold mmap_rw_model; rewrite alloc_top_with_vmmaps; reflexivity]].
    + apply (fun X0__ Q1__ => proj1 (nstep_mmap_na_iff mo _ _ _ _ Q1__) X0__) in NS; [|lia]. destruct NS as (-> & [(_ & -> & _)|(a & _ & _ & ->)]); (split; [reflexivity|]);
        [auto| split; [exact HH|]; split; [exact HK|]; split; [apply mminv_with_vmmaps; exact MI| unfold mmap_na_model; rewrite alloc_top_with_vmmaps; reflexivity]].
    + apply (proj1 (nstep_mmap_fixed_iff mo _ _ _ _ _ MI SF0)) in NS. destruct NS as (-> & _ & ->). split; [reflexivity|].
      split; [exact HH|]. split; [exact HK|]. split; [apply mminv_with_vmmaps; exact MI| unfold mmap_fx_model; rewrite alloc_top_with_vmmaps; reflexivity].
  - apply (proj1 (nstep_munmap_iff mo _ _ _ _ _ MI SF)) in NS. destruct NS as (-> & _ & ->). split; [reflexivity|].
    split; [exact HH|]. split; [exact HK|]. split; [apply mminv_with_vmmaps; exact MI| unfold munmap_model; rewrite alloc_top_with_vmmaps; reflexivity].
  - pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as (-> & _).
    apply (proj1 (nstep_mprotect_iff mo _ _ _ _ _ SF0)) in NS. destruct NS as (-> & [(_ & _ & ->)|(_ & _ & ->)]); (split; [reflexivity|]);
      [auto| split; [exact HH|]; split; [exact HK|]; split; [apply mminv_with_vmmaps; exact MI| unfold mprotect_model; rewrite alloc_top_with_vmmaps; reflexivity]].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mm_progress : ltac2:(zQ "90!kn8!hnf!ho8!ko9!kse!jj3!lh7!hve!mq8>1n$5>2mo$1>0@1$7^1>0@2$8^3^2@2$0$4\3eff$4@2$0$1\3mo'$1@2$0@1$2$3\3evs@1$2$3@6$6?2SC^7^6^3^2^1").
Proof.
  intros n mo MI SF. destruct n; try (exfalso; exact SF).
  - (* [comment removed for export] *) eexists _, _, []. apply (nstep_brk_iff mo); [exact SF|]. split; [reflexivity|]. split; reflexivity.
  - pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as [(-> & -> & [->| ->] & Hl)|(-> & -> & _)].
    + destruct (Classical_Prop.classic (exists a, mmap_grant_conds mo a (pgup len) /\ vm_backing_used mo + pgup len <= vm_limit (m_vmmaps mo))) as [(a & G & B)|NG].
      * eexists _, _, []. apply (nstep_mmap_rw_iff mo); [lia|]. split; [reflexivity|]. right. exists a. eauto.
      * eexists _, _, []. apply (nstep_mmap_rw_iff mo); [lia|]. split; [reflexivity|]. left. eauto.
    + destruct (Classical_Prop.classic (exists a, mmap_grant_conds mo a (pgup len))) as [(a & G)|NG].
      * eexists _, _, []. apply (nstep_mmap_na_iff mo); [lia|]. split; [reflexivity|]. right. exists a. eauto.
      * eexists _, _, []. apply (nstep_mmap_na_iff mo); [lia|]. split; [reflexivity|]. left. eauto.
    + eexists _, _, []. apply (nstep_mmap_fixed_iff mo); [exact MI| exact SF0|]. split; [reflexivity|]. split; reflexivity.
  - eexists _, _, []. apply (nstep_munmap_iff mo); [exact MI| exact SF|]. split; [reflexivity|]. split; reflexivity.
  - pose proof SF as SF0. cbn [mmsafe] in SF. destruct SF as (-> & _).
    destruct (mprotect_budget_ok mo (wz addr) (wz (pgup len))) eqn:B.
    + eexists _, _, []. apply (nstep_mprotect_iff mo); [exact SF0|]. split; [reflexivity|]. right. auto.
    + eexists _, _, []. apply (nstep_mprotect_iff mo); [exact SF0|]. split; [reflexivity|]. left. auto.
Qed.

(* LPS 727298f3: brk (214), mmap (222), munmap (215) and mprotect (226) do not read [in_mem]
   ([RomBase.memfree_NN]), so each node's specification is the same over every larger read-only
   backing ([RomBase.sys_rob], asked by [ITree.ns_rob]); boost-beast's Spec/MmNodes.v lemma. *)
Lemma mm_rob : forall n ms mo, at_node segs n ms -> mmsafe n mo -> RomBase.sys_rob segs (mkCfg ms mo).
Proof.
  intros n ms mo AT SF. destruct n; try (exfalso; exact SF); cbn [at_node] in AT; destruct AT as [SV _];
    (eapply RomBase.sys_rob_memfree; [exact SV | rewrite unsigned_wz by lia]).
  - exact RomBase.memfree_214.
  - exact RomBase.memfree_222.
  - exact RomBase.memfree_215.
  - exact RomBase.memfree_226.
Qed.

Theorem mm_node_sound : ltac2:(zQ "70!puc!pre!pva!jj3!lh7!hve!mq8@8$0$3?4segs?2SC@1$1?4segs@1$4?2SC$2$5$6").
Proof.
  split.
  - (* [comment removed for export] *) apply at_node_pending.
  - (* [comment removed for export] *)
    intros n ms mo evs X AT HH MI SF ST.
    destruct (ms_svc_pending ms) as [x8|] eqn:SV; [| exfalso; exact (at_node_pending n ms AT SV)].
    destruct (node_input n) as [i|] eqn:NI.
    2:{ exfalso. destruct n; try exact SF; discriminate NI. }
    pose proof (mm_input_spec_iff n ms mo x8 i MI SF AT SV NI) as (SP & _ & _).
    left. destruct (sstep_svc_inv ms mo x8 evs X SV ST)
      as [(eff & mo' & mo'' & S & NS & Hh & MAT & ->)
         |[(eff & mo' & evs0 & S & NS & Hh & MAT & -> & ->)
         |[(eff & mo' & evs0 & code & S & Hh & -> & ->)
         |[(eff & mo' & evs0 & sig & S & Hk & -> & ->)
         |(S & -> & ->)]]]].
    + pose proof (proj1 (mm_spec_iff n ms mo x8 eff mo' evs MI SF AT SV) (conj S NS)) as NST.
      pose proof (mm_raw_post n mo i eff mo' evs MI SF NI (proj1 (SP _) S)) as (_ & _ & MI1).
      rewrite (materialize_model_accesses_no_lazy _ _ (mminv_lazy _ MI1)) in MAT. injection MAT as <-.
      exists eff, mo'. auto.
    + exfalso. pose proof (mm_raw_post n mo i eff mo' evs0 MI SF NI (proj1 (SP _) S)) as (_ & _ & MI1).
      rewrite (materialize_model_accesses_no_lazy _ _ (mminv_lazy _ MI1)) in MAT. discriminate.
    + exfalso. pose proof (mm_raw_post n mo i eff mo' evs0 MI SF NI (proj1 (SP _) S)) as (_ & Hh' & _). congruence.
    + exfalso. pose proof (mm_raw_post n mo i eff mo' evs0 MI SF NI (proj1 (SP _) S)) as (_ & Hh' & _).
      rewrite (m_killed_of_m_halted_none mo') in Hk by congruence. discriminate.
    + exfalso. apply (proj1 (SP _)) in S. destruct n; try (exfalso; exact SF); cbn [node_input] in NI; injection NI as <-.
      * apply (proj1 (syscall_spec_214 (pure_input 214 [Z_to_bv 64 req]) mo _ eq_refl)) in S. cbn [in_arg in_args nth pure_input] in S.
        apply brk_outcome in S as (r & _ & E). discriminate E.
      * cbn [mmsafe] in SF. destruct SF as [(-> & -> & PR & Hl)|(-> & -> & Hl & AL & Ap & AC & RF & MC)].
        -- apply (syscall_spec_222 (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 34; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo _ eq_refl) in S.
           cbn [in_arg in_args nth pure_input] in S. destruct PR as [-> | ->].
           ++ apply (proj1 (mmap_rw_outcome (wz 0) (wz len) (wz 3) (wz 34) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_rw (place_declined_b_null _ _ _))) in S.
              destruct S as [(e & _ & E)|(a & _ & E)]; discriminate E.
           ++ apply (proj1 (mmap_noaccess_outcome (wz 0) (wz len) (wz 0) (wz 34) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_34 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) mmap_modeled_na mmap_noaccess_na (place_declined_b_null _ _ _))) in S.
              destruct S as [(e & _ & E)|(a & _ & E)]; discriminate E.
        -- apply (syscall_spec_222 (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 0; Z_to_bv 64 50; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo _ eq_refl) in S.
           cbn [in_arg in_args nth pure_input] in S.
           pose proof (pgup_range len Hl) as [PG1 PG2].
           pose proof (alloc_top_room (m_vmmaps mo)) as TOP. unfold two_pow_64, stack_max_size in TOP.
           apply (fun X0__ Q1__ Q2__ Q3__ Q4__ Q5__ => proj1 (mmap_fixed_noaccess_outcome (wz addr) (wz len) (wz 0) (wz 50) (wz (-1)) (wz 0) _ mo _ mmap_off0 mmap_anon_50 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia)
                    mmap_modeled_fx mmap_noaccess_fx mmap_fixedna_fx Q1__ Q2__ Q3__ Q4__ Q5__) X0__) in S; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
             [| lia| unfold page_size; exact AL| lia| exact RF| exact MC].
           destruct S as [(e & _ & E)|[E|(e & _ & E)]]; discriminate E.
      * apply (syscall_spec_215 (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) mo _ eq_refl) in S. cbn [in_arg in_args nth pure_input] in S.
        cbn [mmsafe] in SF. destruct SF as (AL & A0' & Hl & AH & MH). rewrite TASK_SIZE_val in AH.
        assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
        apply (fun X0__ Q1__ Q2__ => proj1 (munmap_exact_outcome (wz addr) (wz len) _ mo _ ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
                 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) Q1__ Q2__) X0__) in S; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
          [destruct S as [(e & _ & E)|E]; discriminate E| rewrite TASK_SIZE_val; lia| exact MH].
      * apply (syscall_spec_226 (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot]) mo _ eq_refl) in S. cbn [in_arg in_args nth pure_input] in S.
        cbn [mmsafe] in SF. destruct SF as (-> & AL & A0' & Hl & AH & NC & MC & VD).
        assert (PG : len <= pgup len) by (unfold pgup, page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
        apply (fun X0__ Q1__ Q2__ Q3__ Q4__ Q5__ => proj1 (mprotect_expose_outcome (wz addr) (wz len) (wz 3) _ mo _ mprotect_gc3 ltac:(unfold wz; rewrite unsigned_wz by lia; unfold page_size; exact AL)
                 ltac:(unfold wz; rewrite w_is0_wz by lia; apply Z.eqb_neq; lia) Q1__ Q2__ Q3__ Q4__ Q5__) X0__) in S; unfold wz; rewrite ?unsigned_wz by lia; fold (pgup len);
          [| unfold two_pow_64; lia| exact mprotect_mod3| exact VD| exact NC| exact MC].
        destruct S as [(e & _ & E)|(_ & E)]; discriminate E.
  - (* [comment removed for export] *)
    intros n ms mo rsp mo' evs AT HH MI SF NS.
    pose proof (nstep_mm_post n mo rsp mo' evs MI SF HH (m_killed_of_m_halted_none _ HH) NS) as (-> & Hh' & _ & MI' & _).
    split; [exact Hh'|]. split; [exact MI'|].
    destruct (ms_svc_pending ms) as [x8|] eqn:SV; [| exfalso; exact (at_node_pending n ms AT SV)].
    destruct (proj2 (mm_spec_iff n ms mo x8 rsp mo' [] MI SF AT SV) NS) as [S NSP].
    unfold nret. eapply sstep_cfg_syscall; [exact HH| exact SV| exact S| exact NSP| exact Hh'| apply materialize_model_accesses_no_lazy; exact (mminv_lazy _ MI')].
  - (* [comment removed for export] *)
    intros n ms mo code mo' AT HH MI SF NX. exfalso. destruct n; cbn in NX, SF; contradiction.
  - (* [comment removed for export] *)
    intros n ms mo AT HH MI SF.
    destruct (ms_svc_pending ms) as [x8|] eqn:SV; [| exfalso; exact (at_node_pending n ms AT SV)].
    left. exact (mm_progress n mo MI SF).
  - (* robustness over a larger read-only backing *)
    intros n ms mo AT _ _ SF. exact (mm_rob n ms mo AT SF).
Qed.
End Sound.
(* [comment removed for export] *)
