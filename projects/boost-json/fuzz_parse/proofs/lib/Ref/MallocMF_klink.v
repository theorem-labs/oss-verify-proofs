(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch's channel reader. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc Prog KInv AllocTop VmKit MmNodes GapGrid KLink KLink2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RelSpec RefNodes HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MallocMF_klink () := KReplay.lz_vm "#&tWC47Corelib7Program6Basics4flipC4ELinuxProcessSemantics?!s<22Fs4path!st,4Init5Logic8eq_ind_rC89OSSVerify6Proofs:boost_json:fuzz_parse3!sg#Spec6Malloc4aptrC13~~~I!sjT5STree5stree00!sl%!tXU5Monad1M!sf&!u^;trans!t+[5mbind!tp[6MSafeP4etwf!sjV3Lib2Nd9ex_elimF1!tVcassn!vL89Datatypes3fst!y']o!y'+C46Stdlib5Lists4!s+#8nil_cons!wr86!zR%!{FN2Fs!t5+9micromega5Tauto5eKindI!sE;8GFormula00!ud]c!ud-!u'I5State7PipeBuf!vB8map!vB$!|dVKLink3KLB!|b'i!z+PRef>!uP%MF_klink4KLBM!}W]7MmNodes5mminv!sl%K!#53+Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!{E;6op!sL#00!wxQ8m_haltedK!t#C2I!{B72eq!tAVvmmaps!yrRvm_!s\$!wtT4KInv4vm!#4Y&!vb<4prod!uES;vm_noac!s;#!{^72In!u%Z3ehi!yrC1Z02C5!tD&6ZArith6BinInt1Z3pow!sC<2le!v#=list!#3GV!u-$7ld_resv!#3HV9!}]$_top!tKVProg5rba!#:v'!x7Treserved!#7n+!x8%7!s+#Def3mapK!vTA2C7!u/N8HeapCeil5hceil!u-W<vm_start_brkC!#3I?;bv_unsigned!zS\lo!tt&!yp=t!zQ=sub!#6$F1!#3t73an!}V$!#4Y:length!wg<3nat!#4v4Peano2le00!u+<6modulo!w^Q6vm!wX$!v%<mul!sC=ad!#79<!#4V$1!x0Z9ld_groups!#C@Y6Decode8mmap_len!#<4Z!#7>$went!sh`8brk_disj!slald_metas!#8r7!#;3&x!z<>3appI!#8O55NoDup!#6L[!wu#brkreg!#8Z2!#=?91!wP\cov!vb`6!ty%!v`?or!#<NR=vm_live_byte!#L]V!#Dk#6ltotal!#4hA6of_nat!t3]cou!{4+!#AKP!u\$mitk!}DP!#FX:1!wJ3!#>v50!#?<?1I!y\Zmled!#H$&I!uzP5Model!tf?!#8n+3!#:]ZwwZ!#5MaCEIL_MIN!smhAX!~4B!#:R#!~1V!#O1&PGSZ!~3`7LEN!tv,!y+Z9brk_phase!y1,!~}64True!#6$V!}6&BUDCAP!#8V`set!#3v#!sl%c!}Eb7km_!#P2+!stghalt!sti5km_!#M&&!thgna!sto!#J`+!stc6km!#Jo#!ssh8!wI#!#Hy+!suc;!u`&!tom:!sx'!wSk9!sw'n!v`m!#Kv#!tmm!#FM-!tmg!#D7,!xOgdistinc!ugn!#D?-!ugg!#7A#!}rm!#6>l!tk#!#B3,!#?7P6VmMaps!#EHR:!#EEd9!vo$_!#8G'!#IrZse!#U+#ph!sm[!t]%:lbrk!uH&!so`8!so$c!#Np\!sm&sum_g!#PI]!sm-m!smeframe_o!#L#%K!zqPLib5!#g2#4node09!tY\!#qL#4msy!wi\!#^>#:!yI&_ps!tYcupd!sicret!uD`6ps!#P`+K!|SZ!#ER+2!so[!#Gt%2ev!#Mq&!#5/b?ev_step_p!sZ#mf!vE[!#nI&6mmsafe!smV!{%,5n!t`#!si&!#S&:>pow!u'#_nonneg!sN<:!sN#!sJB7compareK!#Yd8q01!#eCA1K!#u^46VarMap1t01I!sD?0!sD6=RingM!s4'7!#vI'!t567Env!sT#5PExpr!tX8!st:1!stE7!#xM;8B!sm&!sH6:Z!t;+=Z!sT$CheckerC!u~<4f!#z8#!sq?C!sq0_sound!zf]2wz!{Qc:!~/#resu!#Lw&C6!#=uH3Sys2Mm4Mmap!sk$un!#sX#!seV=with!#6f#next!uB]=!}%$!so$if!$&%Z!#VQ&dec!sp#0!v4]>!tW#model!uN%!#pOP!v2$!#x&%!tKV!#7O#zerosK!#aXPSyscallEffec!#X{W!#>F$?!y%,_no!#NN&!#fn;4negb!#l/<ltb!sa=andb!v{Q?page_r!}3#_up_Z!xL\!sn%ange!y~[5no_cc!}|cA!$%r#_!yJ/!sxbD!$$Z&!s{6!w2P4m_fd!#zVQm_vm_lazy!s^QA!s^$materialized!{bQ7Vm!s-$01!uYTi!#t~Rm_fsys!s[Tproc!s[Q5!#j&#!t7TtimeK!#h@V!vZUv!tlR9vmst!$-=#!#VNcKLBM!yJ#eq'!{B'!#~1>D!#~1,_in!~X&!sY@:bv_!#{7#us!#I,Y5ps_fa!#Ip_!si#so!si[!#7w$Cvm_only!~n6!#7];eq!#7z<6ltb_!$$k=4of_N!#B'5;ZifyClasses!$=c#ff!$Bs8iff_refl!sjB3inj!sIB5mkre!snC9and_morph!sOB7rew!u+%!sM49SatDivModCZ!yL#!#Ii%!#IpCdi!y{$!u~83no!$+p=div!sC<=!tP#pos_b!#E|#!sM@!tt#!sM15!uH$8PreO!s/#1Z;!tt#0_r_ext!sL>!st#!sL'!#<BR9LiaTuning9zify_don!#O'%!#LI?2K!#J?;!$CG'3!#K-D2!wF85proj!$8e<8eqb!ze$!#Nu7!$0r#1!#5=b<!#5=#re!#bw,!#P39x!#Cw\C!#Fl0!#C{-!x5S2Nd:!|\#!$KU#7!#@Xb@!#J|/_eq!swd!#MI+_query!u]g3!td[!$N4%9mspec_!#^0]!#Z5%>brk0_answer!#`U'!tec!#^<]!#:_#4ps_m!#:^`<!#:^&!#8b#!t[[!#^B#!v;d!sm$:event!#]I#!yWg5!wpi!#bC]!so&:!so%!$Wx+!#6\E4!sJF5!#=<Dapp!#>pB!sK$!#8?F8!uw\5!uw$!ur%I!{VY6P!#KO$!$'f8!#RZ,boo!$1[/!sF81!sf=unit!#_x7!v,%4kind!#ao>!sf$!#`=D3Op205!{GT5ITree4resp!v#3!$Ta50!#iJd!$7Q'!#LgO!~#$00!$K2O4Scfg=hunspell_scfg!xZB:!#f^$ison!#eE7!#bD,;!#?K$!tR$!xL8!wd63!ukQ7MemCopy!$XT=!$6+#!v4VE!v4+!#:/#_forced!#:ua5TWO64!sk&!v/58ZifyInst7Inj_Z_Z!#AW7!$5i$!$<|U!tS&6ms!~5/!#:i[!v6%top_!#f4'!t}77and!$cs#!t6Z;!$Js&_g!#Gm<!ya15Psatz!#Gx7!z^;2!#Hj?!#HFE3!uV[8elo_!$La^!sm'hi!sm-!vBK6!{2\=!xn%ceiling!u3a@!sr0!yf+!x-N1!#XO@7Z_to_bv!#iuQregion_free!#B>Y=l!#ex&s!#C1X!#e|#M!t]$<!#[<'li!yDbA!uP-_app_!$lK&!#is<eb!uyZ7l!#]8#!#J1b;!sl%!wS%!#6@0!$Sa,7forallb!sB7>!sB&_!s-%!tX]iv!$V\#oi!}kc:In_!v<k!#m^&p!$Ul8!$St+1!v:7:in_map!#[Y/!sE-9in_or!y@#!ua[?!z0/In!$KH%!#VSbAwent_In!#[=$s!$&T]!#47%!tt/!$\0^!|u&!#:Z'!we'!wbB2!#9_D4!t[[C!y9-_al!$fq$!|W&!#As:or!#dj>eb_le!yE+4Bool!s'$:orb_true_r!t%=sn!#aa87f_equal!#M4E6!#6HT!#uF$9!$Sq#BAND!#3P=ex!s2#b!t2[7!#}R%!x`3!$YP5!#?E>3Pol!#LJ7!#;P:!#?o[>!$$G$!u,&!#nI&!#z3U;brk_grow_ok!t[[B!#lO,!#yCa!#Mu+quie!#7Xa9!#=f#dea!#VU<!#BF77!sOK5!#k#<add!#k##!#4;Z!w]-_facts!~\37!#WF%?Relation!s6&=eq_Tran!$_P$!sV59Morphisms:respectful!s}E<eq_Reflex!s|BJr!sL'_eq_dom_r!s]GI!s],!s0,proxy!s\?@!sR0per!sS??eq!sL&!t#;!uk7Symmetric!sUE8s!sR%!u%@NR!u%,artial!#CZ#m!sF&!sa?M!%8A#_co_!%3Y#v_impl!s`,3!#G{$7tac!~T#<!#7B%_help!#7d79Fal!$LU#d!#=qbB!#mF#!#Ge6!|/24Znat5Nat2Z9i!$?k'!#7\S!#H2$C!#JG%_!${^-!#38`vmwf!%7q$!sn`!#OG#pair!smclo!sm/!%$%ORef!#n;#?!$Rn+!uP/!#|4;succ!w}>8inj_!sJ#!#^zd3!v<aD!#sF1grow!$PZV!#j734!vAB7eqb_neq!#:}Y!$OJ&!$[I'!snU!#U,&!ux#!#mrc!#F}&!#kK#g!tj#i!v$#q!#;{P!#kWF7!#GXD5!#4X76eq_sym!z1e!#oZ%I!#3xS!#DV%!w7&!#_v&!#dWH1!|]>6!|]#le!#kVA!%<l85!#7f#!#i<Q!uD7!$S_V!sn71!v4<!#GH/!#GiC2C5!#;L'!#HH%6PosDef3Pos3ad!$,2<7pos_sub!~`a6!#3Mf!$\;&4!ty1:!s,%_dec;Z_lt_le!s2#!xP26!z|#if7sum!#qh$!tZa2!tZ2!w?,!$2`/div!$2`N!wO#!teV!%O_'!$Zo[!~53!#km'!#ahN<vm_!#UJ#base!$h2Qvm_init_sp!$@AP!$iJ&!$~Q\>!u%$!$&Le!#mv$is_er!#@5[8A!sk#TopA!#mw+same_sp!#:+`?!#Z''!~-#p!#i%a<wcov_rf!#[l-!#VD59in!#HZ#or!#=pY!$l_#!$t+,!#<&J!#`t+7Sorting;Permut!#J|#B!s2-_middleK!u46!%9_%2!sr@A!sr/!sW$!vr[9!vr$mon!$Cla=!$lt&!#Es-!vV5!$&q-;!$@^%_rev!#Bb^!%A=[!u53g!u52!}D[=!}D%no_form!v&2!#`A+>!#`A'intro!#a'=tb_!$V#\=dec!#5w$n!$@d'!sr[8!sr'!w4a@!~u+!#dB0!xsUProg9neg!w6%!sm[!$=7&4pgup!#9zW!%^U%tains!#B^Z8!#8a&01!u?c!w#%grant!te#d!$Ztc=!yW%a!#Ng$!stirw!st/!$x?_:!{=Z!sj%6eff!#<+]!$_2'!#fK$!vH'!$gp+!ya:5Riscv7Prelude6bv_eq!#iq[<!yS%dd!#PQdB!sq/!#4J%!sw%!#W_N7Rel!sz#;!uN%!$At-!|iP?vm_backing_used!wfirw!wf,!}fe2!w7a7!$E8%!sl%!#`Sb=!#`S#!zD%ew!tha:!#:h$_n!#X2cD!t_$fixed!#Ft2!$~G_!wA\!#>~#4MAPF!zTW6ENOMEMI!yQd0!tLW9!$mU#size!wV\9PROT_NONE!xGb7!so$RW!z#a<!uH+!#]H'!%'bfm!#=-$re!$$4]!#?J#>!#A{'!{%$!sr`7!%,K%!sk%!$I_Y9!|Y+!$>S\6!wA$2!$3_0bov!$1b=>!#}8%_!s-%!#>Abfx!#?7hD!#8%,!v7%!$}^d!#I8$of!#4SZ!wm33!t^a<!t^'!$9@^!x`'!#}y#subtract_!%tP'!#`>@!%i`?opp!#nJ<lan!$wpQ=!tp0!$>AQiv!s`,!#4>YF!v@1In!#A>/!s{ZD!tg-!#JL'!y+Z!#aM/8!#4>[KInv5MAPFX!{Mk!#hSZ!#IE-;!|9a:!#7S#!%+r#!t[Z!$3z&!$=~#!uM\!#;m-2ev!#v#bC!#55#len!~c#!#S?a!#67&<!vE%!#7+h@!#7+%!sy%!#LnC!#ej9!#Hm#emove!#56[>g!sh&_sp!#6+]!|+$8!sr'!uC'!#;[47!#CS#!$ay,!#bk-app_assoc!#<=7!#`J#!t{'1!sIE2!%f9Y6pwdisj!$V?b9!sm%_I!%x}`5e!#f@+!#Cmb>!%TS$!$8v#!$Dzc;!$+g#!x^C6filt!%Bn,!x]/!sA%!v?#!{\J2Fs9!#S%%eq!#{|7!$xW#!$v][A!$+f,!uO1!t903Nat3!#voR!t5-<!#do'!{o#!t0<add!vU7:!&'z$!sb$!#|S<7!$-2$!trV!#7'%@!#4I%!#q,2!$cGP!sh#hasI!#9Kd!}D'!%$c'!uh$8!&-J#!vL#!vP'!v1B!vs$!#PNOTASK_SIZE!#8;\=!sj+_va!$un\Prog?!#=F#protect_r!#WZ%!#=Ke1!v~2!#{D3mod_mul!#@;_<!t3&!$HDP8M!uf&B!uo+budget!$HOW!w['>!ss+!#=ggB!#=g%!s{'!#=i,!}z5B!#:G$!$]0#!#:K$l!#8mY9bump!#w##!x-B!%/&#sp!$&T3!$0F+7!$DH#ct!&7}>eq_dec!#?S[=nodup!$Z$$n!$V{[!ss'm!$$W%_!uz#!#:k`!#w9+!sre;!#7G%!sp_!#7'%!{W,!$:Qj!#vm/!#c2+!#Hz_4!u\b6ENOSYS!#5n[!{n$!%'o%r!%q=i=ev!%VX#_ok!#A`^!%g<%g!$TFb>!$]s-g!uZjB!uZ%!$D4#1!u_/!t#o2!t#o=!#c-&!sznC!sz'!#TF$!t$n!#e+#!#A|$!s|nA!s|#!~u'!z\[3!$9M13!~ef5!sjf!$?+%I!sj_0!sjb<undef_rea!%+4#!}o\!&iP#9!&iP#_!&g`]!%3r$membe!&hLb<!$Kw$cons!%B@\!#U@$c!uM$!%?ac?!t`%pointwi!%Fw&!#TgY5cpath!$K/'!sk`!%uKr!u]$mf!tig!#_E[!&pz/1!slh!tZ&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z3h5LinuxProcessSemanticsfLinuxProcessSem5Statehc5Model89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefeMallocMF_klink2HC~~~~~~l24KLBM79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~q14mled79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5KLink~~~~~~u43KLB37Corelib4Init9Datatypeshi74listq18set_live79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hl24cptr37Corelib4Init5Logichp82eq04Nposhc8m_vmmaps35stdpp9bitvectorbdefinitionshs32bvhi74Nonehi76optionhc6VmMapshc8m_halted79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes~~~~~~igc5mminvhi74prodhc9alloc_tophc6vm_brkhc8vm_limithc7vm_mapshcbvm_noaccesshcbvm_reservedhccvm_start_brk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ir16PStatehl22evhp83andir15ps_fair14ps_mir15ps_sohi74boolhi74truehi74unitq19answer_okq1aevent_posthl26mstateir16ps_brkq19set_brkphu4albrk_bytesu48lbrk_cntq19brk_phaseu49phase_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~jpf5mbind79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~ju58dec_brk079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~kie4NBrkl2fev_step_post_mfq19BPUntriedq16ld_brku48frame_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MSafeP~~~~~~kq45mspechl24EBrkigc6mmsafejpf4mretjpf4msysjpf4mupdir1aset_brk_psju58mmap_lenhi74pairq14went36Stdlib5Lists4Listlje2In46Stdlib6ZArith6BinInt1Zll73addll72lthp82exhp82orq13ehiq13eloq19ld_groupsq18ld_metasll72lehl24PGSZhs37Z_to_bvhi74Somehi73apphcbregion_freeq1dlbrk_pages_okq19ld_brkregll76moduloju57brk_ansju57dec_brkq19BPQueriedhl2bround_up_pgjpf1Mjpf4mgetll73mulq16BPLivehi74conshi75falsehccmkVmMapsFullhcavm_init_sphccvm_mmap_baseq17LEN_MAXq19brk_quietq17lrangesq1aset_groupsq19set_metashl26is_errhl2emmap_answer_okju58mmap_anshi73nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~mv94respq14MAPFju58dec_mmapju5ddec_mmap_nonekie5NMmaphl25EMmaphl29PROT_NONEhl27PROT_RWir19neg_errnoir17ev_stepq15MAPFXq17BPGuardhl27EMunmaphl29EMprotectq19event_pre" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Notation mspec := (MSafeP.mspec mmsafe).
Notation MP := (Monad.M PState).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HC.
Context {HC : HeapCeil}.

(* [comment removed for export] *)
Record KLBM (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKLBM {
  km_minv : mminv mo;
  km_halt : m_halted mo = None;
  km_wf : vmwf (vm_maps (m_vmmaps mo));
  km_nawf : forall e, In e (vm_noaccess (m_vmmaps mo)) -> ehi e <= 2^64;
  (* Weakened with [KLB]'s [kb_resv]/[kb_resv_top] (Spec/KLink.v), which
     [KLB_KLBM] below feeds straight into these two: at 75d69e00
     [State.init_reserved] appends the launch's vDSO/vvar pair to the reserved
     ledger, so neither old shape is true at the launch. *)
  km_resv : exists lo hi, vm_reserved (m_vmmaps mo) = lo ++ hi
      /\ ld_resv L = rband (alloc_top (m_vmmaps mo)) :: map wwZ lo;
  km_top : CEIL_MIN <= alloc_top (m_vmmaps mo) <= CEIL_MAX;
  km_hceil : alloc_top (m_vmmaps mo) = hceil;
  km_resv_top : exists V, (length V <= 2)%nat /\ live_bytes V <= 20 * 4096 /\
      (forall e, In e (vm_reserved (m_vmmaps mo)) ->
         ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo)) \/ In e V);
  km_resv_wf : forall e, In e (vm_reserved (m_vmmaps mo)) -> elo e < ehi e /\ ehi e - elo e <= 2^34;
  km_resv_n : (length (vm_reserved (m_vmmaps mo)) <= 8)%nat;
  km_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_top (m_vmmaps mo);
  km_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_top (m_vmmaps mo)
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  km_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_top (m_vmmaps mo)
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  km_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  km_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_top (m_vmmaps mo)
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  km_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_top (m_vmmaps mo)
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  (* [comment removed for export] *)
  km_live : vm_live_bytes (m_vmmaps mo) = ltotal L;
  km_count : Z.of_nat (length (vm_maps (m_vmmaps mo))) = lcount L;
  (* LPS 727298f3 port: [KLB]'s two vDSO fields (Spec/KLink.v), here too: the MAP_FIXED
     guard and the mprotect of a metadata page must miss the launch's vDSO/vvar pair
     ([MmNodes.mmsafe]), and these two facts are what puts them apart from it. *)
  km_vdso_in : incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo)))
                    (vm_reserved (m_vmmaps mo));
  km_vdso_disj : forall r, In r (vm_reserved (m_vmmaps mo)) ->
      forall e, In e (vm_maps (m_vmmaps mo)) -> edisj e r;
  (* LPS 727298f3 port: [KLB]'s [kb_rdr], the launch's channel reader *)
  km_rdr : m_channel_reader mo = true }.

Ltac kbm_open K :=
  pose proof (km_minv _ _ _ K) as Kminv; pose proof (km_halt _ _ _ K) as Khalt; pose proof (km_wf _ _ _ K) as Kwf; pose proof (km_nawf _ _ _ K) as Knwf;
  pose proof (km_resv _ _ _ K) as Kresv; pose proof (km_top _ _ _ K) as Ktop; pose proof (km_hceil _ _ _ K) as Khc; pose proof (km_resv_top _ _ _ K) as Krtop; pose proof (km_resv_wf _ _ _ K) as Krwf; pose proof (km_resv_n _ _ _ K) as Krn;
  pose proof (km_start _ _ _ K) as Kstart;
  pose proof (km_groups _ _ _ K) as Kgrp; pose proof (km_metas _ _ _ K) as Kmet; pose proof (km_distinct _ _ _ K) as Kdis;
  pose proof (km_brkreg _ _ _ K) as Kbreg; pose proof (km_phase _ _ _ K) as Kph;
  pose proof (km_live _ _ _ K) as Klive; pose proof (km_count _ _ _ K) as Kcnt;
  pose proof (km_vdso_in _ _ _ K) as Kvdi; pose proof (km_vdso_disj _ _ _ K) as Kvdd;
  pose proof (km_rdr _ _ _ K) as Krdr.

(* [comment removed for export] *)
Lemma KLB_KLBM : ltac2:(zQ "50!h9!ka!pa!td!hi1>1L$3>4pbrk$0>2mo$1>0@4$4?2HC^3^2^1@3$2^4^3^2").
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is
   untouched, so no caller changes.  CAUSE, from a farm round
   (the source branch) at this line:
     Anomaly "decompose_lambda_n_decls: not enough declarations."
   [KLB] gained two fields at the revision ([kb_vdso_in], [kb_vdso_disj]; see
   Spec/KLink.v), and the recorded replay eliminates [KLB] with the OLD field
   count.  [KLBM] is [KLB] without [kb_limit] (it carries the two vDSO fields
   too since the LPS 727298f3 port), so the conversion is still one [destruct] and one
   [constructor], and every [KLBM] field is literally a [KLB] field. *)
Proof. intros L pbrk mo K. destruct K; constructor; assumption. Qed.

Lemma KLBM_set_live : ltac2:(zQ "70!pa!hjf!h9!ka!td!hk7!hp0>1L$4>1v@1$1$6>4pbrk$2>2mo$3>0@3$0^4^2^1@3$0@2$5^4^5^3^2").
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is
   untouched, so no caller changes.  CAUSE: [KLBM]'s [km_resv] and
   [km_resv_top] were weakened with [KLB]'s (see Spec/KLink.v), because
   [KLB_KLBM] feeds [KLB]'s fields straight into them and both old shapes are
   false at the launch once [State.init_reserved] appends the vDSO/vvar pair.
   The recorded replay builds the old shapes.
   This one is the mirror of Spec/KLink3.v's [KLB_set_live], which carries the
   same change over [KLB]. *)
Proof. intros L v pbrk mo K. destruct K; constructor; cbn; auto. Qed.

(* [comment removed for export] *)
Lemma KLBM_vm_eq : forall L pbrk mo mo',
  KLBM L pbrk mo -> mminv mo' -> m_halted mo' = None ->
  m_kernel mo' = m_kernel mo ->
  m_channel_reader mo' = m_channel_reader mo ->
  m_vmmaps mo' = m_vmmaps mo ->
  KLBM L pbrk mo'.
(* LPS 727298f3 port: restated as Spec/KLink.v's [KLB_vm_eq] (one more premise,
   [m_kernel mo' = m_kernel mo]), because [KLBM] now carries [KLB]'s two vDSO fields,
   which read [m_kernel]. *)
Proof. intros L pbrk mo mo' K MI HH EK ER E. kbm_open K; constructor; rewrite ?EK, ?ER, ?E; auto. Qed.

Lemma KLBM_vm_eq' : forall L pbrk mo mo',
  KLBM L pbrk mo -> mminv mo' -> m_halted mo' = None ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
  vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
  m_kernel mo' = m_kernel mo ->
  m_channel_reader mo' = m_channel_reader mo ->
  KLBM L pbrk mo'.
(* LPS 727298f3 port: restated as Spec/KLink.v's [KLB_vm_eq'] (premises for [vm_mmap_base],
   [m_kernel] and [m_channel_reader]), for [KLBM]'s vDSO and reader fields. *)
Proof.
  intros L pbrk mo mo' K MI HH H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. kbm_open K.
  assert (Hrdr : m_channel_reader mo' = true) by (rewrite H10; exact Krdr).
  assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps mo')) ->
                   forall e, In e (vm_maps (m_vmmaps mo')) -> edisj e r).
  { intros r Hr e He. rewrite H1 in Hr. rewrite H2 in He. exact (Kvdd r Hr e He). }
  constructor;
    try exact (kb_vdso_in_eq mo mo' H9 H1 H8 H7 Kvdi);
    try exact Hvdd; try exact Hrdr;
    unfold vm_live_bytes in *; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6, ?H7; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ev_step_post_mf : ltac2:(zQ "50!iud!ka!h9!td!iv7>1L$3>1e$4>1G>0$0>0$1P>2s0$0>0$2>0$0>0$1P") := ltac2:(zQ "h30!ivd!hqc!h9!iud!ka!jg4!jgd!jh5!jhe!il4!ji6!jie!pa!jj6!jk2!td!iv7!jkf!jl9\1L$f\1e$h0\1G>0$3>0$4P\2s0$3\1z$2\1s$3\2mo$4@2$0@3$1$8@3$d^7^6^3$a@2$0@3$c@3$e^7^6^3@1$h2^2^1@2$0@2^5^2^1@2$0@3$1$h1@1$6^2@1$6^4@2$0@3$1@2$9$2$2@1$5^2@1$5^4@3$1$b@1$7^2@1$7^4").

Lemma KLBM_rephase : ltac2:(zQ "a0!h9!jm3!hqc!pa!jmf!jnc!ka!jo7!td!jp3>1L$8>2ph$7>4pbrk$0>5pbrk'$0>2mo$6>0@3$3^5^3^1>0@4$9^5^6^3^2>0@3$2$0@1$4@2$1^6^7@1$4^7>0@3$2$0@1$5@2$1^7^8@1$5^8@3$3@2$1^8^9^6^5").
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is
   untouched, so no caller changes.  CAUSE: [KLBM]'s [km_resv] and
   [km_resv_top] were weakened with [KLB]'s (see Spec/KLink.v), because
   [KLB_KLBM] feeds [KLB]'s fields straight into them and both old shapes are
   false at the launch once [State.init_reserved] appends the vDSO/vvar pair.
   The recorded replay builds the old shapes.
   Mirror of Spec/KLink.v's [KLB_rephase], minus the two vDSO bullets that
   record does not have. *)
Proof.
  intros L ph pbrk pbrk' mo K Hph Hb Hc. kbm_open K; constructor;
    try exact Kresv; try exact Krtop; try exact Kvdi; try exact Kvdd; try exact Krdr; cbn; auto.
  - unfold ltotal in *. cbn. rewrite Hb. exact Klive.
  - unfold lcount in *. cbn. rewrite Hc. exact Kcnt.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma ev_brk0_ok_mf : ltac2:(zQ "h80!iud!h9!jie!ivd!hqc!ka!jtc!ki2!kma!pa!kn2!ko4!jo7!kp0!td!kp9!ku2!kub!kv3!kvd!lg5!lgd!jl9!lh5>1L$e>1G>0$0>0$5P>2s0$0>0@1$f^2>0@3$4$c@1$d^4$b@6$h0$h2$0$1\1s$0\2mo$5@2$3@3$4$0^2^5@2$3@3$9^7@1$h6^2^1@2^6^2^1@5$6$0$1$1@4$h4$0$1@1$8Z$7\1r$1@5$6$0$2$1@2$h5$0@1$h7^1\0$2@3$h3$0$1^2@4$a^5@1$h1Z^4^3").
Proof.
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is untouched, so no
   caller changes.  CAUSE: the recorded replay rebuilds [with_vmmaps h' mo] as
   [mkModelOf .. (mkVmState h' lazy mat) ..], and [VmState] carries the run's kernel build
   and vDSO state as two more fields at the revision.  Mirror of Spec/KLink.v's
   [ev_brk0_ok] (written out in this tree), over [KLBM] and with no budget conjunct,
   which [ev_step_post_mf] does not have. *)
  intros L G s0 HG Hph.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ G s mo /\ brk0_answer_ok r = true /\ KLBM (set_brkph (BPQueried r) L) r mo)).
    intros s mo (-> & HK & HGs). split; [cbn; lia|].
    intros rsp mo' evs Hst.
    apply (fun X0__ Q1__ => proj1 (nstep_brk_iff mo _ _ _ _ Q1__) X0__) in Hst; [| lia]. destruct Hst as (-> & -> & ->). rewrite !brk_result_query.
    pose proof (km_minv _ _ _ HK) as MI. rewrite (with_brk_next_eq mo) by exact MI.
    pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz 0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    set (h' := brk_model_next (m_vmmaps mo) (MmNodes.wz 0) (vm_brk (m_vmmaps mo))) in *.
    exists (bv_unsigned (vm_brk (m_vmmaps mo))). split.
    { unfold dec_brk0. cbn. unfold brk_zeros, brk_is_grow. change (w_is0 (MmNodes.wz 0)) with true. cbn. rewrite brk_unmaps_noop. reflexivity. }
    assert (HK' : KLBM L (ps_brk s0) (with_vmmaps h' mo)).
    { eapply KLBM_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (km_halt _ _ _ HK)| ..];
        cbn [m_vmmaps with_vmmaps]; unfold m_vmmaps, with_vmmaps; cbn;
        first [assumption | reflexivity]. }
    pose proof (km_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
    pose proof (km_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Evm : m_vmmaps (with_vmmaps h' mo) = h') by reflexivity.
    pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo))) as R. unfold bv_modulus in R.
    splits.
    - reflexivity.
    - eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
    - unfold brk0_answer_ok. rewrite Ebrk.
      unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - eapply KLBM_rephase; [exact HK'| | unfold lbrk_bytes; cbn; rewrite Hph; reflexivity| unfold lbrk_cnt; cbn; rewrite Hph; reflexivity].
      cbn [phase_inv]. rewrite Evm, E5, E4, Ebrk. splits; auto. }
  intros r. cbn beta. eapply mspec_bind.
  { apply mspec_upd. }
  intros []. apply mspec_ret. intros s mo (s1 & -> & -> & HGs & Hans & HK). unfold ev_step_post_mf.
  cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post Z.eqb ans_cont].
  splits; auto; try (eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs]).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma went_In_bounds_mf : ltac2:(zQ "h90!h9!li3!il4!ivd!lif!lj7!ll1!hqc!hr2!hr8!lmf!ln6!hu0!lnc!lo2!ka!ilc!inc!pa!lo8!loe!lp4!lq0!td!lqb>1L$h7>4pbrk$0>2mo$f>1b$0>1l$0>0@3$h2^5^4^3>0@2$e@3$6@2$2$0$0@4$4$0$0^3^2@1$h5^6@2$d$0\1k$0@3$6@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0^4^3^1@1$h6^7@2$3@2$bZ^4@2$3@2$bZ@1$1^3@2$3@2$h8@2$a^4@1$1^3@1$h0@1$9^5@2$3@3$6@2$2@1$c@1$8#k0@1$c@1$8#k0@2$5^4@1$1^3@1$h1@1$9^5@2$3@3$7$0@1$h4@2$5^4@1$1^3^4@3$7$0@1$h3@2$5^4@1$1^3@2$a^4@1$1^3").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocMF_klink ()) ["HC"] "##mOp'0h01eh11qh22H1h34__p1h44__x1h56__sat3h62Hah74__p2h8!s;%5h94__x2h:2H0h;!s;%2h<!s/%4h=1kh>2H2h?2H4h@2H7hA2H8hB7__arithhC4__ffhD4__p3hE!s_%7hF8__varmaphG5__withH4__x3hI4__x4hJ3H10hK2H9hL3HinhM3H11hN2H3hO2H5hP2H6hQ!sv%6hR1HhS3H12hT3H13hU2HbhV2HchW2HlhX2HmhY1KhZ1Lh[!s[%1h\1bh]1lh^2moh_4pbrki001xp%0p&0p;3p;2p;1p;4p;7p;5p;8p;6g00A:k30KTg00J7j2vTg00]?j1pTg00KQj3?Tg00\_j4WTg00aUj1]Tg00b[S00j27Tg00g]R0k20@Tg00CMj1YTg00Lij1UTg00X7j1GTg00MGj2oTg00W>j2<Tg00GHj15Tg01@gk40JTg03G3k20HTg00Oej1;Tg00^Fj16Tg00D2j1z!s/$Pk10>!t'$\S01j20Tg01HEk708!t}$Bj21Tg00_Mj2ITg00`Oj39Tg02_@j4RTg03H>j5KTg01IUk80!sK$Mdj23Tg00V=j1`!uw$hj1_Tg00H?j1VTg01f\j2tTg01gDj3s!s/$hk20FTg01hIj2|!s/$ck10ETg00N@k10CTg02\^j2gTg01iak10BTg01j?k10A!s0$jj2{Tg02]`j2fTg00FLk10?Tg01l[k20=Tg01m=k20!vW$Fnj3a!s9$ik30;Tg01nHk40:!uP$[k209Tg00YWj1[Tg03Iej2TTg03JNj2bTg00S6j3e!t]$Ck107Tg03K:j4d!s/$Xj3x!tI$8j3yTg03L;k306Tg03MBk405Tg00ZPj2wTg00[ej2q!yW$Wk104Tg01kMj4}Tg032Zk70D!uP$<k603Tg033>k702Tg034mk80GTg03NIk30!wy$maR1P1f1R2f0R3CWp=Qg00n?R4/<3p=2g03O2R5,33p=Pf2R6/02/03p=ug015nR7,<3,02p=r1162%;3'3p=H%Y3#Yp=\f3R81I62%V33?p=81023,06p=4g014jR9,w3=a14p=O%;3,32p=i%V39?62p=k1<27,06!t=$D1<4!tG%E1186/3!s3%J1w39p=nAa124!s8$m1162/33p=>1<37p=Ff6R7f5R:f4R;P8P6P2P3CRCRp=lP:10;!s9&DKp=@1343p==1q39p>00&04;9?7:13861129/33'0'0p=:1q69!tS'C13!tj&jA?86!s1%hA9!s1'^1q!sa$p=~Aa123p=NP1P2g03:<P3C}p=ZP2g00<\R9g038\R<P<g039<R=P3g039\K0Dp=BP2P9P<P<P=P3J03p=SP6!s8+2P3K02p=MP8!s:+!uO$L0Gp=A13!t\&cB01!tS$L!tS&@Z!tS%Xg00n]g00oaB0K;861v11R91Q62%p:3?1v91R>P9P11Q86P3CW%]73?X=1,71+0@g03P?g010WR?#YR@#URA%G?RB#G!s$&URC'oRD,<5%5:R5f7REP7P:P6H0J+0H%;5R5#2%P5%G@!sY%S02#URF,oARG,<53uP01Q:;f8R0#p5?9!t\%7:R5P3CWf9RH#]5?>!tb%%2:RI/r:S03%27RJ%6:RK%5ERL5H7%Y@S04#\#\R@#zS05$0>RM/vMRMP7PKPLC834S06'0P6%pH9?95f:R5PHP0P:PEP7P3K08%2ERL%OE%67RK,1ES07%50RN'iS081IEKRO=kMNS09A95EK34349DJ7%5HRJ#;RN%PN'ES0:1<NG1rLES0;%20P0%6ERPPNPMP0PPPJC8CJ34S0<Q0:%55S0=#;S0>/<G%2HS0?/rHRJ%25RP%n5%6HRNf;RQ#5RR5H5RSPMP5PNPRC8RRf=RT?95N34'm10SRS0@94JP%2QRR%OQS0A%65RS,1QS0Bf<RN#5RU'iRV1IQSRW=kMURUf>RX?9QSS0C3434%5TRY#;RZ#2R[%PZS0D%2NS0E%6QR\=>NZPMPNP\PYC8349DRQS0F%5XS0G#;S0H#P%2TRY%FTR\10Y\S0I%2XS0J%6TR\f?R]#5R^5HXS0KPMPXP\P^C8S0L'034S0M%FXf@R^#2R_%O^%6]R`fARa#5Rb#;Rc5>^RdPMP^P`PbC8RbfCRe?9^`34%2]RfA4_db7D]S0N%naPa%6^RbfBRg#5Rh#;S0OPMPaPbPhC8S0PfDRh?9ab'0CJ'm%OgRi%6aRj%5eS0Q5HgRkPMPgPjQ0QC8RlfERm?9gj'0%2aS0R%FaS0S10kl,Eg3uS0T%6gRl,1eS0U%5hRk'iS0V1IelRn=kMkS0WfFRo?9el34%6eRp%5mRq5HhRrPMPhPpPqC8RqfGRs?9hpS0X%2eS0Y%2hRt?4rq7DeS0ZPMPm%6hRu%5oS0[C8S0\fHRv?9muS0]'0PMPo%6mRw%5sRxC8RyfIRz?9owS0^%2mAHowxS0_/0y,Eo7DmS0`fJRx%6oR{79sS0a%2sS0b%FsS0c'0S0d%2vS0e%6sR|%5zS0f5HvR}PMPvP|Q0fC8R~'0S0g'0S0hQ0bQ0cPHP0CRQ0eQ0gPEP}P~P8P2CRFlWJXAyP3DKWKX@rP3E@WAX?i!s/$@X:_P;E@WPX>YP8DKWOX2[!s/$?X:JP6E@WNW>P8DKb2WLP3O1!#3D$E7!#4z$5!#3?'Q00P!sC&0E!sC%Q!sC%Q0<P3!s@%5H!s@%T5?>PXPTPNPHPQP5!#6q$IQ0A%=2%U?R>/12Q0CA>>63112>$00R9%6NS0<'3PMP3%5^RJ%`3RY&008R_,1]RiPi%_3RiF:X0M,7M[[^1154U7CS54V54R9DP5Q0D,0[S0D1<ZGQ0FQ0DQ0H/<GQ0IQ0J%nXQ0K%=;11>;Q0LA9aX\11>:RZ/33139`PMP3Q0QPY11g_R`P`P!t?1347C\34'mQ0MQ0I%O]%6XR\,1]S0M/iJS0Q%=:S0J1I]\R`=kMJS0FA9g]\A>>73139bPMP3PkPY11e_RkPk!t149CZ\3454f%2cS0A%PcQ0NQ0AQ0O#PQ0RQ0SQ0TQ0R%FgPt%Oh%=511>5Q0X11>QRc!uC%w!uC%fPY11v_RZPZ!t8254q7Cp54rQ0Z%nmPmPuQ0[#;Q0\Q0]11>NRr!sq%{!w\%xRpPY11z_RqPq!u,6cu,jQ!~b%oS0]Q0_Q0^11>T!ta'|PMP3fKRu#5RqPY11x!tf9y9Crw,jNQ0`Q0]PsP{%5vRr#;PM1Is{%VrQ0a11>X!to$%6vRw,39!t'$LRy#5RZPY11u!v}7'0Ch9Cc{,jTCJP}%=XA9uv|11>]!tt$%6zR{!ss'MRk#5RbPY11y_RJPJ!tx4~9Cr|Q0dQ0h'0PM1Izw%VpPyPzPw11>^Rp!sz$xRr!sz'NR|#5R~PY11k!sz7C^!to$w,j]%=^S0h1~p{PMPxP{PqC8S0dA9kx{11>a!t'&uRc!t''ORw#5RJPY11|_R[P[!wl4%2z%FzS0aPxP{%;qQ0dCJ,Ex3uQ0hPM1Iur%VZP|PuPr11>gRg!t2$yRZ!t2'PRx#5PY11w!xv7!u5%pr1~gcRgPMPyPcPb!u-$PwPyPcA>>e3%6kRp!sw'QRr!x~-!u'5C^%2uPyPc%;b!t}&y7DuPM1IkZ%V~PxPkPZA>>h3%6|S0d!t#'RRu!tx%r_RbPb!tx6PMP|PpPJC8RbA9r|pA>>m3%6wRm!sk'SRc#5R[!yg%S0`Q0!~s3%2kP|Pp%;JPbCJ,E|7DkPuPwQ0dA>>o3%6x!ss'TRo!t`%c_R|P|!t`4A9cxmRcA>>s3%6rRs!s_'UR|!s_%o_RoPo!tP4wPxPm%;q!y?$mPqC8!xD$7DwA>>v3%6u!sp'V!sn%|!tO7%2rRi%FrRr'0%2uR|AHus[R_PMPuPsP[C8R['0Rs'0PiPrP]PXCRP|PsPTP_P[PHP8CRFlWTXMcP3DKWSXJbP3E@WMXKg!s/$JWA!s-$KX@}!s/$AW?!#:L&t!#:L$!#:1$WOW2!s-$?W:!#:I'E!#:I$X=1P2P3O2n20010!s#$121!s0%W2P3O1!s@-!s?%!s'$%2;%6;Rt%57R}5H:PMP:PtP}C854I7D;Q01Q03Q06%2KQ08Q09%`O/NE%_OQ07'N'03454LP3Q0;Q0?%60RLQ0>5>HPMPHPLQ0=C834Q01PPQ0@%2S%`W/NQ%_WQ0B'N'094VU54RP3Q0EPTQ0<Q0HPM!s0&GC8CJ!tR$KQ0L%2\Q0QQ0F%``/N]%_`Q0M!tR'fP3Q0P1tACRf%2AR`%=C%2D[R][R\%=ARTg018<RMAsAC2UW6RC%=D\M^6TRD1tAFRR%=F%2G[RU\`RVAsAF2VMX6TRF%=G!sO%WP2g03?H20F4A'|P`eRQO1RSPUP;PQO1RPP]p-0RLg03?nRH$0ERO&0CHRK1g12&0B1R}&0A1Rt1{14Rg1f1?R?'Z,BtRb1St85Mt&0?<R<PbCA20=t=R=P3P6g037\Rcg038<R['|20<36=ac[dB0;142H0:R4bCbFbGX41W31E32%22[^41^3LP3%FvPvP^O3bBb<b;b[b;b5b<-09a%\@#\#\#UR[,1a,<j9cajQ0Y%2lRjQ0VQ0W%`n/NeRc%_nQ0U'NRn'0R_!{_%R|'0P7PjP|PfP\PCPDPRPVPFPWPSPUPPP]g014KR|#[Rj#[RX,T1Rr1T1j1T1|R|'LRj'LRig03QNRu'b=eHOPKP1P11g16RYP6&071R9CdP2P9CdP}PtQ04,f1R9/X?,BtR>1St;5MtP<Pt1Zg9,BtRw1St:!s:%bCACAP=P!v?,X91X3LX7LAc236%26Rx/0;Px[!vO$91^3L^7!{=$a11z[,<{PzP{PEPaO6bBb8b5!v^%b8Q0VPsP6Q0WP_P2PcPn!u}3%U@R@,tARn%=@1oA@Rc#2[R_\`R`AsA@!y|&@%=c!y|%TPSP_PPPUPE!yk$QP]%[XRX#[RM#[,T1Rs1T1MRM/Li'L/bu!vP08P;1g1;!vL$YCdRYP}Pt%YB,f1Ri,X9,Bt1St7R7!vN&Ax1?i1f1BRB'X,B!s:$Pb!vh$StE9Mtw!s2&01{1ARAQ02#z5y1,ZB,Bt!sk$1Xg?,BtQ059y1A,Z?!s?%CACARACA!wD8H1XI!wJ&XDLAc68;A>2;610I01<:G,05Q0J1<:c'0[[Rc\!wb,H1^I!wh&^DLP3%;~R~%P~'ERx%FyR:11y[,<ZR[PZPyP~PkP5PNP^PhPvO<bBbE!x//bQbERG:06elPePlPG!{,4nP`P@P!w\,QP]1T1X/Lj,LM/bu1Lr|,Ls!wO&5eHPKP!w<$AMt>7!w&&i?/XB!v}&1Zgi!s1%!v<L3;A>;26Pc\I!u~<PxP:P[Pk!uj$Z!ujCH05CRFlFlb2WXXVd!#976!s/%W2WU!sD@W!sD=b2b:bRWLWYX]1X\1W^X_1WZo"). Qed.


Lemma KLBM_lbrk_pages_ok : ltac2:(zQ "he0!h9!hqc!hr2!lmf!il4!lqb!jhe!ji6!lr1!ln6!lr9!hu0!ls4!lsc!hue!lif!ivd!lo2!ka!hv8!ilc!hr8!lt3!inc!ip4!pa!lu1!lv1!td!lvd>1L$hc>4pbrk$0>2mo$h2>2lo$0>3len$0>0@3$h9^5^4^3=1h$h3@1$h5^4>0@2$9Z^4>0@2$9Z^4>0@2$5@2$3^6^5@1$h4^3>0@3$1$6@3$h6@3$d@2$4@1$b@1$2#k0@1$b@1$2#k0@1$h8^4@1$h7^4@2$a@1$2#k0^7@2$a@1$2#k0^6$7>0>1b$0>1l$0>0@3$1@1$e@2$4$0$0@1$hb^d@2$c@2$4$0$0@4$f$0$0^2^1@2$h0@3$1$0@2$hd^2$8Z@2$h1@2$5@2$3^3^2^b@2$5@2$3^b^a@2$3^3$8@3$1$6@3$ha^c^9^8$7").
Proof.
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is untouched, so no
   caller changes.  CAUSE: the replay consumes [km_resv] as the old plain equation, and
   [km_resv] is the prefix existential for the vDSO suffix now.  Mirror of Spec/KLink.v's
   [KLB_lbrk_pages_ok] (written out in this tree), with the [km_] accessors and
   [went_In_bounds_mf]. *)
  intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof alloc_ceiling_lt as Hcl. pose proof (alloc_top_lt _ (km_top _ _ _ HK)) as [Htop _]. fold h in Htop.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - destruct (km_resv _ _ _ HK) as (rlo & rhi & Hrlo & Hlr). rewrite Hlr in H. destruct H as [E|H].
    { unfold rband in E. injection E as <- <-. left. exact Hceil. }
    apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    assert (H' : In (e, sz) (vm_reserved h)) by (unfold h; rewrite Hrlo; apply in_or_app; left; exact H).
    pose proof (region_free_InZ _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H'))) as D. rewrite Ulo, Ulen in D. exact D.
  - injection E as -> ->. pose proof (went_In_bounds_mf _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite <- mmap_len_round_up. exact D.
  - injection E as -> ->. pose proof (went_In_bounds_mf _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite <- mmap_len_round_up. exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.


Lemma ev_brk_grow1_ok_mf : ltac2:(zQ "hf0!iud!h9!mg7!jtc!jl9!jie!ivd!hqc!ka!kvd!mh2!kma!pa!kn2!mhd!jo7!kp0!td!kp9!ku2!kub!lr1!mi9!kv3!mj8!mjd!lg5!lgd!lh5!lmf!mk5>1L$h1>1G>0$0>0$8P>2s0$0>3cur$1>0@1$h2^3>0@3$7$f@1$h0^5@1$e^2=3req$1@2$hd@1$h6^3@2$he+2$h5@6$h3$h7$0$1\1s$0\2mo$8@2$6@3$7$0^2^7@2$6@3$c^9@1$4^2^1@2^8^2^1@5$3$0$0$1@1$h9$0\1s$0@5$3$0$2$1@4$ha$0$2@1$b^2@2$a@1$4^1^2\1a$2M2\1a$2@2$h8$0$1^1@5$3$0$5$1@2$hb$0@1$hc^3\0$5@3$9$0$1^4@3$9$0$1@1$4^2@4$d^7@1$h4^1^6^5").
Proof.
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is untouched, so no
   caller changes.  CAUSE: the recorded replay rebuilds [with_vmmaps h' mo] in the
   pre-revision [VmState] shape.  Mirror of Spec/KLink.v's [ev_brk_grow1_ok] (written out
   in this tree), over [KLBM], with no budget conjunct and none of [KLB]'s two vDSO fields. *)
  intros L G s0 cur HG Hph req. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
                match a with
                | BrkGrown => KLBM (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
                | BrkSame => KLBM (set_brkph BPDead L) cur mo
                end)).
    intros s mo (-> & HK & HGs).
    pose proof (km_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
    pose proof (km_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (km_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (km_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    split. { cbn. unfold PGSZ in *. lia. }
    intros rsp mo' evs Hst.
    destruct (nstep_dec_brk' req mo rsp mo' evs MI ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as [-> [[Hdec ->]|(Hdec & -> & Hgo)]].
    - exists BrkSame. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz req)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HK' : KLBM L cur (with_vmmaps h' mo)).
      { rewrite <- Epbrk. eapply KLBM_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (km_halt _ _ _ HK)| ..];
          rewrite ?with_vmmaps_vmmaps; first [assumption | reflexivity]. }
      destruct (lbrk_dead L ltac:(right; eexists; exact Hph)) as [D1 D2].
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + eapply KLBM_rephase; [exact HK'| exact I| exact D1| exact D2].
    - exists BrkGrown. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      apply brk_grow_ok_facts in Hgo; [| lia| unfold PGSZ in *; lia| rewrite Ebrk, Ecur; exact S2| rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      pose proof (brk_model_next_grown (m_vmmaps mo) req ltac:(lia) ltac:(unfold PGSZ in *; lia)
                    ltac:(rewrite Ebrk, Ecur; exact S2)
                    ltac:(rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity))
        as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KLBM_lbrk_pages_ok L (ps_brk s0) mo cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace cur with (bv_unsigned (vm_brk (m_vmmaps mo))) at 1 by exact Ebrk.
        replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo)))) by (f_equal; lia). exact Hrf. }
      assert (Hn : bv_unsigned (MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))) = 2 * PGSZ) by (unfold MmNodes.wz; rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (bv_unsigned_in_range 64 (vm_brk (m_vmmaps mo))) as R0. unfold bv_modulus in R0.
      assert (Hvdi : incl (vdso_reserved (m_kernel (with_vmmaps h' mo)) (vdso_top (m_vmmaps (with_vmmaps h' mo))))
                          (vm_reserved (m_vmmaps (with_vmmaps h' mo)))).
      { apply (kb_vdso_in_eq mo); rewrite ?with_vmmaps_vmmaps;
          first [reflexivity | assumption | exact (km_vdso_in _ _ _ HK)]. }
      assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps (with_vmmaps h' mo))) ->
                       forall e, In e (vm_maps (m_vmmaps (with_vmmaps h' mo))) -> edisj e r).
      { rewrite with_vmmaps_vmmaps, P1, P2. apply kb_vdso_disj_cons; [| exact (km_vdso_disj _ _ _ HK)].
        rewrite Z_to_bv_bv_unsigned in Hrf. exact Hrf. }
      assert (HK' : KLBM (set_brkph (BPGuard cur) L) req (with_vmmaps h' mo)).
      { kbm_open HK. constructor; try exact Kresv; try exact Krtop; try exact Hvdi; try exact Hvdd; try exact Krdr;
          rewrite ?with_vmmaps_vmmaps; cbn [set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
          rewrite ?P1, ?P2, ?P3, ?P4, ?P5, ?P6, ?P7; auto.
        + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; rewrite Z_to_bv_bv_unsigned in Hrf; exact Hrf].
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
        + intros b l Hin. specialize (Kgrp b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
        + intros b l k Hin. specialize (Kmet b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
        + intros b l Hb. rewrite Ereg in Hb. discriminate.
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
          * exists (vm_brk (m_vmmaps mo), MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
          * intros b l Hin. pose proof (went_In_bounds_mf _ _ _ b l HK (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
            rewrite Z_to_bv_bv_unsigned in Hrf.
            pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
          * intros b l k Hin. pose proof (went_In_bounds_mf _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
            rewrite Z_to_bv_bv_unsigned in Hrf.
            pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        + unfold vm_live_bytes in *. subst h'. rewrite P2, live_bytes_cons, Hn, Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg set_brkph ld_groups ld_metas]. rewrite Hph, Ereg. lia.
        + cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg set_brkph ld_groups ld_metas]. rewrite Hph, Ereg. lia. }
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & (HK & HPG)). unfold ev_step_post_mf.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post_mf.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ecur.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma ev_brk_grow2_ok_mf : ltac2:(zQ "i20!h9!iud!mg7!hqc!jtc!jl9!il4!jie!ivd!ka!kvd!lmf!ls4!hue!lif!mh2!kma!pa!kn2!mkc!jo7!kp0!lv1!td!kp9!ku2!kub!lr1!kv3!mj8!mjd!lg5!lgd!lh5>1L$h7>1G>0$1>0$9P>2s0$1>1b$0>1l$0>0@1$h8^4>0@3$3$h4@1$h5^6$h3>0@3$3@1$d@2$6$0$0@1$h6^7@2$c@2$6$0$0@4$e$0$0^4^3=3req$0@2$b@2$b^5^4$hb@6$h9$hc$1$0\1s$1\2mo$9@2$8@3$3$1^2^9@2$8@3$h1^b@1$5^2^1@2^a^2^1@5$4$1$1$0@1$he$1\1s$1@5$4$1$2$0@4$hf$1$2@1$h0^2@2$f@1$5^1^2\1a$2M2\1a$2@2$hd$1$0^1@5$4$1$7$0@2$i0$1@1$i1^3\0$7@3$a$1$0^4@3$a$1$0@1$5^2@4$h2^9@1$ha^1^8^7").
Proof.
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is untouched, so no
   caller changes.  CAUSE: as for [ev_brk_grow1_ok_mf].  Mirror of Spec/KLink.v's
   [ev_brk_grow2_ok] (written out in this tree), over [KLBM], with no budget conjunct and
   none of [KLB]'s two vDSO fields. *)
  intros L G s0 b l HG Hph Ereg req. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
                match a with
                | BrkGrown => KLBM (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
                | BrkSame => KLBM (set_brkph BPDead L) (b + l) mo
                end)).
    intros s mo (-> & HK & HGs).
    pose proof (km_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    pose proof (km_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (km_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (km_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (km_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    split. { cbn. unfold PGSZ in *. lia. }
    intros rsp mo' evs Hst.
    destruct (nstep_dec_brk' req mo rsp mo' evs MI ltac:((first [clear - S3 S1; lia | lia])) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as [-> [[Hdec ->]|(Hdec & -> & Hgo)]].
    - exists BrkSame. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz req)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HK' : KLBM L (b + l) (with_vmmaps h' mo)).
      { rewrite <- Epbrk. eapply KLBM_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (km_halt _ _ _ HK)| ..];
          rewrite ?with_vmmaps_vmmaps; first [assumption | reflexivity]. }
      destruct (lbrk_dead L ltac:(left; unfold brk_quiet; rewrite Hph; exact I)) as [D1 D2].
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + eapply KLBM_rephase; [exact HK'| exact I| exact D1| exact D2].
    - exists BrkGrown. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      apply brk_grow_ok_facts in Hgo; [| (first [clear - S3 S1; lia | lia])| unfold PGSZ in *; lia| rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity| subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      pose proof (brk_model_next_grown (m_vmmaps mo) req ltac:((first [clear - S3 S1; lia | lia])) ltac:(unfold PGSZ in *; lia)
                    ltac:(rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity)
                    ltac:(subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity))
        as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KLBM_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [(first [clear - R4 R3 R1; lia | lia])| unfold PGSZ; lia| subst req; lia| |].
        - replace (b + l) with (bv_unsigned (vm_brk (m_vmmaps mo))) at 1 by exact Ebrk.
          replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo)))) by (f_equal; (first [clear - Ebrk; lia | lia])). exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
      assert (Hn : bv_unsigned (MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))) = PGSZ) by (unfold MmNodes.wz; rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (bv_unsigned_in_range 64 (vm_brk (m_vmmaps mo))) as R0. unfold bv_modulus in R0.
      pose proof (fun b0 l0 H => went_In_bounds_mf _ _ _ b0 l0 HK H) as WB.
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hvdi : incl (vdso_reserved (m_kernel (with_vmmaps h' mo)) (vdso_top (m_vmmaps (with_vmmaps h' mo))))
                          (vm_reserved (m_vmmaps (with_vmmaps h' mo)))).
      { apply (kb_vdso_in_eq mo); rewrite ?with_vmmaps_vmmaps;
          first [reflexivity | assumption | exact (km_vdso_in _ _ _ HK)]. }
      assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps (with_vmmaps h' mo))) ->
                       forall e, In e (vm_maps (m_vmmaps (with_vmmaps h' mo))) -> edisj e r).
      { rewrite with_vmmaps_vmmaps, P1, P2. apply kb_vdso_disj_cons;
          [exact Hrf | exact (km_vdso_disj _ _ _ HK)]. }
      assert (HK' : KLBM (set_brkreg (Some (b, l + PGSZ)) L) req (with_vmmaps h' mo)).
      { kbm_open HK. constructor; try exact Kresv; try exact Krtop; try exact Hvdi; try exact Hvdd; try exact Krdr;
          rewrite ?with_vmmaps_vmmaps; cbn [set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
          rewrite ?P1, ?P2, ?P3, ?P4, ?P5, ?P6, ?P7; auto.
        + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try (first [clear - Kstart Ebrk; lia | lia]); auto.
        + intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
          specialize (Kgrp b0 l0 Hin). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption; try (right; assumption).
          unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
        + intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
          specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
          unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
        + intros b1 l1 E. injection E as <- <-. splits; auto.
          * clear -R3. unfold PGSZ in *; lia.
          * unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
          * clear -Hceil. subst req. lia.
          * intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
            -- destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
            -- exists (vm_brk (m_vmmaps mo), MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. (first [clear - Hge Hx Ebrk; lia | lia]).
        + rewrite Hph. exists b, (l + PGSZ). unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; (first [clear; lia | lia]).
        + unfold vm_live_bytes in *. subst h'. rewrite P2, live_bytes_cons, Hn, Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg set_brkreg ld_groups ld_metas]. rewrite Hph, Ereg. lia.
        + cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg set_brkreg ld_groups ld_metas]. rewrite Hph, Ereg.
          unfold PGSZ in *. replace (l + 4096) with (l + 1 * 4096) by lia. rewrite Z.div_add by lia. lia. }
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & (HK & HPG)). unfold ev_step_post_mf.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK). unfold ev_step_post_mf.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Ecur.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma KLBM_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
  KLBM L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  a mod 4096 = 0 -> 0 < a -> a + n <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  mminv mo' -> m_halted mo' = None -> m_kernel mo' = m_kernel mo ->
  m_channel_reader mo' = m_channel_reader mo ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KLBM (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
  /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false.
(* LPS 727298f3 port: written out (rule 11g), restated with Spec/KLink.v's [KLB_mmap_new]
   [m_kernel] premise now that [KLBM] carries [KLB]'s two vDSO fields; the text is that
   lemma's over [KLBM] (no [kb_limit] here, which no bullet named). *)
Proof.
  intros L pbrk mo mo' a len isnone HK Hq Hlen h n A1 A2 A3 Hrf Hmi' Hh' Ek Er Evm. pose proof alloc_ceiling_lt as Hcl.
  pose proof (alloc_top_lt _ (km_top _ _ _ HK)) as [[Htop0 HtopC] Htop47]. fold h in Htop0, HtopC, Htop47.
  assert (Etop : alloc_top (m_vmmaps mo') = alloc_top h) by (rewrite Evm; apply alloc_top_same_sp).
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds_mf _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; symmetry; apply mmap_len_round_up).
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (km_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ alloc_ceiling)) by lia. cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - destruct (km_resv _ _ _ HK) as (rlo & rhi & Hrlo & Hlr). rewrite Hlr in H. destruct H as [E|H].
        { unfold rband in E. injection E as <- <-. left. exact A3. }
        apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
        assert (H' : In (e, sz) (vm_reserved (m_vmmaps mo))) by (rewrite Hrlo; apply in_or_app; left; exact H).
        pose proof (region_free_InZ _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H'))) as D. rewrite Ua, Un in D. exact D.
      - injection E as -> ->. rewrite <- mmap_len_round_up. apply Dgm. left; exact H.
      - injection E as -> ->. rewrite <- mmap_len_round_up. apply Dgm. right; exists k; exact H.
      - injection E as -> ->. pose proof (km_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  kbm_open HK.
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
            match ld_brk L' with
            | BPUntried => vm_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo') /\ ld_brkreg L' = None
            | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo')) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur /\ pbrk = cur /\ ld_brkreg L' = None
            | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo'))
                /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
                /\ ld_brkreg L' = None /\ cur + 2 * PGSZ <= alloc_top (m_vmmaps mo')
                /\ (exists e, In e (vm_maps (m_vmmaps mo')) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
                /\ (forall b l, In (b, l) (ld_groups L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
                /\ (forall b l k, In (b, l, k) (ld_metas L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
            | BPLive => exists b l, ld_brkreg L' = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = b + l /\ pbrk = b + l
            | BPDead => True
            end).
  { intros L' E1 E2. rewrite E1, E2, Etop, Evm. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  assert (Hlbb : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L -> lbrk_bytes L' = lbrk_bytes L /\ lbrk_cnt L' = lbrk_cnt L).
  { intros L' E1 E2. unfold lbrk_bytes, lbrk_cnt. rewrite E1, E2. split; reflexivity. }
  (* the two vDSO fields: the pair is in a ledger this grant does not touch,
     and the one new mapping is apart from every reserved entry because [Hrf]
     ran [region_free] over [vm_reserved ++ vm_maps] *)
  assert (Hvdi : incl (vdso_reserved (m_kernel mo') (vdso_top (m_vmmaps mo'))) (vm_reserved (m_vmmaps mo'))).
  { apply (kb_vdso_in_eq mo);
      [exact Ek| rewrite Evm; reflexivity| rewrite Evm; reflexivity| exact Etop| exact (km_vdso_in _ _ _ HK)]. }
  assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps mo')) ->
                   forall e, In e (vm_maps (m_vmmaps mo')) -> edisj e r).
  { rewrite Evm. cbn [vm_reserved vm_maps].
    apply kb_vdso_disj_cons; [exact Hrf| exact (km_vdso_disj _ _ _ HK)]. }
  assert (Hrdr : m_channel_reader mo' = true) by (rewrite Er; exact Krdr).
  destruct isnone; constructor;
    first [ exact Kresv
          | exact Krtop
          | exact Hrdr
          | exact Hvdi
          | exact Hvdd
          | apply (Hph' (set_metas _ L)); reflexivity
          | apply (Hph' (set_groups _ L)); reflexivity
          | rewrite ?Etop, ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros e [<-|He]; [rewrite ehi_pair, Ua, Un; lia| apply Knwf; exact He].
  - intros b0 l0 Hin. specialize (Kgrp b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n in Hq2. lia.
    + specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kbreg b0 l0 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - unfold vm_live_bytes in *. rewrite live_bytes_cons, Un, Klive. unfold ltotal. cbn [ld_groups ld_metas set_metas]. rewrite sum_mlen_cons.
    destruct (Hlbb (set_metas ((a, len, 0) :: ld_metas L) L) eq_refl eq_refl) as [-> _]. fold n. lia.
  - cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount. cbn [ld_groups ld_metas set_metas length].
    destruct (Hlbb (set_metas ((a, len, 0) :: ld_metas L) L) eq_refl eq_refl) as [_ ->]. lia.
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
    + specialize (Kgrp b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kbreg b0 l0 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - unfold vm_live_bytes in *. rewrite live_bytes_cons, Un, Klive. unfold ltotal. cbn [ld_groups ld_metas set_groups]. rewrite sum_glen_cons.
    destruct (Hlbb (set_groups ((a, len) :: ld_groups L) L) eq_refl eq_refl) as [-> _]. fold n. lia.
  - cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount. cbn [ld_groups ld_metas set_groups length].
    destruct (Hlbb (set_groups ((a, len) :: ld_groups L) L) eq_refl eq_refl) as [_ ->]. lia.
Qed.


Lemma ev_mmap_core_mf : ltac2:(zQ "i00!h9!iud!mu6!jhe!ivd!mv2!hue!il4!ka!nj5!njd!ln6!hqc!nk4!nl0!nm1!pa!kn2!mp1!mpb!td!kp9!ku2!nma!nn3!no0!kv3!jtc!kvd!lg5!nob!jl9>1L$h4>1G>0$1>0$8P>2s0$1>3len$0>6isnone$3>0@1$h5^4>0@1$h3^6>0@2$4@2$bZ^4@2$b^4$h2=4prot$0M3\6isnone$3$0^4$h8$h9=3dec>3rsp$9@1$6$2M3\6isnone$3>3rsp$9@1$6$2^5@3$e?2HC^6@1$5@2$7$0$0@3$d?2HC^6@1$5@2$7$0$0@6$h6$ha$1$0\1s$1\2mo$8@2$4@3$c$1^2^a@2$4@3$h0^c@1$hf^2^1@2^b^2^1@5$hb$1$2$0@4$hd$1$2@4$fZ^7^2$a^1\1a$2@3$hc$1$0M2\1a$2$0^1\1e$0@1$he^1\1x$0^1@4$h1^a@4$h7Z^7^2$a^9^8").
Proof.
  intros L G s0 len isnone HG Hq Hlen prot dec.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_aligned len) as Hna.
  assert (Hl63 : 0 < len < 2 ^ 63) by (unfold LEN_MAX in Hlen; lia).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMmap 0 len prot MAPF) dec _
             (fun x s mo => s = s0 /\ G s mo /\
                match x with
                | MmErr e => 1 <= e <= 4095 /\ KLBM L (ps_brk s0) mo
                | MmOk a => KLBM (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) (ps_brk s0) mo
                            /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false
                end)).
    intros s mo (-> & HK & HGs). pose proof (km_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (km_top _ _ _ HK)) as [[Htop0 HtopC] Htop47]. pose proof (km_hceil _ _ _ HK) as Khc.
    split. { cbn. left. subst prot. destruct isnone; splits; auto; lia. }
    intros rsp mo' evs Hst.
    assert (Hcase : (rsp = efferr ENOMEM /\ mo' = mo) \/
              exists a, mmap_grant_conds mo a (mmap_len len) /\ dec rsp = Some (MmOk (bv_unsigned a)) /\
                mo' = (if isnone then mmap_na_model mo a (mmap_len len) else mmap_rw_model mo a (mmap_len len))).
    { subst prot dec. destruct isnone.
      - apply (fun X0__ Q1__ => proj1 (nstep_mmap_na_iff mo _ _ _ _ Q1__) X0__) in Hst; [|exact Hl63]. destruct Hst as (_ & [(-> & -> & _)|(a & C & -> & ->)]).
        + left. split; reflexivity.
        + right. exists a. split; [exact C|]. split; [|reflexivity]. destruct C as (C1 & C2 & C3 & C4).
          unfold dec_mmap_none. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite !bv_eqb_refl. cbn [andb].
          rewrite mmap_addr_ok_intro; auto. cbv zeta in C3. change (pgup len) with (mmap_len len) in C3. lia.
      - apply (fun X0__ Q1__ => proj1 (nstep_mmap_rw_iff mo _ _ _ _ Q1__) X0__) in Hst; [|exact Hl63]. destruct Hst as (_ & [(-> & -> & _)|(a & C & _ & -> & ->)]).
        + left. split; reflexivity.
        + right. exists a. split; [exact C|]. split; [|reflexivity]. destruct C as (C1 & C2 & C3 & C4).
          unfold dec_mmap. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite !bv_eqb_refl. cbn [andb].
          rewrite mmap_addr_ok_intro; auto. cbv zeta in C3. change (pgup len) with (mmap_len len) in C3. lia. }
    destruct Hcase as [[-> ->]|(a & (C1 & C2 & C3 & C4) & Hd & Emo')].
    - exists (MmErr ENOMEM). split.
      { subst dec. unfold efferr, eff0. destruct isnone;
          [unfold dec_mmap_none|unfold dec_mmap];
          cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps];
          rewrite errno_of_errno_ret by (unfold ENOMEM; lia); reflexivity. }
      splits; auto; unfold ENOMEM; lia.
    - exists (MmOk (bv_unsigned a)). split; [exact Hd|].
      assert (VO : vm_only mo mo') by (rewrite Emo'; destruct isnone; apply vm_only_with_vmmaps).
      split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact VO| exact HGs]|].
      assert (MI' : mminv mo') by (rewrite Emo'; destruct isnone; apply mminv_with_vmmaps; exact MI).
      assert (HH' : m_halted mo' = None) by (rewrite Emo'; destruct isnone; rewrite m_halted_with_vmmaps; exact (km_halt _ _ _ HK)).
      assert (Evm : m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                   (if isnone then (Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                   (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))).
      { rewrite Emo', Z_to_bv_bv_unsigned. destruct isnone; reflexivity. }
      destruct (KLBM_mmap_new L (ps_brk s0) mo mo' (bv_unsigned a) len isnone HK Hq Hlen
                  ltac:(rewrite page_size_eq in C1; exact C1) C2 C3
                  ltac:(rewrite Z_to_bv_bv_unsigned; exact (proj1 C4)) MI' HH'
                  ltac:(rewrite Emo'; destruct isnone; reflexivity)
                  ltac:(rewrite Emo'; destruct isnone; reflexivity) Evm) as (HK' & Hans & Herr).
      splits; auto. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & Hx). unfold ev_step_post_mf.
  cbn [answer_ok event_post]. change (Z.land MAPF MAP_FIXED =? 0) with true. cbv iota.
  destruct x as [e|a].
  - destruct Hx as [He HK]. unfold mmap_answer_ok. rewrite (is_errno_form_neg e He). cbn [orb].
    rewrite (is_err_neg e He). splits; auto.
  - destruct Hx as (HK & Hans & Herr). rewrite Herr. subst prot. destruct isnone.
    + change (PROT_NONE =? PROT_NONE) with true. cbv iota. splits; auto.
    + change (PROT_RW =? PROT_NONE) with false. cbv iota. splits; auto.
Qed.

Lemma ev_mmap_ok_mf : ltac2:(zQ "h50!h9!iud!ivd!hqc!ka!njd!nma!ln6!lo2!pa!kn2!mp1!mpb!td!kp9!ku2!nn3!no0!kv3!np8!jl9>1L$d>1G>0$1>0$4P>2s0$1>3len$0>4prot$0>0@1$e^4>0@1$c^6>0@2$8@3$3$0^3$h0@3$3$0^3$h1>0@2$2@2$7Z^5@2$7^5$b@6$f$h2$1$0\1s$1\2mo$4@2$2@3$3$1^2^9@2$2@3$9^b@1$h4^2^1@2^a^2^1@2$h3?2HC@4$6Z^6^5$5@4$a^9@4$6Z^6^5$5^8^7").
Proof.
  intros L G s0 len prot HG Hq Hprot Hlen. unfold ev_step.
  change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
  destruct Hprot as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota. apply (ev_mmap_core_mf L G s0 len true HG Hq Hlen).
  - change (PROT_RW =? 0) with false. cbv iota. apply (ev_mmap_core_mf L G s0 len false HG Hq Hlen).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_mmap_fixed_ok_mf : ltac2:(zQ "h50!iud!h9!ivd!hqc!ka!nq3!nma!lr1!nn3!pa!kn2!nqb!jo7!kp0!td!kp9!ku2!mi9!kv3!np8!jl9>1L$e>1G>0$0>0$4P>2s0$0>3cur$1>0@1$f^3>0@3$3$c@1$d^5@1$b^2=1a$1@1$h1^3@6$h0$h2$0$1\1s$0\2mo$4@2$2@3$3$0^2^7@2$2@3$9^9@1$h4^2^1@2^8^2^1@2$h3?2HC@4$6^1$7$8$5@4$a^7@4$6^1$7$8$5^6^5").
(* LPS 727298f3 port: written out (rule 11g); the zQ statement above is untouched.  The
   recorded replay opened [km_resv_top] in its old one-sided form.  Mirror of Spec/KLink2.v's
   [ev_mmap_fixed_ok] over [KLBM], with no budget conjunct (which [ev_step_post_mf] does not
   have): the guard page is inside the tracked mapping the [BPGuard] phase hands over, and
   [km_vdso_disj] keeps every reserved entry apart from it. *)
Proof.
  intros L G s0 cur HG Hph a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
  set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KLBM L' (ps_brk s0) mo /\ x = FxDone)).
    intros s mo (-> & HK & HGs).
    pose proof (km_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
    pose proof (km_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (km_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (km_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
    set (aw := MmNodes.wz a). set (nw := MmNodes.wz PGSZ).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hrf : region_free (vm_reserved (m_vmmaps mo)) aw nw = true).
    { apply (bjhl_region_free_inside _ _ _ e0).
      - intros r Hr. exact (km_vdso_disj _ _ _ HK r Hr e0 He0).
      - rewrite Ua, Ha. exact He0l.
      - rewrite Ua, Un, Ha. unfold PGSZ in *. lia. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    assert (SF : mmsafe (NMmap a PGSZ PROT_NONE MAPFX) mo).
    { cbn. right. change (pgup PGSZ) with PGSZ. fold aw nw. splits; auto;
        first [rewrite Ha, Ecur; exact S2 | unfold PGSZ in *; lia]. }
    split; [exact SF|].
    intros rsp mo' evs Hst.
    apply (nstep_mmap_fixed_iff mo) in Hst; [| exact MI| exact SF]. destruct Hst as (_ & -> & ->).
    change (pgup PGSZ) with PGSZ. fold aw nw.
    exists FxDone. split.
    { unfold dec_mmap_fixed. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. change (mmap_len PGSZ) with PGSZ. fold aw nw.
      subst aw nw. unfold MmNodes.wz. rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    pose proof (fun b0 l0 H => went_In_bounds_mf _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (HK' : KLBM L' (ps_brk s0) (mmap_fx_model mo a PGSZ)).
    { subst L'. unfold mmap_fx_model. fold aw nw.
      kbm_open HK. constructor; try exact Kresv; try exact Krtop; try exact Kvdi; try exact Kvdd; try exact Krdr;
        rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - intros e [<-|He]; [rewrite ehi_pair, Ua, Un; lia|]. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: lia.
      - intros b0 l0 Hin. pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgrp b0 l0 Hin). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + intros z Hz. exists e0. split; [exact He0|]. lia.
      - exists a, (2 * PGSZ). splits; [reflexivity| lia| lia].
      - unfold vm_live_bytes in *. cbn [vm_maps]. rewrite Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]. rewrite Hph. reflexivity.
      - rewrite Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]. rewrite Hph. unfold PGSZ. reflexivity. }
    splits; auto. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & ->). unfold ev_step_post_mf.
  cbn [answer_ok event_post]. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota. fold L'.
  splits; auto. unfold mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma phase_quiet_mf : ltac2:(zQ "h10!hqc!hr8!h9!kp0!hr2!ka!im8!iq2!lv1!td!hu0!hue!il4!pa!jo7!mpb!jp3>1L$9>2L'$9>4pbrk$2>2mo$5>3mo'$5>0@3$d^5^3^2>0@1$f^6>0@3$0$e@1$3^6@1$3^7>0@3$0@1$b@2$c$2$2@1$8^7@1$8^8>0@3$0@1$a@1$4#k0@1$7@1$1^5@1$7@1$1^6>0@3$0@1$a@1$4#k0@1$6@1$1^6@1$6@1$1^7@4$h0@1$3^a^a^9^7").
Proof.
  intros L L' pbrk mo mo' K Hq E1 E2 Es Eb.
  pose proof (km_phase _ _ _ K) as Kph. unfold brk_quiet in Hq.
  unfold phase_inv. rewrite E1, E2, Eb, Es.
  destruct (ld_brk L); try contradiction; try exact Kph; auto.
Qed.

Lemma ev_munmap_ok_mf : ltac2:(zQ "h50!h9!iud!hqc!ivd!ka!nr5!lif!il4!lo2!pa!kn2!mpb!lp4!td!kp9!ku2!mi9!kv3!np8!jl9!ll1>1L$d>1G>0$1>0$4P>2s0$1>1a$0>2l0$0>3len$0>0@1$e^5>0@1$b^7>0@3$h4@2$7$0$0@4$6$0$0^5^4@1$c^8>0@2$8@3$2$0^4^5@3$2$0^4@1$h0^5@6$f$h1$1$0\1s$1\2mo$4@2$3@3$2$1^2^a@2$3@3$9^c@1$h3^2^1@2^b^2^1@2$h2?2HC@2$5^7^5@4$a^a@2$5^7^5^9^8").
Proof.
  intros L G s0 a l0 len HG Hq Hin Hlen. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite <- mmap_len_round_up in Hlen.
  set (L' := set_groups (g_remove a (ld_groups L)) L).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMunmap a len) (dec_munmap a len) _
             (fun x s mo => s = s0 /\ G s mo /\ KLBM L' (ps_brk s0) mo /\ x = RgDone true)).
    intros s mo (-> & HK & HGs).
    pose proof (km_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6). pose proof (km_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (km_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    pose proof (went_In_bounds_mf _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
    set (n := mmap_len l0) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
    assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
    assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
    { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
    destruct Hlen3 as [Hlen1 Hlen2].
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
    assert (Hhas : map_has (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, KInv.wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    assert (Hwent : went a n = (aw, nw)) by (unfold went, KInv.wz; fold aw nw; reflexivity).
    assert (MS : maps_subtract (vm_maps (m_vmmaps mo)) a (a + n) = map_remove (vm_maps (m_vmmaps mo)) aw).
    { rewrite <- Ua, <- Un. apply maps_subtract_exact; [exact (km_wf _ _ _ HK)|]. rewrite <- Hwent. exact A5. }
    assert (SF : mmsafe (NMunmap a len) mo).
    { cbn. change (pgup len) with (mmap_len len). rewrite Hlen2, TASK_SIZE_val. unfold MmNodes.wz. fold aw nw.
      splits; auto; try lia. all: unfold PGSZ in A3; exact A3. }
    split; [exact SF|].
    intros rsp mo' evs Hst.
    apply (nstep_munmap_iff mo) in Hst; [| exact MI| exact SF]. destruct Hst as (_ & -> & ->).
    change (pgup len) with (mmap_len len). rewrite Hlen2. unfold MmNodes.wz. fold aw nw.
    exists (RgDone true). split.
    { unfold dec_munmap. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite Hlen2. fold aw nw.
      rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. rewrite !bv_eqb_refl. reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    pose proof (km_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. pose proof (went_In_bounds_mf _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (km_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + n) by lia.
    assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
    { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. unfold KInv.wz in E. rewrite unsigned_lit, Ua in E by lia. exact E. }
    assert (HK' : KLBM L' (ps_brk s0) (munmap_model mo a n)).
    { unfold munmap_model. unfold MmNodes.wz. fold aw. cbv zeta. rewrite MS.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) (munmap_model mo a n)) by (eapply phase_quiet_mf; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]).
      unfold munmap_model in Hph'. unfold MmNodes.wz in Hph'. fold aw in Hph'. cbv zeta in Hph'. rewrite MS in Hph'.
      subst L'. kbm_open HK.
      assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps mo)) ->
                       forall e, In e (map_remove (vm_maps (m_vmmaps mo)) aw) -> edisj e r)
        by (intros r Hr e He; exact (Kvdd r Hr e (map_remove_In _ _ _ He))).
      constructor; try exact Hph'; try exact Kresv; try exact Krtop; try exact Kvdi; try exact Hvdd; try exact Krdr; rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - apply vmwf_remove. exact Kwf.
      - intros e He. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: lia.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgrp b0 l1 Hin1). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        unfold map_remove. apply filter_In. split; [exact G5|]. destruct (bv_eqb _ aw) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E.
        apply (Kfst b0 l1 Hne ltac:(pose proof (mmap_len_ge l1 G0); lia)). exact E.
      - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kmet b0 l1 k Hin0). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + unfold map_remove. apply filter_In. split; [exact G7|]. destruct (bv_eqb _ aw) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E.
          apply (Kfst b0 l1 Hne ltac:(pose proof (mmap_len_ge l1 G0); lia)). exact E.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + n) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kbreg b0 l1 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
        intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr].
        unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:Efst; [|reflexivity]. exfalso. apply bv_eqb_eq in Efst.
        unfold brk_disj in A6. specialize (A6 b0 l1 E).
        destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
        + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
        + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold KInv.wz in D. fold aw nw in D. rewrite Un in D. lia.
      - unfold vm_live_bytes in *. destruct (live_bytes_remove (vm_maps (m_vmmaps mo)) aw nw Kwf A5) as [-> _]. rewrite Klive, Un.
        unfold ltotal. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !sum_glen_app, sum_glen_cons. fold n.
        unfold lbrk_bytes. cbn [ld_brk ld_brkreg set_groups]. lia.
      - destruct (live_bytes_remove (vm_maps (m_vmmaps mo)) aw nw Kwf A5) as [_ ->].
        assert (LP : (1 <= length (vm_maps (m_vmmaps mo)))%nat) by (destruct (vm_maps (m_vmmaps mo)); [destruct A5| cbn; lia]).
        rewrite Nat2Z.inj_sub, Kcnt by exact LP. unfold lcount. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !app_length. cbn [length].
        unfold lbrk_cnt. cbn [ld_brk ld_brkreg set_groups]. lia. }
    splits; auto. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & ->). unfold ev_step_post_mf.
  cbn [answer_ok event_post]. fold L'.
  splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma ev_mprotect_ok_mf : ltac2:(zQ "h90!h9!iud!lr1!il4!lmf!lif!ivd!ka!ns0!no0!mk5!hqc!pa!kn2!mpb!lq0!td!kp9!ku2!mi9!kv3!np8!jl9!ll1!lqb>1L$h0>1G>0$1>0$7P>2s0$1>1b$0>1l$0>1k$0>0@1$h1^5>0@1$e^7>0@3$h7@2$3@2$3$0$0$0@4$5@2$3$0$0$0@4$5$0$0^5^4^3@1$f^8>0@2$h8@2$a@2$4+2^4$2@1$h3^5=1a$0@2$4^7@2$a@2$4+1^5$2@6$h2$h4$1$0\1s$1\2mo$7@2$6@3$b$1^2^b@2$6@3$c^d@1$h6^2^1@2^c^2^1@2$h5?2HC@3$8^1$2$9@4$d^b@3$8^1$2$9^a^9").
(* LPS 727298f3 port: written out (rule 11g); the zQ statement above is untouched.  The
   revision's mprotect answers [unmodeled] for a range meeting the vDSO/vvar pair, so
   [MmNodes.mmsafe]'s NMprotect case has the vDSO gate the recorded replay does not build.
   Mirror of Spec/KLink2.v's [ev_mprotect_ok] over [KLBM]: the gate from [km_vdso_in] and
   [km_vdso_disj].  With no budget conjunct the budget check may fail; that branch answers
   ENOMEM, leaves the model and the ledger as they were, and [event_post] keeps [L]. *)
Proof.
  intros L G s0 b l k HG Hq Hin Hk2 a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite <- mmap_len_round_up in Hk2.
  set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\
                ((KLBM L' (ps_brk s0) mo /\ x = RgDone true) \/ (KLBM L (ps_brk s0) mo /\ x = RgErr ENOMEM)))).
    intros s mo (-> & HK & HGs). pose proof (km_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (km_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    pose proof (km_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds_mf _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (nb := mmap_len l) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess (m_vmmaps mo)) aw nw = true).
    { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hvd : region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw = true).
    { apply bjhl_vdso_gate_apart; [exact (km_vdso_in _ _ _ HK)|].
      intros r Hr. pose proof (km_vdso_disj _ _ _ HK r Hr (went b nb) A5) as D.
      unfold edisj, elo, ehi in D. unfold elo, ehi in B5, B6. unfold elo, ehi.
      rewrite Ua, Un. destruct D as [D|D]; [right| left]; unfold PGSZ in *; lia. }
    assert (SF : mmsafe (NMprotect a PGSZ PROT_RW) mo).
    { cbn. change (pgup PGSZ) with PGSZ. unfold MmNodes.wz. fold aw nw. splits; auto; try (unfold PGSZ in *; lia). }
    split; [exact SF|].
    intros rsp mo' evs Hst.
    apply (nstep_mprotect_iff mo) in Hst; [| exact SF]. change (pgup PGSZ) with PGSZ in Hst. unfold MmNodes.wz in Hst. fold aw nw in Hst.
    destruct Hst as (_ & [(_ & -> & ->)|(_ & -> & ->)]).
    { exists (RgErr ENOMEM). split.
      { unfold dec_mprotect_rw, dec_mprotect, efferr, eff0.
        cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps].
        rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. }
      split; [reflexivity|]. split; [exact HGs|]. right. split; [exact HK| reflexivity]. }
    exists (RgDone true). split.
    { unfold dec_mprotect_rw, dec_mprotect. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. change (mmap_len PGSZ) with PGSZ. fold aw nw.
      rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. rewrite !bv_eqb_refl. reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    pose proof (km_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds_mf _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (km_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (HK' : KLBM L' (ps_brk s0) (MmNodes.mprotect_model mo a PGSZ)).
    { unfold MmNodes.mprotect_model.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) (MmNodes.mprotect_model mo a PGSZ)) by (eapply phase_quiet_mf; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]).
      unfold MmNodes.mprotect_model in Hph'.
      subst L'. kbm_open HK. constructor; try exact Hph'; try exact Kresv; try exact Krtop; try exact Kvdi; try exact Kvdd; try exact Krdr;
        rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - intros e He. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: unfold PGSZ in *; lia.
      - intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
        specialize (Kmet b1 l1 k0 Hin1). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
        unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
        + assert (Eb0 : b0 = b).
          { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
            pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
          subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
          splits; try assumption; try lia.
          intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b + q * PGSZ) (b + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(right; subst a; clear -Hq1; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
        + splits; try assumption.
          intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          assert (D : b0 + mmap_len l0 <= b \/ b + nb <= b0).
          { destruct (Z.eq_dec b0 b) as [->|Hne].
            { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
            exact (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne). }
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hab Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      - rewrite map_base_bump. exact Kdis.
      - unfold vm_live_bytes in *. rewrite Klive. unfold ltotal. cbn [ld_groups ld_metas set_metas]. rewrite sum_mlen_bump. unfold lbrk_bytes. cbn [ld_brk ld_brkreg set_metas]. reflexivity.
      - rewrite Kcnt. unfold lcount. cbn [ld_groups ld_metas set_metas]. rewrite length_bump. unfold lbrk_cnt. cbn [ld_brk ld_brkreg set_metas]. reflexivity. }
    left. split; [exact HK'| reflexivity]. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & [(HK & ->)|(HK & ->)]); unfold ev_step_post_mf.
  - cbn [answer_ok event_post]. fold L'. unfold mprotect_answer_ok. cbn [Z.eqb orb]. splits; auto.
  - assert (Aok : mprotect_answer_ok (neg_errno ENOMEM) = true) by (vm_compute; reflexivity).
    assert (Ep : ((neg_errno ENOMEM =? 0) || (neg_errno ENOMEM =? TWO64 - ENOSYS))%bool = false) by (vm_compute; reflexivity).
    cbn [answer_ok event_post]. rewrite ?Ep. splits; auto.
    all: try lazymatch goal with
         | |- KLBM (if ?c then _ else _) _ _ => replace c with false by (vm_compute; reflexivity); exact HK
         | |- mprotect_answer_ok _ = true => exact Aok
         end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_step_spec_mf : ltac2:(zQ "f0!iud!ivd!ka!hqc!h9!pa!kn2!nsd!td!kp9!ku2!iv7!kv3!np8!jl9>1L$8>1e$b>1G>0$0>0$2P>2s0$0>0@1$9^2>0@2$7^5^4@6$a$c$0$4\1s$0\2mo$2@2$1@3$3$0^2^5@2$1@3$5^8@1$e^2^1@2^6^2^1@2$d?2HC^5@4$6^6^5^4^3").
Proof.
  intros L e G s0 HG Hpre.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
    + unfold ev_step. cbn [Z.eqb]. apply ev_brk0_ok_mf; assumption.
    + destruct (Z.eqb_spec (round_up_pg cur + 2 * PGSZ) 0) as [E|NE].
      * intros s mo (-> & HK & _). exfalso. pose proof (km_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & _).
        pose proof (km_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow1_ok_mf; assumption.
    + destruct (Z.eqb_spec (b + l + PGSZ) 0) as [E|NE].
      * intros s mo (-> & HK & _). exfalso. pose proof (km_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow2_ok_mf; assumption.
  - destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + apply ev_mmap_ok_mf; assumption.
    + apply ev_mmap_fixed_ok_mf; assumption.
  - destruct Hpre as (Hq & l0 & Hin & Hlen). apply (ev_munmap_ok_mf L G s0 addr l0 len); assumption.
  - destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). apply (ev_mprotect_ok_mf L G s0 b l k); assumption.
Qed.

(* [comment removed for export] *)
Lemma membed_spec_mf {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  frame_ok G -> ctree_ok L t Post ->
  mspec (fun s mo => s = s0 /\ KLBM L (ps_brk s) mo /\ G s mo) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KLBM L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  intros t. induction t as [r|e k IH]; intros Post G L s0 HG Hok.
  - cbn [membed]. apply mspec_ret. intros s mo (-> & HK & HGs). exists L.
    split; [constructor|]. cbn in Hok. splits; auto.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk].
    eapply mspec_bind; [apply (ev_step_spec_mf L e G s0 HG Hpre)|].
    intros z. unfold ev_step_post_mf. apply mspec_pointwise. intros s1 mo1 (Hans & HK1 & HG1 & Hm & Hfa & Hso).
    eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + intros r s mo (L' & Hp & HP & HK & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.
End HC.
