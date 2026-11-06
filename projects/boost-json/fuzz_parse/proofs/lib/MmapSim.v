(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RelSpec SimInv ExitSim PropExec CatSim CatExec SeqExec StreamSim AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MmapSim () := KReplay.lz_vm "#$EyC47Corelib7Classes9Morphisms6Proper!sI5?Relation!sY'Reflexive!sR-Program6Basics4flip!t;?:forall_def!sM?Krespectful_per_oblig!tZ$_1C46Stdlib5Lists4!s+#2hd!su,4Init9Datatypes6lengthC4ELinuxProcessSemantics?!s<22Fs4pa!sV#!sv05Logic6eq_ind!sB88eq_trans!sD87f_equal!sa<ind_r!tsN2Fs!ui<3app!sq;5Riscv7Prelude5bvmap!tEK5State7PipeBufI!tM;4list00K!xO,Numbers7BinNums8positive02!sKG1!sK=1N02I45stdpp9bitvector;defini!yF#s2bv00!ty<6op!sL#00!uyK>!v]$!sE+:fetch_wordK!t2C1I!xj72eq!tL\8is_ecall!wQ=prod!t-=!x{&DecodeC:d!s-$_anyK!sW@5Instr5i!s+#07!wd>Z!xO/!ti81C79OSSVerify6Proofs:boost_json:fuzz_parse3lib8PropExec4getrC13~~~C!xm@9bv_signed!t7Y6v_addi!t9%!uB<3nat02!x4[store_ok!sfZ@!z<#_to_le_bytesI!snY>machine_result00!waZmkst!wa'!tWX4step!tKP7Cat!wt$w!uw$!wt'!u}h!z`Q7Seq!tX#7!u:#_sb!zbG;bv_un!zd&!sP@7Z!xV#bvK!#6y@1!sFB2!uIXEN!y{/_1_small!uW%!z1K<MemImageType7Segmen!#8yI3!#5;<bool!sk/!sF82I!#5&L!#9#,!#5&50!#5tGmsize!wQ>!#3:#1!u'B1!~&Z=!{''state!v:4!#9q+1c!xyPMmapSim;!{D&_any!{H&5!#Bt%6ZArith6BinInt1Z2lt!sB<3add!s_>e!#;w8or!#4IRAllocSim8zmem_ou!#4MQ!#A,$8m_haltedI!s]P5Model!#=yL!s\%9m_vm_lazy!s^Q4m_fd!uNTvmmaps!s]Q;vm_reserve!t?R7vm_!t>U:map_remove!twUnoac!s;#!s`Q=!tt#_subtract!sbQ<vm!}2#rt_brk!saQ6vm!s[U8!yE#imi!tuV!xk#_bas!vvR:vm_init_spK!uVQVmMaps01!t>QA!{y$materialized!tEQ7Vm!s-$!tFS4m_io!x0Rm_fsys!s[Tproc!s[Q5!xd$!t7Ttime!v\Q!#4u%!vZRBpage_outside_range!#Tm66filter!#:%W<mun!{##m!tn#!#7~$!snX8plac!#HT#!#8j%!#=-:andb!#Tt73iff!#:P73an!#NB#!#?9'!#X>3Diff_impl_subr!#Ym&!vH'4Bool!s'$=!tK#_true_if!#Y8?:!#Y8+!sM?@!t>-_ref!sS@F!sS1!t-GIr!#[z&_!s0,proxy!s\5>!s\+_Prop@and!u\#_m!s=&!z9Q9alloc_top!#?e<eqb!sC<6eqb_eq!sc=lt!sc>ltb_!#A/>le!sc?eb_leK!ya<1!sa=modul!#4\Q;reg!x@#free!xm@!x00per!x7;!sY,B!yH/p!#bF%!x4P!#3G#size!#Vd?1!tS-!#bp1!|d#!#H3<unit!#H3L!#:^0!~06!#da2=!z~#!#de5!x@-5proj2!#<iQiv_overlap!#4V<negb!#3I6!s>#!#3I,!sG4>!#3j#fals!sH%!{J@geK!sh'9micromega6VarMap1t02!sD@3I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr!tX8!sI23K!t?L1!sQ65Tauto8G!sJ'4!#aGC2!slF8C!sJ<B!sJ&!sH6:Z!u&+=Z!sT$Check!}4#!w8;4f!#iO#!sq?C!sq0_sound!#Pg8or!#a/3!s@,1I!t4@;!y~%!#=N#!|r#!uu:5eKindI!~8A0!w$<4kind!x68!xa13Op203!}UK!#T416ms_gpr!#3eKMonad7outcome00!#@VW>!#AF%args!#@\:!#9B%no!#JLQ?!#74#r!xf#_up_Z!toX=!sk0!#T8V7!uV#ha!#H-K3Run9sys_inpu!uiNpecs<syscall_spec!ufX:!wW&eff!#bvP!x}2!#HIQ6in!xr#C6!vBJSys2Mm4!u'#;!u$&!ui#!#=t>?eq!#>HKM!#uq#_co_!#uB#v!#Fl$!#CaX8in_sysno!#cMPExitSimB!sd'_!y%,!zC%!stPRel!y7#@!y6/_215!srV!#jY':bv_eqb_neq!#_<&!x+M7S!tX%5w_is0!uCXD!zi'xact_!z7&!uGV9StreamSimA!zD%1!w2a!x$&!ss&0!ss48!ssN3Lib2Nd:and_elimF4!#i8P!zA%=!w3&Effect!#`lSTASK_SIZE!#b&Qev!#jM#!#EOD>iff_T!}%#!#j[#!#4gWA!x|&!xv&_si!|6^6Ok_inj!#5X_2!tHX<Un!#Ur#ed_Ok!#h{A!#N9#gt!#F4?1!#GZ5<!#GZ,!#WmX6unfi!#p\&!#?|H5K!#;FM6config!#LZL!s[#5sstep!$$,[>ms_svc_pending!#=EN?mi_account_!tR#!uaO!#vy$to!#O|-!#A,,6eq_sym!sB89F!#Le$nd!#y3i2!snj3!#3gPG!#:4&e!#4N#_!#it$e!#bpQJ!#eC,!#_F$!so+!{JXD!#`9-_no!#oF$!#D/UR!tg=!s}+!swP;with!#om%!#FSX!#6&&k_inv!#:5f3!v7W4m_f!xSR8m_kill!#jlR!#:%%3!vLXC!xw0!#vT$!#8hQ!tS/4!uhQI!uh'_of_!#w{&_none!uC`no_u!#9`&!x&Q3Run<apply!}f&!s_O@advance_past_svc!#8/N!#8d&0I!#6^V0!#7<W2!#jB75!#6x#!$<X3!sC%4Tru!$$S:!sB%1".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq37Corelib4Init9Datatypesla6option01Z3h5LinuxProcessSemantics5Riscv5Instrne5instr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~qa4getrqa6v_addila4Somela4boolla4prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshgadmachine_stateqa4mksthf9bv_signedla4consla5falsela4listla3nilla4pairla4true3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehof7Segmenthga9MachineOkhgaafetch_wordhga8is_ecallhgaemachine_resulthga4stephga8store_ok3h5LinuxProcessSemantics5Riscv7DecodeCihcadecode_anyne3SZ1ne5Store3h5LinuxProcessSemantics5Riscv7Preludeile5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~iod6wbyteshf7Z_to_bvhfbbv_unsigned69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AllocSim~~~~~~iu94zmemk12or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim4FPX1~~~~~~jj15zfill46Stdlib6ZArith6BinInt1Zjn93addjn92lejn92lt3h5LinuxProcessSemanticsfLinuxProcessSem5Statejq45Modeljq48m_vmmapsjq4amap_removejq4dmaps_subtractjq4cmkVmMapsFulljq46vm_brkjq4avm_init_spjq48vm_limitjq47vm_mapsjq4cvm_mmap_basejq4bvm_noaccessjq4bvm_reservedjq4cvm_start_brk5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapko3h3with_mmap_destroyedjq4bwith_vmmapsjq4fpage_round_up_Zjq46VmMapsla4andbla3appjq49alloc_topjq49page_sizejq4bregion_freejn93eqbjn93lebjn93ltbjn96modulojq4fvm_backing_usedjq48m_haltedjj1cmunmap_modeljq49m_vm_lazyk13andjj18place_okjq4estack_max_sizehga6ms_gpr3h5LinuxProcessSemanticsfLinuxProcessSem3Runlra9sys_inputjq46in_argk13notjq49TASK_SIZEjq47map_hasjj1dpage_round_upjq4dSyscallEffectla3natjq47MemCopyjq49mkEffectU3h5LinuxProcessSemanticsfLinuxProcessSem5Monadmlb7outcomek13iffmlb2Ok3h5LinuxProcessSemanticsfLinuxProcessSem5Specsmq0csyscall_specjq45eventjj1emunmap_args_okjj1amunmap_effmlb9Unmodeledla4Nonejj16unfilllra5mkCfglra7step_tohgaems_svc_pendinglra5SNextlrah0advance_past_svclracapply_effectlra5sstep69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~no2emunmap_args_okno2amunmap_effno2cmunmap_modelno2dpage_round_up" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
Lemma step_sb_any : ltac2:(zQ "i21!h9!jc!l5!n2!nb!q2!u5!uc!v5!vc!hg3!hk1!hl2!hl9!hm5!hmc!hn4!hnb!ho1!ho8!hs4!hsf!htc!hua!hv6!ig8!ih0!ik2!il0!il6!io4!is7!it1!itb&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$h0$h4>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>0@3$2@1$3@1$1@1$0#i0@2$h6^9^7@2$8@1$1@1$0#i0^4>0@3$2$9@1$h7^5$f>0@3$2@1$3@2$a$5$4@1$hb^6@2$8@2$a$5$4@4$h2$5$4@4$hd$hc^5^4^3+4>0@3$2$9@4$ha^c^9@2$7@2$6^b^6@2$d@1$0#c^4N1$h3@3$2@1$h8$b@2$h9^d@5$c?2fx^c^b^a^9@2$h5$b@5$c?2fx^c@2$7^b+4@3$hf^a@2$7@2$6^c^7@2$d@1$0#c^5@3$e@1$1@1$0#8@2$i0@1$0#8@2$i1@1$0#k0@2$6^c^6@1$h1@1$1@1$0#8^9").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##47h07Hdecodeh16Hecallh26Hfetchh33Hokh43immh51lh63memh72pch84regsh93romh:3rs1h;3rs2h<4segsh=1wp;1p;2p;3p;4p;5p;>p;6p-1R0p10000p4p710p9P!s6%S!s611?R1!s8,P!s2$2!s3/31!sS-]!sc12D!s613<!s6&8!s6&!t;'8p10043p4p70R0g004c!tE'R2!sT'5?!s8&3!s8+]!t]&R4!s9'6:!sK&!s{&6X!s{%5P2p8P5P3!s+$4!s+$0p8P5p1007F!tV'g007cR5!s}'6!s\$6!s\$6!s\$6P!t#&8O!t#%!sI:g009Ej1;Tg009ej10Tg00:Jj17!s/$oj13Tg00;Mj12TP5j2LTg00<0j15!s/$Rj2CTg00=Tj28Tg00>6j31!s/$Pj1?Tg00?Pj2=Tg00@0j1<!s/$aj4QTg00AMj1P!s/$kj4OTg00BKj24Tg00CLj29Tg00D4j26Tg00E7j1I!s/$Vj4HTg00FVj2ETg00G^j1BTg00Hfj5:Tg00Igj2DTg00Jcj3ATg00Kej2FTg00Lml>GTg00N0j2@!s/$Zj2JTg00O@j1K!s/$`j3>Tg00P@j1MTP1j6NTg00QQ#;g00RPR1#0R5#7#3R0%05R5#0R6#0#0R4#0#3R3#2R2'L%36R6#2R7#5\2R8%34#2R4%20R0%71#0!sR$1#2%54f8R9f6R:'Cf3R;,8431g00S5R4f4R<#?g00SU!s:$T5R=g00TaR>'=R?#5f5R@#<P=P>g00U?P<P;f2R>CQ%P5R5CO,8?31f;R?P9f:R=/4@191;'6g00Uk#IRACHg00VJ514%;7R414?@RB,EAg00VjRA#Bf=p,2fxRCf<RDP?P=f9RED:'DPCPD16?5f7R5,4D191@'6f0R15A=PED:,FA31X54PCP!s^$PEP9P5P:P@P<P;P>f1P1M>G1@3B,J6%K75>7%MBENW3W0W1W2W4X;0W:W=X98W6X72W8W<o"). Qed.

(* [comment removed for export] *)
Lemma step_sb_at : ltac2:(zQ "i21!h9!jc!l5!n2!nb!q2!v5!vc!hg3!hk1!u5!hl2!uc!hm5!hmc!hn4!hnb!ho1!ho8!hs4!hsf!htc!hua!hv6!ig8!ih0!ik2!il0!il6!io4!is7!it1!hl9!itb&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$f$h3>4regs@2$hd@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1a@1$1@1$0#k0>1v@1$1@1$0#k0>1b@1$1@1$0#8>0@3$2@1$3@1$1@1$0#i0@2$h5^c^a@2$6@1$1@1$0#i0^7>0@3$2$7@1$h6^8$e>0@3$2@1$3@2$8$5$4@1$ha^9@2$6@2$8$5$4@4$h1$5$4@4$hc$hb^8^7^6+4>0@3$2@1$1@1$0#k0@2$c@2$a^e^9@2$i0@1$0#c^7^6>0@3$2@1$1@1$0#k0@2$a^f^9^6>0@3$2@1$1@1$0#8@2$hf@1$0#8@2$i1@1$0#k0^7^6>0@3$2$7@4$h9^h2^f^9N1$h2@3$2@1$h7$9@2$h8^h3@5$b?2fx^h2^h1^h0^f@2$h4$9@5$b?2fx^h2@2$c^h1+4@3$he^h0^a@3$d@1$1@1$0#8^8@1$h0@1$1@1$0#8^f").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##3Ch01bh12Hah22Hbh32Hdh42Heh52Hfh63Hokh72Hvh81ah93immh:1mh;3memh<2pch=4regsh>3romh?3rs1h@3rs2hA4segshB1vhC1wp;1p;2p;3p;4p;5p;6p;=g009Ej1QTg009ej11Tg00:Jj1?!s/$oj17Tg00;Mj1;Tg007cj2KTg00<0j1=!s/$Rj2ITg00=Tj2>Tg00>6j30!s/$Pj1ETg00?Pj2CTg00@0j1B!s/$aj4PTg00AMj1O!s/$kj4NTg00BKj28Tg00CLj2ATg00D4j2<Tg00N0j29!s/$Zj26Tg00E7j1J!s/$Vj4@Tg00G^j1HTg00O@j1G!s/$`j34Tg00Jcj33Tg00Hfj52Tg00X1j2FTg006:j6:Tg00Igj2D!sA$Kl=LTg00Kej2MTg00VjR0f0R1'Mp=5g00QQ#Qg00RPR2#1R3#?#7R4%13R3#1R5#1#1R6#1#7R7#;R8'K%75R5#;R9#=\8R:%76#;R6%;4R4%?2#1!sR$2#;%=6f;R;f9R<'If6R=,>630g00S5R6f7R>#Eg00SU!s:$T5R?g00TaR@'CRA#=f8RB#BP?P@g00U?P>P=f5R@CP%O3R3CN,>A30f=RA/8B1A2='<=08@f>R?/8B=08@197=,65=09@fARCP?PBg00Uk#JRDC@g00VJRE506%H0R0p,2fxRFPCf@RG/<3RHf?RIf<RJ,8Cf:RK,A2'<R218C;RL,97,65%G9RM54933P?D2#5PFfBRN1<C3R3A49BM93GKPID2#5RO9001X:0P8P<PFPNP318NJ!sn%=49M93G1!sQ%=00OX08P8PB!sO&971!sL,K!sL19P>!sL%A491!sF49PFPCPHA49>M93I<!tv%,F0197B,65f1E:PLf2E:P2f3RLE:!sW$GPIP?D2,DNPN!s5'PAPJP;PKP=P@f4P8P<fCPGP1PDC@=06EX08P1P2PLE:M=LE:W6W2W7W1W3W4W5X09XB8X88W9X@4W?WCX>:W;X<8W=WAo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zfill : ltac2:(zQ "31!h9!jc!n2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m~0~0") := ltac2:(zQ "40!h9!jc!n2!ji4\1a@1$1@1$0#k0\1n@1$1@1$0#k0\1m>0@1$1@1$0#k0@1$2@1$1@1$0#8@3$3^1^3^2").

Lemma zfill_out : ltac2:(zQ "a0!h9!jc!itb!n2!l5!jic!jn0!jp1!jp8!jpe>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1x@1$1@1$0#k0>0@2$5@2$9@2$2@1$0#k0^1@2$2@1$0#k0^4@2$8@2$7@2$2@1$0#k0^4@2$2@1$0#k0^3@2$2@1$0#k0^1@3$4@1$3@1$1@1$0#8@4$6^5^4^3^2@1^3^2").
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["FPX1"] "h02Hxh11ah21mh31nh41xp;1p;2p;5g009ej10Tg00:oj13Tg00;Mj12Tg00<0j14Tg00N0j21Tg00YRj29Tg00Ynj28Tg00ZKj25Tg00Zgj26Tg00[Aj57Tg00RP#0#0#0R0#0#0#0#3R1#2R2%30#2#4\2f0R0,11R3f3R4,11R5'9f2R6,11,85/53'6P6f4P4f1P0D7W0X42W2X32W1o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model : ltac2:(zQ "30!h9!jt2!jc>4addr@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "h20!jtb!h9!itb!jc!jt2!ju7!jv5!kg6!kh6!ki0!kie!kja!kk5!kl5!km4!kn3!kr7!jp1\4addr@1$3@1$1#k0\1n@1$3@1$1#k0\1m$4@4$h0^3^2@8$7@1$e@1$0^1@2$5@1$b@1$0^1^3@3$6@1$d@1$0^1@2$2@1$1#k0^3@2$h1@2$2@1$1#k0^3@2$2@1$1#k0^2@1$f@1$0^1@1$8@1$0^1@1$a@1$0^1@1$c@1$0^1@1$9@1$0^1^1").

Definition mmap_model : ltac2:(zQ "30!h9!jt2!jc>1a@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "h10!jtb!h9!jc!hm5!ho1!hg3!jt2!kg6!kh6!ki0!kie!kja!kk5!kl5!km4!kn3!ksf\1a@1$2@1$1#k0\1n@1$2@1$1#k0\1m$6@2$h0@8$7@1$e@1$0^1@3$3@2$5@1$2@1$1#k0@1$2@1$1#k0@4$4@1$2@1$1#k0@1$2@1$1#k0^3^2@1$b@1$0^1@1$d@1$0^1@1$f@1$0^1@1$8@1$0^1@1$a@1$0^1@1$c@1$0^1@1$9@1$0^1^1").

(* [comment removed for export] *)
Definition page_round_up : ltac2:(zQ "20!h9!jc>3len@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!kte!it1!jc!itb\3len@1$3@1$0#k0@2$2@1$0#k0@1$1@2$4@1$0#k0^1").

(* [comment removed for export] *)
Definition place_ok : ltac2:(zQ "50!vc!h9!nb!kv1!jc>1h$3>1a@1$4@1$1#k0>1n$2$0") := ltac2:(zQ "h30!h9!kvb!jc!itb!lg2!hg3!nb!kv1!lg8!lh5!li2!kja!km4!jp1!lj1!lj8!ljf!lk6!it1\1h$7\1a@1$2@1$0#k0\1n$6@2$1@2$1@2$1@2$e@2$h1@2$3@1$0#k0^2$9Z@2$h0Z@2$3@1$0#k0^2@2$f@2$d@2$3@1$0#k0^2^1@1$8^3@3$a@3$4@2$5@1$2@1$0#k0@1$2@1$0#k0@1$c^3@1$b^3^2@2$h2@1$0#k0^1").

(* [comment removed for export] *)
Definition grant_ok : ltac2:(zQ "50!h9!jc!vc!nb!jt2>4hint@1$1@1$0#k0>1m$4>1a@1$1@1$0#k0>1n$3$2") := ltac2:(zQ "h60!h9!kvb!jtb!jc!itb!jp1!lj8!lg2!hg3!nb!jt2!lg8!lh5!li2!ll0!kie!kja!km4!lj1!ljf!lk6!it1\4hint@1$3@1$0#k0\1m$a\1a@1$3@1$0#k0\1n$9@2$1@2$1@2$1@2$1@2$h2@2$h4@2$4@1$0#k0^2$cZ@2$h3Z@2$4@1$0#k0^2@2$6@2$5@2$4@1$0#k0^2^1@1$b@1$2^3@3$d@3$7@2$8@1$3@1$0#k0@1$3@1$0#k0@1$h1@1$2^3@1$h0@1$2^3^2@2$h5@1$0#k0^1@2$6@2$5@1$e^3^1@1$f@1$2^3").

Lemma munmap_model_halted : ltac2:(zQ "70!h9!jc!lm3!n2!l5!jt2!lmf>4addr@1$1@1$0#k0>1n@1$1@1$0#k0>1m$5@3$4@1$3@1$1@1$0#k0@1$2@3$6^3^2^1@1$2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["FPX1"] "h04addrh11mh21np;1p;2g009ej10Tg00:oj15Tg00;Mj12Tg00<0j11Tg00\Fj14Tg00X1j23Tg00RP#0#0#0#0#0#0#5#2R0g00]=%10f0#4'3W1X20W0o"). Qed.
Lemma munmap_model_no_lazy : ltac2:(zQ "93!h9!jc!hg3!hn4!hnb!l5!lnf!jt2!lmf&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0&@1$4~0>4addr@1$1@1$0#k0>1n@1$1@1$0#k0>1m$7>0@3$5~1@1$6^1~2@3$5~1@1$6@3$8^4^3^2~2").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##/;h05Hlazyh14addrh21lh31mh41np;1p;2p;3p;8p;7p;6g009ej11Tg00:oj1STg00;Mj1OTg00?Pj2NTg009Ej1RTg00^3j10Tg00O@j1QTg00>6j33!sA$kj15Tg00_^j16Tg00`Uj1ITg00aOj1ETg00bEj2?Tg00c>j1KTg00N0j2>Tg00Ynj2JTg00d8j3:Tg00e4j1H!s/$oj1GTg00fdj1FTg00g[j1DTg00hVj1CTg00iOj8BTg00jFj1<Tg00kFj39Tg00l>j17Tg00m1j14!s/$fj1=Tg00n[j1;Tg00oOj12Tg010Dj78Tg011:j2@Tg012;j3ATg00X1j2MTg006:j6L!sA$Vj3PTg00RP#1!s$-SR0#OR1g00]=1N11R2#RR3f0R4#0%Q2R233P3P2f2R5#5%65R6#I%E6f4R7'?%K61>07R7f3R8,>0R9,J7R:3:%H6%G6%F6%D6%C6GB%<5794%75%45%=5%;5%25F8R6#5%66%06?:7:1@7:%<65A139%76%46%=6%;6%26F8#0=332X231M32f1R6#0R:P4EL%56%66R4#I%E4/?8%K41>05,J9R07:9%H4%G4%F4%D4%C4GB%<679:!t-4R:#5%6:%0:?:901@90%<:!tY&:%4:%=:%;:%2:!tY'eAP856!s2&W0W3X41W1o"). Qed.

(* [comment removed for export] *)
Lemma place_ok_unpack : ltac2:(zQ "h60!h9!loc!l5!jc!itb!vc!ho8!nb!lg2!hg3!kv1!lg8!lh5!li2!kja!km4!lp2!jp1!jp8!jpe!lk6!it1>1h$a>1a@1$3@1$0#k0>1n$7>0@3$2$5@3$h0^3^2^1$6@2$1@3$2$7@2$h4@2$4@1$0#k0^3$cZ@2$1@2$h3Z@2$4@1$0#k0^3@2$1@2$h2@2$h1@2$4@1$0#k0^3^2@1$b^4@3$2$5@3$d@3$8@2$9@1$3@1$0#k0@1$3@1$0#k0@1$f^4@1$e^4^3@2$h5@1$0#k0^2$6").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##<~h01Hh11nh21mh35lemmah42H1h52H2h62H3h71Ah81Bh92H4h:1ah;1hp;1p;3p;2p;4p;8p;6p;=g009ej1ATg00:oj1aTg00;Mj1ZTg013^j3VTg00N0j21Tg014bj27Tg00?Pj2UTg00`Uj1=Tg00aOj13!sS$Zj25Tg015@R0j2K!s1$YR1j22Tg0164R2j3\!s1$ej2JTg017Fj4G!s/$mj2[Tg018Zj8OTg019Mj3XTg01:CR3j6WTg00YRj28!s/$nj2BTg01;5j1>Tg00ZKj2;!s8$mj2FTg00>6j3<Tg01<Jj2S!s/$jj2MTg01=Gj2`!s/$gj2HTg01>Dj2_!s/$dj4LTg01??j2RTg007Fj3Q!s8$_j3PTg01@Yj4^Tg01ALl=]Tg00S5R4f0R5g00VJR63<p=0g01B;R7,R5g01C3R8'Fp=91M85p=6f2R9f1R:'B%>5'Hp=:f4R;f3R<;Q9?P:5p=EA<456,2:p=4p-0R=P=P0P0P5P0g01CQR>P2GOp=Y%=:=Q95p=@AP9:5=<46p=?!sT$:P5C^p=IP5P:P1P3P9g01CoP<P;f5R3f6R6f7R4f8R2f9R?M=]p=N1R57p=Dg00TaR7?<58p=C1F58p=Tg01DOg00RP#A!s$-aR@#ZRAAV9:5#011@9RB#9%6B'7A:B:<'7RB1UAARA%=<%3<P915@:DERC'7#0%0B/4CRD'K11@<RE#9%6E'7RFA:E9;RE'7RGPA%=;%3;P<15@9DERH!s`%GRG%0HRH'2;\5W31JBCP5O2PD%0F/4ERD,KGP=^8=RG^7=RCP=P=\=P0P!vm&CGRBCGRIP=PG!s<+>CGR>CGRJ!s<&01[=0RGPBP>%YGGORG11@;R>#9RB%6>RK'7RLA:><3R>!te%LRL%0>R>'2P5%339@A315@<7?;RMPMg01EF9X=0R=/IMM:NW31JFEP5O212DH!v-$KRD,KLPCPIPJPG11@3RG#9RJ%6GRI'7#0RCA:G;6#0RG'2%0J/4IRI/2GRJ!s[$5PGPG1I=GEW%369@A615@;7?3R!s>&!tE&BK!tE&>/2MP1!t;&6RG#D#C188G1BG3%>4';PA%=4%34P615@3DE'4'2'2P511@4RG#9#0%6G'4A:G62'4P111@2!s>14?#0f:RG%3G5@A15@27??11@GR2#DR4!t>$21B2?f;RJ#>!tA%J%3JPG15@?!tA'[P5%T4#0%!t6+JR2!t6%2#0f<R2,1@f=R47:J#0f>RJ%3J!t?+4!sV&D!t=+4f?R?!t='?%3?PJ15@4!t=+[!uZ%!t0+11@?f@R2!t,%A!t,-?7?2P11F:5#0A<79:[R2A<7:51F9:#0R?[A<7<9\?1S:5P:n20010!s#$12!s-%0X27X17P2^27^17P5fB,1@#DR2P8P;O3%C2P11M!|u$8!t-$18:51M!t,&18!t+$`!t+KP8fD,1@R2P3O31882P11H!t'$;9:[R11;:51H!t'$2[1;<9\21_!t'B1!u1+FR1,1@fE'BR2fGR<#>R3P6O31;23!~I$3!wL&3R81B31fHR3#>';R2!|B,17?<R<'2R1'2P;P8P1P9P2P<P5P6CLCLCLb6b0b5b0b4b0W9W6W5W4P:P5O2!ts0!s/&W0!sBYb!s$$W0X17W:W;o"). Qed.

Lemma place_ok_intro : ltac2:(zQ "h50!h9!l5!jc!itb!vc!ho8!nb!lg2!hg3!kv1!lg8!lh5!li2!kja!km4!lp2!jp1!jp8!jpe!lk6!it1>1h$9>1a@1$2@1$0#k0>1n$6>0@3$1$6@2$h3@2$3@1$0#k0^2$bZ>0@2$h2Z@2$3@1$0#k0^3>0@2$h1@2$h0@2$3@1$0#k0^4^3@1$a^5>0@3$1$4@3$c@3$7@2$8@1$2@1$0#k0@1$2@1$0#k0@1$e^6@1$d^6^5@2$h4@1$0#k0^4$5@3$1$4@3$f^7^6^5$5").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##/?h01bh12H1h22H2h32H3h42H4h51ah61hh71np;1p;2p;3p;4p;6g009ej12Tg00:oj1MTg00;Mj1KTg00N0j23Tg01??j2@Tg00YRj2:!s/$nj26Tg01;5j17Tg00ZKj2=Tg00?Pj2ETg00`Uj15Tg00aOj19Tg007Fj3?!t$$Zj2>!t$$_j3<Tg01<jj2DTg014bj21Tg01=gj2CTg00X1j2LTg01>Dj2JTg01F6j48!sJ$Gj2I!tU$mj2A!sn$Jj2GTg013^j3HTg00>6j3BTg006:j6FTg00TaR0f0R1g01C3R23Bp=;g00S5R3g00VJR47B1p=0P3P4f3R5f2R6f1R7P1EFp=4g01DOg00RP#2!s$-MR8#KR91387g01B;R:'@#;1386,:21385/66f4R;#7'=1E99R9f5R<#5%9<3?1>857<;#0f6R=,38R>,D2R?,1116><R@f7RA#7RB'CRC'1%5A%9A5?91>8<7<=RA'1#0X031141/1C/1A!s5'4RD/11!s7,D4/1!sR&L34%5=%9=!so%;7<<P1C4138<R8/6;R1%7=R9'CR4%041=@B[1=19%0C[1J19P7C8C41D28R7%071:2>[1:28%0?[1I28P6!sF$@8:R8/A2R6%061@>:R>#;[%;81A>2#0[1G82P5C8C4AH=<;#0eW4W3W2W1X70W5W6o"). Qed.

(* [comment removed for export] *)

Lemma region_free_cons : ltac2:(zQ "f1!h9!jc!itb!vc!hg3!ho8!l5!li2!jp1!jp8!hm5!hn4!ho1!loc!jic&@2$4@1$1@1$0#k0@1$1@1$0#k0>1b@1$1@1$0#k0>1s@1$1@1$0#k0>1r@1$b~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$6$3@3$7@3$a~0@4$c@1$1@1$0#k0@1$1@1$0#k0^5^4^3^2^1$5@2$d@2$e@2$9@2$8@2$2@1$0#k0^3@2$2@1$0#k0^2@2$2@1$0#k0^6@2$9@2$8@2$2@1$0#k0^6@2$2@1$0#k0^5@2$2@1$0#k0^3@3$6$3@3$7^4^3^2$5").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##9Wh02H1h11Hh22b1h32b2h41bh57__arithh64__x1h74__x2h84__x3h91xh:1yh;2H0h<2H2h=4__ffh>8__varmaph?5__with@2lohA1nhB1rhC1sp;1p;2p;4p;3p;7p;8g009ej18Tg00:oj1[Tg00;Mj1KTg00?Pj2DTg009Ej1@Tg00Akj4WTg00O`j3VTg01?_j37Tg014bj2>Tg015YR0j29Tg016ej2BTg01FQj4;Tg01GJj1:Tg00N0j22Tg00Ynj24Tg00ZKj21!s/$gR1j26!sU$hj1UTg01HIj2TTg01<jj25!s8$kj2J!tY$@j1ITg01IKj2=!s/$ij4FTg01JGj1G!s/$ej1HTg01KPj2<Tg01L3j3E!um$Jj1L!s8$Vj4CTg01MAj7M!s/$ej1NTg01NGj8O!s/$kj2PTg00X1j2QTg01OMj2ATg01P9j3R!s/$Xj4STg01QJj3Z!s/$dj3YTg01>dj4XTg00>6j3?Tg00S5R2f0R3g00VJR43?p=0g00SU9?23p=3g00RPR5#8R6#8!s$+[R7#KR81D88R9#@P8P8f4R:f3R;CWf2R<5V9f1R9;73#0P01>93R=#0%0<R>%09R?'9[R@%03,9?1><9R?#0RA[%0;/9>\A1B93P9n20010!s#$12!s-%0X32X22P@^32^22P3P;P<f6R@f5RAC;#:R>A7:;<RBP9O3%0>%0B'9P0P:P;f7RBP@C;#:#0A7A:;#0127AR>127:'4f8RC,27RD'1127B,4DRE/1>'6A7@A:#0'9P3P@PAf9RAPC!sm'CB@#0f;R@,27R:,1Ef:,27,4:RE/1D'6A7ACB#0P0%:3#0%39RB[RD%33R>%:9#0RF[%3<RG\F%U!ui;42PD^42P3PAPCf<RCP@C;R@P<O2%3@P0%3=16GB[R=16B>%3?R?[%3;/6G\?1T!vhB=!vh'f>,27R=f=,27R?'4RG,5:R>15=ERE!vl$3>%3E'6P1127CRCf?,27R1/4=RE'5#314C:,51#314?CRCf!v1%'114:1R>/1?'6P315?>#3fA,27R>,1GRG14>:/1=R=g00TaR?P01593#3119<[R0113915<9#3RB[11<;\B1J!uJ<:?W9RBP0^:?^9?R0P3P1fB,27R@/4>RAP9O311A1g01R>RA#I%@AP?1=?<P91=?;CF%G?%H?RAg01RjR1g01SIRDPDg01SiRFPAP1PDPDPFP?1<?51<?65E?g01TI%L5,<?CCg01CoFMR5%NDP5GO1PAFP3P<1Q241A3<#0dg01C3=R?9CSb=b>b?X6?X7?X8?R41439/1<149</1;[^6?^7?^8?R?P3P>fC,27fD,27R7P9O4b5b0b13ZW0P3O115:C#3PBP0!zk$!w~$11E@P4P?P3P7P:P>!s\,9YG=!s^%!vk-211000!s'$b0b1b0b1P3CXW<W0P9P3O2!w?0!s/&b1b;W1XA8X@8WBXC8W4o"). Qed.

(* [comment removed for export] *)

Lemma stack_max_size_val : ltac2:(zQ "30!l5!nb!lpe@3$0$1$2+ogggg0").
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["FPX1"] "p;1p;2g009ej10Tg00AMj12Tg00X1j23Tf0R0#0#0p=4%00#0#0#0p=1g00Tag00RP#0#4#1#1#1#1#1#2'3o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_arg3_sys_input : ltac2:(zQ "90!h9!jc!hn4!l5!hs4!hk1!lr0!lu6!lv3>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N3@2$6^2N3").
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["FPX1"] "h02msh14segsh22x8p;1p;2g009Ej16Tg009ej10Tg00:oj13Tg00;Mj12Tg00E7j11Tg01U0j25Tg00X1j24Tg00QQ#6g00Vjg00RP#0#0#0#0#0#0#3#2R0f1g00Uk#1#1#1'5,40W2W0W1o"). Qed.

Lemma in_arg4_sys_input : ltac2:(zQ "90!h9!jc!hn4!l5!hs4!hk1!lr0!lu6!lv3>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N4@2$6^2N4").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##$ch02msh14segsh22x8p;1p;2g009Ej16Tg009ej10Tg00:oj13Tg00;Mj12Tg00E7j11Tg01U0j25Tg00X1j24Tg00QQ#6g00Vjg00RP#0!s$-3#2R0f1g00Uk#1!s$%'5,40W2W0W1o"). Qed.

Lemma in_arg5_sys_input : ltac2:(zQ "90!h9!jc!hn4!l5!hs4!hk1!lr0!lu6!lv3>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N5@2$6^2N5").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##$eh02msh14segsh22x8p;1p;2g009Ej16Tg009ej10Tg00:oj13Tg00;Mj12Tg00E7j11Tg01U0j25Tg00X1j24Tg00QQ#6g00Vjg00RP#0!s$-3#2R0f1g00Uk#1!s$''5,40W2W0W1o"). Qed.

(* [comment removed for export] *)
Definition mmap_args_ok : ltac2:(zQ "10!hk1>2ms$0P") := ltac2:(zQ "80!h9!l5!lr0!it1!jc!loc!lvd!hk1\2ms$7@2$5@1$6@3$1@1$4@1$0#k0@2$2^1N1@2$3@1$0#k0Z@2$5@3$1@1$4@1$0#k0@2$2^1N2@2$3@1$0#k0+3@2$5@3$1@1$4@1$0#k0@2$2^1N3@2$3@1$0#k0+i2@2$5@3$1@1$4@1$0#k0@2$2^1N4@2$3@1$0#k0-1@3$1@1$4@1$0#k0@2$2^1N5@2$3@1$0#k0Z").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition munmap_args_ok : ltac2:(zQ "20!hk1!jt2>2ms$0>5model$1P") := ltac2:(zQ "h70!lr0!h9!loc!l5!itb!vc!ho8!lvd!nb!hk1!jt2!mg3!jtb!mh0!kte!lh5!kja!mhb!jp1!jp8!lk6!it1!jc\2ms$9\5model$a@2$2@3$3$8@2$h4@2$4@1$1#k0@2$0^2N0$fZ@2$2@1$7@3$3@1$h6@1$1#k0@2$0^2N1@2$h5@1$1#k0Z@2$2@2$h3@2$h2@2$4@1$1#k0@2$0^2N0@1$e@2$4@1$1#k0@2$0^2N1$b@3$3$5@3$d@1$h0@1$c^1@2$0^2N0@1$h1@2$0^2N1$6").

(* [comment removed for export] *)
Definition munmap_eff : ltac2:(zQ "20!hk1!mic>2ms$0$1") := ltac2:(zQ "e2!h9!jc!hnb!hg3!lr0!hm5!hn4!mjd!ho1!hk1!mk3!mke!mhb!it1&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0\2ms$9@6$b@2$d@1$0#k0Z@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8~1@3$5~0@4$8@1$1@1$0#k0@1$1@1$0#k0@2$4^1N0@1$c@2$4^1N1~1@1$2$a@1$2@2$3@1$1@1$0#k0$7").

(* [comment removed for export] *)
Lemma munmap_outcome_si : ltac2:(zQ "h60!mic!l5!h9!mo9!lr0!hn4!hnb!mp4!nb!hs4!mpa!hk1!lu6!mse!jt2!mte!mu7!mv9!lmf!mhb!jc!itb>4segs@1$5$9>2ms$b>2x8@1$h4@1$2#k0>5model$e>1o@1$3$0>0@3$1$8@2$h5@1$2#k0^3+t7>0@2$h0^5^3@2$7@3$d@3$c^7^6^5^4^3@3$1@1$3$0^3@4$a$0@1$h1^6@3$h2@2$4^6N0@1$h3@2$4^6N1^4@1$6$f").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##3vh01bh13Halh24Hhash34Hlenh43Hnoh53Hnwh65lemmah75modelh82msh95nd_i2h:1oh;4segsh<2x8p;1p;2p;3p;4p;5p;9p;6p;7g009Ej1ZTg009ej12Tg00:oj1MTg00;Mj1ITg01Unj1YTg00N0j23!sJ$Jj14Tg00AMj1LTg00>6j31Tg01Vfj2J!s\$0j20Tg01??j2GTg00E7j1F!sn$Zj2XTg01X0j1E!s/$Ij1DTg00Ynj2CTg00ZKj2BTg00_^j1@Tg00aOj1?Tg01YGj18Tg01ZPj3ATg01[Fj3=Tg01\<j3<Tg01]7j19Tg012Vj3;Tg00O@j1KTg01^=j4:Tg015@R0j25Tg01_5j27!s/$jj56Tg01`jj2HTg01aVl9NTg01bPj1OTg01cGj3PTg006:j6>Tg01dUj4QTg01eaj4RTg01fhj1STg01gbl9TTg01i2j3WTg01jAj3VTg01kNj7UTg00QQ#Zg00Vjg00RPR1#2!s$-MR2#IR3g00]=g01lSR4#YR5g00TaR6f2R7,32%41#2#4!s&$4#4#LR131f4R8/J7f5R9g00UkR:'0R;,32R<g01B;'Gg01C3R=516R>%F:R?,09R@1X2=R=513#E132@#D,C<g01mQR<'Bg00S5RAf3RB#@#?%8@R@7A;g00VJRC31f6RD?=98?<B7P4%99A;;@Bg01nI#KR@C:9157'510D?=13=#Ef7R;/0:,3210;?,32#D'C/B<%@D#?f8R</0:10<?#83A=1ACf:RCf9R8;=<RE?<;D17E:RF17E?RGPEP;PDD6'5p-0RHP0g01o?f;?=C8R0?<<;170:170?RIP0P<P;D6f0RJP4%9C10C:RK10C?#8;;<P!t{%;RLPL1HHLM9NW6!t/%P3P<132J=161X03P9%OEAPC8<E>CQP3108:R:PJP!t2+/5LX03!s@$?R?PKPJ!s@2:P?!t%&BP2P?P=P7CR%S?g00SU51Aef1PJM9T!sO,D6P4%98%8?=;:;!t{&D'5ePGAW!tY$PFAV!s/$O2W2W5W3X1>PJFUW9W4W:W7W<W8W;o"). Qed.

Lemma munmap_ok : ltac2:(zQ "h40!h9!lr0!hn4!hnb!l5!nb!hs4!mpa!hk1!lu6!mse!jt2!mic!mte!mu7!mv9!lmf!mhb!jc!itb>4segs@1$2$6>2ms$8>2x8@1$h2@1$0#k0>5model$b>0@3$4$5@2$h3@1$0#k0^2+t7>0@2$e^4^2@3$a@3$9^6^5^4^3@4$7$c@1$f^5@3$h0@2$1^5N0@1$h1@2$1^5N1^3@1$3$d").
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["FPX1"] "h01Hh12Hah23Hnoh35modelh42msh54segsh62x8p;1p;2p;3p;4p;7g009Ej1DTg009ej10Tg00:oj1=Tg00;Mj1;Tg00N0j2CTg00:Jj12Tg00AMj1>Tg00>6j34Tg01Vfj2<Tg01[Fj36Tg01]7j13Tg01U0j21Tg00E7j1:Tg01YGj19Tg012Vj38Tg00O@j1BTg01^=j47Tg01\<j35Tg01Unj1?Tg0200j7@Tg00X1j2ATg00QQ#Dg00Vjg00RPR0#0#0#0#0#0#0#=R1#;g00]=g00Taf1R2,C1%20#0#2#0#2#2#2#>34f3R0/<2g015Yf5R1f4R3;60f2R4g01lSR5%33g00UkR6,13%:6R7,13#9;84g01nI#BR8C7R935%?5R:P5%3111161117#9;80P8C7R;;4;R<[A4:99f6R=?613?50;[R>f7?6=1P5%3=11=611=7#9;83P8C7753\<P1P3P0P4P9P2f0R2F@P2n2001000000120000000P>P21A:;O1b0W1W2W3W6W4W5o"). Qed.

Lemma munmap_ok_inv : ltac2:(zQ "h50!l5!hn4!jt2!mic!mte!loc!h9!lr0!hnb!nb!hs4!mpa!hk1!lu6!mse!mu7!mv9!lmf!mhb!jc!itb>4segs@1$1$a>2ms$c>2x8@1$h3@1$6#k0>5model$2>3eff$3>6model'$2>3evs@1$1$4>0@3$0$9@2$h4@1$6#k0^5+t7>0@2$f^7^5>0@3$e@3$d^9^8^7^6@4$b$3^5^4^3@2$5@3$0$3^6@1$h0^9@2$5@3$0$2^5@3$h1@2$7^9N0@1$h2@2$7^9N1^7@3$0@1$1$4^4@1$8$4").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##40h01Hh15Hspech23effh33evsh46model'h52Hah63Hnoh75!s:$h82msh94segsh:2x8p;1p;2p;3p;7p;8p;4p;6g009Ej1?Tg009ej16Tg00:oj1DTg00;Mj1ATg00N0j2L!sA$Jj18Tg00AMj1ETg00>6j30Tg01Vfj2CTg01[Fj3:Tg01\<j3;Tg01Unj1@Tg01]7j14Tg00E7j1KTg00O@j1JTg0200j7ITg021=j8HTg015YR0j21Tg00X1j2<Tg01>dj4=Tg006:j69Tg01^=j4F!t3$0j2>Tg01YGj1GTg012Vj3BTg01lSR1f2R2f1R3f0R4CFp=7f3R5g00UkR6'>1>23#G;B4p=2A0134p=5g00]=R7?034p=3g00QQ#?g00Vjg00RPR8#6!s$-DR9#Ag01nIR:#?R;g00Taf4R<,L9%88#6#!s&%8#8#E30f6R8/C<f8R9f7R=;:8f5R>A7<523;P0f9R??:9=A7><5R57;8%@1R@A78><R<%4?P?P?%K6R6P=C2%J:R:3730RA[RB%49P9P9P6P8C2;7:90@5f:RC?:?9?;=<R<[A7=8>%4CRDPCPCP6P9C2RE;7:50@\<P?P9P=P8P5P2P3FIP3n20010!s#$12!s-%0PBP4P3O1PAP1P=PDP8PEP>P:P4GH15=D138EA0;>:'1'1P0f;R>#4,59P>P>P6P?C2,3=A0;8:'1f<R8#4,5?P8P8P6PCC2,39A0;=!sd%4f=R=#4,5CP1f>R9#4f?REPEP!uu$,3>RDA0;C:RA'1f@RB#4R2,53PBPB!uS%,38!tZ&R5'1[X21!vA,,3CA0;?:'1P0PDPA1522/15P4fAR5P5P6PE!tz$P7fBR2P2P6PBC2A0;9:fD!t:$A/5ARA!t<&2C2R2,33A0;E!u4$[X47!uA$P;P:1322A0;4:'1,1AX3;fCRA#4R2/52PAPAP6P5C2R5/35R6A0;:!uJ$1<12P6PA1<751<;:C=C=P9P4E9W0!s-+3P4O2!wp0!s/&W0P>!sJCb1b1b0W1W5W6W3X47X21X77W:W8W9o"). Qed.

Lemma munmap_no_unmodeled : ltac2:(zQ "f0!h9!hn4!l5!lvd!nb!hs4!ng7!hk1!lu6!mse!jt2!mic!mu7!jc!itb>4segs@1$1$5>2ms$7>2x8@1$d@1$0#k0>5model$a>0@3$2$4@2$e@1$0#k0^2+t7>0@2$c^4^2@1$3@3$9@3$8^6^5^4^3@1$6$b").
Proof.
ltac2:(KReplay.run1 (kr_t_MmapSim ()) ["FPX1"] "h05Hspech11Hh22Hah33Hnoh45modelh52msh64segsh72x8p;1p;2p;3p;4p;7p;5g009Ej1FTg009ej10Tg00:oj1?Tg00;Mj1<Tg00N0j2ETg00:Jj12Tg00AMj1@Tg00>6j33Tg01Vfj2=Tg01[Fj36Tg022?j1;Tg01\<j34Tg01Unj1:Tg01]7j19Tg01U0j21Tg00E7j1DTg01YGj17Tg012Vj38Tg00O@j1CTg01^=j45Tg0200j7ATg0237j5BTg01X0j1>Tg00QQ#Fg00Vjg00RPR0#0#0#0#0#0#0#?R1#<g00]=g00Taf1R2,E1%20#0#2#0#2#2#2#@33f3R0/=2f5R1f4R3;60f2R4g01lSR5#;R634R7g015Yf6R8?613?406%:5R9P5%98g00UkR:,18%D:R;,18#7;83g01nI#CR<C5736R=[R>P5%91111:111;#7;80P<C59396f7R??681?436R@[P5%9?RA11?:11?;#7;81R?P<C59396\@P8P1P3P0P6P4P2FAP2n2001000000120000000P>f0R>P2O1P=P5PAP?P<P>DBb0b1W0%>7eW2W3W4W7W5W6o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unfill : ltac2:(zQ "31!h9!jc!n2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m~0~0") := ltac2:(zQ "a0!h9!jc!itb!vc!n2!nh4!kvb!jp1!lj8!ljf\1a@1$1@1$0#k0\1n@1$1@1$0#k0\1m>0@1$1@1$0#k0@1$4@1$1@1$0#8\1x@1$1@1$0#k0M3\0$3@1$4@1$1@1$0#8@2$6@2$8@2$2@1$0#k0^4@2$2@1$0#k0^1@2$9@2$2@1$0#k0^1@2$7@2$2@1$0#k0^4@2$2@1$0#k0^3@1$5@1$1@1$0#8@1^2^1").

Lemma unfill_out : ltac2:(zQ "a0!h9!jc!itb!n2!l5!jic!nhb!jp1!jp8!jpe>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1x@1$1@1$0#k0>0@2$5@2$9@2$2@1$0#k0^1@2$2@1$0#k0^4@2$8@2$7@2$2@1$0#k0^4@2$2@1$0#k0^3@2$2@1$0#k0^1@3$4@1$3@1$1@1$0#8@4$6^5^4^3^2@1^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["FPX1"] "##5bh04__x1h14__x2h22Hxh31bh41mh57__arithh64__ffh78__varmaph85__with94__x3h:1ah;1nh<1xp;1p;2p;3p;4p;7p;8p;6g009ej15Tg00:oj1ETg00;Mj1@Tg00<0j1ITg00N0j20Tg00YRj24!s/$nj22Tg00ZKj23!s/$gR0j2MTg01=gj29Tg01<jj28Tg014bj26Tg01Mej1CTg00>6j31Tg00X1j2DTg024?j2WTg00O@j1VTg009Ej1UTg01IKj2A!sJ$_j1R!s8$ij4BTg01JGj1O!s/$ej1NTg01KPj2:Tg01LVj4>Tg01Nkj2LTg01OMj2KTg01P9j3J!s/$Xj4HTg01F6j4?Tg025=j1GTg01Hkj2P!sn$3j3Q!v@$Jj1F!sJ$]j4S!uE$Aj7T!t1$Gj8YTg006:j6XTg00S5R1f0R2g00SUR331p=7f1R4g01RjR5g01SIR6P6g01SiR7P2g01CoFTp==f3R8P5P6P6P7f2R5P4P2GYp=<P1P3P8P!s7$EXp=;g00RPR9#5R:#5#5R;#5!s$$ER<#@R=%E;#@R;#IR>\=10<2R?10<8R@'410<5RA,2@/3?'MP010<4R0f4R?,0<RB'412B@/30P1P>f5R0,0<RC/9A12CBRD,8A'6%C;R;P8P5O1REn010!s#$20000=1>EP214AC!sf$7,0<REf6,0<RF'2RG,8BRH,62P;P0P?O1R0!sf40X31P?P8O1RI,D>RJ19F@RK%7K14BE[14@F19EBRL#7[1WF@PIP>g00TaRMg01R>RN#VRO%UNRNPM1AM5RPP4%RMCB%OMRQ%NMRRPM1:M9RSg026_1:M:R:C>,=RRT%C6R6PTC<1LR7R7P2P5g00VJRT,D11K25=11Tdg01C3=JM4CHRTb6b7b8X0MW114241445[^0M^1MP2f8,0<R<PCP5O3b5b4C?C;W2P2O113DAP1P>16L!v,$!v#91P>P!sE>J16K3%GKC;12FCRF,8!vI&3GB[13F@%7H[1P@FPIP>POPNPMPPP41AM8CBPQPRPMAQMS:g01TI%F9,:M!v#%RP6PRC<P7P!uV,X1MX9M1224/351245/38!u`&^9MP2PCPEP<P5O4!u`1n20!u3+11000!s'$P?!{8%CSP5P4O151>eW2X<=W4X;=W:o"). Qed.

(* [comment removed for export] *)
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hn4!hs4@1$0$1").

Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
    (1 <= length buf)%nat ->
    twm_pend ms model buf bufs code ->
    twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(* [comment removed for export] *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
         (skipn n rest) bufs code) ->
    twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
    twm ms model bufs code ->
    twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
    (1 <= length rest)%nat ->
    twm_pend ms model rest bufs code ->
    twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm_tail ms' model rest bufs code ->
    twm_tail ms model rest bufs code.

Scheme twm_min := Minimality for twm Sort Prop
  with twm_pend_min := Minimality for twm_pend Sort Prop
  with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_munmap_inv : ltac2:(zQ "hd1!h9!jc!l5!hn4!mte!hnb!n2!hg3!lr0!ni5!nie!nh4!v5!loc!nb!hk1!nj9!nkb!nl4!nm9!nn9!jt2!lm3!lnf!nrc!nse!ntc!nuc!itb&@2$7@1$1@1$0#k0@1$1@1$0#k0>2ms$f>5model$h5>2x8@1$1@1$0#k0>3evs@1$3$4>2st$a>0@3$2@1$6@1$1@1$0#k0@1$h6^4@1$b@1$1@1$0#k0>0@3$2@1$3~0@1$h7^5@1$5~0>0@3$2@1$6@1$1@1$0#k0@1$h0^7@2$c@1$1@1$0#k0^5>0@3$2$e@2$hc@1$0#k0^6+t7>0@2$h8^9^8>0@4$h4?4segs@2$9^a^9^7^6@2$d@3$2@1$3$4^8@1$5$4@3$2$a^7@1$h1@2$9@1$h2@2$h3^b@1$h9^b@3$ha@2$8^bN0@1$hb@2$8^bN1^a").
Proof.
ltac2:(KReplay.run1z (kr_t_MmapSim ()) ["WithSegs"] "#$Uvp'0h01Hh12H1h22H3h32H0h42H2h52H4h63Hssh72H5h82H6h92H7h:1mi001mh;2x0h<1li011lh=6model'i02!s0&h>1si031sh?3evsi043evsh@!sE%0hA3ms0hB2sthC3effi053effhD1oi061ohE2HxhF1ehG4evs0hH2HmhI2_HhJ1thK4HeffhL3HeqhM4HevshN7!tI%'i07!s1'hO5HargshP2HhhQ5HlazyhR3HnohS4HsvchT1ci081chU4codei09!s-$hV5!sj$i0:!s/%hW2msi0;2mshX3ms'i0<3ms'hY3sigi0=3sighZ2x8i0>!s+$?9cfg_!sl&@6!s3$sp%0p%1p%2p&0p;1p;2p;3p;4p;6p;7p;8p;9p;:g009ej1ZTg00:ok10mTg00;Mk10cTg009Ek109Tg00<0S00k10FTg01Mek10CTg00?Pk20BTg00^3k10>Tg00O@k10:Tg00>6S01j30Tg00=Tj22Tg00N0k207!t@$Jj1qTg00AMk10gTg01Vfk20fTg027Fj21Tg028;R0j44Tg00E7k10bTg00\Fj1C!sD$oj1GTg00G^k10[Tg02:5j3PTg00Kej2oTg02;1j1B!s/$gj4STg005?j6=Tg004cj66j7Lk80ITg02<Cj2!tN$<bk10eTg015Yj2ATg02=jk10dTg01[Fj3!v$$]7j1!ua$5]j6^Tg012Vj3jTg02?2j1yTg02@8j2xTg02AAk40?Tg02BQk30!tN$_^k10<Tg00`Uk10aTg00aOk10`Tg00bEk20_Tg00c>k10^Tg00Ynk20]Tg00d8k30;Tg00e4k10\!s0$ok10!x>$fdk10YTg00g[k10XTg00hVk10WTg00iOk80VTg02Cbk20U!x1$kk10TTg011:k20!vG$jFk10R!uO$;k30QTg00kFk30!w$$l>k10OTg00m1k10N!s0$fk10MTg00n[k10LTg00oOk10KTg010Dk70JTg00X1j2!xb$>dk40HTg006:j8bl9uk600k70Gm:0lTg02D\l:vTg02Eej6wTg02Fjj1?Tg01\<j3hTg02G]j1}Tg02HTj2WTg02IJk30ETg02JYj2_Tg02KOk20kTg022?k10!wn$LWk70iTg02Mfj2`Tg01U0j2lTg01YGk105Tg02N_j1!wc$Akk40hTg01^=k403!{X$`k30!z`$7Fk30DTf2R1f1R2#Cf0R330p=8%G2=013p=Dg02O\S02?023p=Ig02PQR4!s4%J%:3,`2p=df3R5g00UkR6'l1l12$05;j3p=3%a2/13p=c%B39042p=]A0512/A3p=9g00VjR7g00]=R8P2P3H0hp=p%B2=043p=eQ02P8P5P1P2P3E^p=nA0823p=5Q02P7!s@/rA0723p=>f5R9f4R:#:'`#a1l56!ta,'1#Bp=N1112#B!t2%QA0423,A1p=i1123#Bp=H!uQ%#ap=U!s:%9041,A5p=VP:115!tD$C4p=MP8P:!tU'J00p=\P7!s82[g02QGS03!t?%;P4Q03!sJ,FLp>02!s;%!uF'6p=|g01lSR;!s8%H039h:5p=71283p=<%y2,x1=053p=K1`12#a!w0$Y%y3,x2p>0112839012p=k!sG+#Bp=TA0:51!w'&'Ap=Xf6R<?F9:P!t<,7h5p=R1`23#ap>0A!ti%%B3C4p>0@1l36p={1l23$05p=z%:2,`1!t2'>08!sr-p=tAF:51?h23p=@%}!yu&Og01nIR=1W12<!v:$~B0D=12!uM%mB04=23:0D=1p=E12239051p=s1_12>04=3p>06g00RPR>#Z!s$,$0mS04$0cR?&09=R@&0F?RA&0C?RB78520B??RC$09&0>:&0:C3012?:9DA<S05g00TaQ040079%q>#Z#q!s&$q#q$0g30f8R>f7RC+0fp,4segsRDf9RE/1>S06P<P9C4P0PDf>S07f=R0'1S08,I5f<RF90@51J5FP@Q07&0:=R=fARG/dGPGPG&0b6R6f@RHC3'c,]0C9[[[P3%C1S09=0ABRI%G:S0:!s2$J20B78RK$0[RLAPD9:1p51,oK3011<9RMfHRNfGRO'1RP'IfFRQ90@=1eMQQ06fKRMfJRR'1S0;'IQ02!|~%3P3n0110800012010@10?WFS0<f:S0=/1ES0>fLRS/1MP3Cn15EM!sc&7P3P2!sc9?f;RTQ0='1S0@fMRU/1SP2Cr1>TUfNRV,>FP3fORW,>0fPRXQ07/5XRYA0@=WRZf?R[Q07'1S0A/eWA8AGBfCR\9PD9fBR]/pG,oK50LP@fTR^P=fSR_fWR`P!s$%6fVRaENS0B'JS0CC9]1^3J]0]5]2[X:7150WP3PYfQ!tA%XRb11H[S0D/eXRc%GaS0E=0ABAPD`:1p\]!t=+URdP=fXReP!s$%6P`ENS0F,J^C9]1]3^0I]5]2X:8P3PbP@P=AQGHYRbA8AdBRf%G`Rg!x?$hAPDe`fDRi/p\!t/%RjA0@:=S0GfYRkP!s$%6PeENS0H7id]1]3]0]5X<@!t+$41H]G%CaRb!t|$DAeBAPDkefERl/pi!s{%A0@==RmfZRnP!s$%6PkENS0I7i5!sx%X>4P@P=PD11nkRoP3PaC4Pm11OQRp#Bf[Rq/UqPqPqP6PnC3CV]6X?@PD11keS0JP=PdC4P411QlS0K#BRrPDPqPnP=P3DMPm%BPf\Rs/UsPsPsP6Pq!sk&B4PDPoP=PrC4PAPB%GqS0L12?kRrPAQ0LPBP5CSRo!s3'rP5!sN$CnRtPrPAPtPBP:CS!s0&rP:PAPBQ0LPrPoP^E=!s$'A0ABr!sB%0P?p-0S0MP3g02R=Rrg02RZS0Nn101106000210!s#$XFAS0Og02S6S0P12?nP3E6PrPmfIRo/1NS0Q#Bf]Rt/UtPtPtP6PsC3CV/f3b0bLW6PaP9P3F!s0%<PWFLX7jX4hX1ffRRfP3E6b1X5cPY!s1&2ZP[P3D\b1W3Q07P3D[b3W0P3O1b!s+&W4!#6p$P9P:P5O6W5W2W4W1W3W0X=8XX7X@8XA7P<!sH%!sT%O7A8A3BS0RADA1BS0SAPD51S0T&0eKRZ50L11:511i\'IS0UA0@=]S0V%;]S0W11C</IpS0XQ0<11>CS0YPPP3CnS0Z15COS0[Q0?Q06Q0QP2CrS0\1>EoS0]Q0=/>RS0^P31>TMS0_PS15FSRPA0@=MRp%;MS0`A8A[BRcAPD9GRh=0LZA0@X=S0aPW1U__P_P_P6PfC3CVS0b!~44TMS0cP3PPP!u1$SRj%;SRuADAfBRvAPD_:Rw=0LZP@PYP=1d^^P^P^P6P_!#7%$XC9S0d!}}4jP@P=%;US0eA8AYBRxADA_BRyAPD^_Rz=0LZR{Q0G1dddPdPdP6P^!sx%YS0f'AS0g!}q0Q!so$fBR|%G^S0h!~n$}APDd^R~!to$a!s$&6PdENS0i9im5S0j!}e4adRZP3PfC4Q0B#;,Am!}P+d^S0BP=PYC4PD11`aS0kP=P3C4Q0F!sQ'!}6$ZP=Q03!}7%Pg12?dS0lPAPg!}3%S0m!s3%Q0l!}4%PbQ!sG$b!}2+b!sD%!}3$PgQ0lQ0mPX!}4,Q0l90AB!sq%BQ0OQ!|[$aS0!|^$S0oPrQ0H!te$S0H!|K,fP9P3I02!s1$<PMFLRgX7{X4yX1xPVP3C|b1X5uPU!|L'pP0!|L'PF!|KT!|E%!|A,5Q0RQ0SQ0T&0dKRK50LQ0UQ0VQ0WQ0XQ0ZQ0[Q0\Q0]Q0^P3Q0_PSQ0`A0LhKQ!zc&^0c]5^2p\PX:7Q!zb,LwKQ0d]1^3v^0I^5u^2j!z1-Q0eA0LzKRzQ0g]1^3y^0x!yY-0L~KQ0j]1^3}^0|X>4PgX7z!v:~!v:2%C9S0R=!xG$S12?99DACS0UAFD><S0VPC!sn$1D7Q0S&0F8RpP<PC%<9CKQ0@11fY'IS0WA0@<XQ0==Y0>/eXQ08Q0B'I!#3q$Q0APZ!#3m$^Q07/5dS0cQ0?Q0DQ0k!#3o$D1>H`S0j1>GeS0gP31>]kS0dPn15\nS0`A0@[kS0bAY1\G/ek%CQS0_!u0%]Q0:12?QS0\50AS0[AFD9OS0ZPNPQPlP\D7Q0]201ONS0T=kpQP@f`RZP=f_RufcRxP!s$%6fbRyENS0p'JS0qC9S0r]2]4!~Z&8]7!#4V$]kS0sP3Q0`PqA0@HnRzf^Rg?Yi]/enS0t%GZS0u12?OS0v!tb$wfaR|=FDNS0xP:POPQPiD7%COS0y!u<%z201NoS0{=kpOP@P|P=fdR}P!s$%6PxENS0|,JZC9S0}!te'^0I]8]7X:8Q0bP3PzP@PqAYul\/eqRzA8AuBS0~12?NS109DA|S11AFDyoS12P|PNPOP5D7%CNS13!tW$14201oRS15=kpNS16P@PyP=feRKP!s$%6P}ENS17,J|S18C9!vA/X<@Q0t!tW$4ATZQiA8AZBS1912?o9DAyS1:AFDxRS1;PyPoPNPZD7%CoS1<=0ABPpPRPM%<oCKP@PxP=ffRzP!s$%6PKENS1=,J9S1>!tF/X>4Q0~Q11Q!uK+uD7Q14Q16P4ATKMoR~PD11zKS1?PxP3C4P@P}P=fgRL?YUM%:LS1@PLPLP6PzC3S1A5TLS1BDX!#6d%11K}S1CPyP~C4PAP?Q00P?P?P3P3PV!#?_5JAS1D12?US1E12?}S1FPAQ1E%GzS1GQ!s4%GQ1EP:CSPuE=E^A0?U}P?PKfhR~#GS1H12?3S1I50APDfiRjP2P~PWPVPzFRP@PLP=fjRv?YXV%:vS1JPvPvP6PjC3S1K5TvDX]2]4X;?%GLS1L12?KS1M!su$P~PzPLPVPUPKFR%:jRw90;WS1NPjPjP6P~C3S1O,5VA0@z=RPPPATjWU20AjwQ1OCVQ1NQ1K,5WS1PA0@~=P;flRw#:S1QPDfmRP/1wS1RPvAYP3YH0@fnRc=FDwS1SPPP2P_fkRJD7PpP^P1%<_!xd$PP=fpRh?Y5^%:hS1TPhPhP6foS1UC3S1V5ThDX]9]2]6XC;PDPwPJPjQ1Q=TwXDMAFDPJS1WPw%:PS1XPfPv!t2$_%:cS1Y%<fCKP8Q1UQ1UP6PcC3S1ZAFDhcS1[!s=$TP3PPD7A8A2BS1\PpP1frS1]#:S1^%<a!tv$hP=fsR{%:{S1_+0ARb/H`S1`P{P{P6Q1]C3S1a,1b']C9]9]5]2X=8Q1U=FDPS1bPcQ1U#:S1cQ1ZPwD7Q1V=8ABfqS1d#{S1eQ1d/z6S1f;jhS1gQ1d#:S1h#yS1i'xS1j=kpd!#?1$P{Q1]P3Q1`DMPDftRbQ1]P{%:bS1`%{bS1k1zb6S1l;j{S1mP2!yW$1P=fuS1nQ1n'US1o/1kQ1oQ!s7$P6PbC3S1p'H!y]$!#@#$Q1]Q1dP=!s-$^;TaDM!tL%d!s8$_Q1aP=FRPpQ1mQ1`#yS1`'x%<kS1a90p3XDpP1Q1m#<Rb!sI%Q1kQ1lP{PcH0?40=E6AkpbeQ01PpQ1p#<Rb%<qS1p90p2PmfxS01Q01'UR{/HsP{Q01#{S1`Q01!vL$mfwR{3jS1lCV[P3Q!tF$bfvS1kQ1kP6Q1nC3#<%<nS1n50pPpP8Q00P8!#SV$&0<{Rb$0a&0`bQ1`+0_&0^bQ04!s3$7S1`Q1`!s5$m+07+0]S1m40;&0\b&0Zb&0Yb&0Xb&0WbL0V00U!su$T&0<b&0>b!uh$m40;!s/%+0S&0Rb60Q?40P&0Ob&0Nb&0Mb&0Lb&0KbK0J!#3e/10001XFp!y~'kC3S1k#<Q1pP3E^Q1k/5qQ1l/5sP3fyS1lQ1lP6Q01C3/5tP8fzRbPbP6Q1lC3S01Pmf{S1pQ1p'US1m/H3!uZ$mQ!s:$!xu'mCVX:8P8Q01PDQ1pPbP=!z,$f|!v1%P6Q1p!yG$#<=kp2f}S04Q!s%'P6Q1`EN!s9%5im]9]6XN8PDPbQ1lP=Q01:08bbDM!y3&=0pbP!y6%`Q1p408Rb/Jb1g@=1g4bH0HW9W6PgP2PCP9L0IPgP3E6b7W3P3O1!#AP&W0n2!vU$6!#7>$101Q1n90p3Pm1U{{R{/HqP{Q1kCV[XDpQ1aO1P3Q1n,gpO1b0b9W2W6Q1UP<P9P1GbW9W5W2P^P:P2PTP3M9uW!sJ$PfP1P<P5PCM9uWMWHWKPDPjPL!#7Z&P|PZP3M:vEwW2W4PV!#C/$GbbEW6P|P<PqFL!t,%W4W1Ps!uG$1W8PGP3J00b1W7Pi!#D0'\!#D07!#Cd%PC!#PK&O8W8W7!#D8/G@XN8X=8XC;X;?!#DG%TQ0=PEP>!s`,!sp%O<A8A:BS0bQ05PDPCP9P<!sE%FRQ0bPpP9P<&0C8R{CKQ0>11XW'IS0tA0@=VS16%;VS1N110FS1n11_f'IS1aQ0<Q0811^_!#DL$8150_S1kQ0?Q0AQ0B!#DJ$B1>[dS0A1>HaS1pP31>G`S1`Pe15]eS1mA0@=`S01%;`A8AlBS1l!#D@$lS0450AS1_PDP9PQPOPlPiP\FRS1^Q1lPp!s:${CKP@PgP=1d||P|P|P6PZ!#Oe$tC9S1o!#D26G`S1qP3Q1mPkA0@=eRb%;eS1rQ0\9DAgS1sPDPuPOP:AtQliS1tD@S1uQ0]Q0T=0p{P@PuP=1dyyPyPyP6P|!tB%gS0T!#@k+!#Cg-1!#]%&%;kRbA8AtBS1vQ0v9DAuS1wPDPZPNPuAtOQlS1xD@S1yQ0zQ0{=0p{S0{A0@<=S1zQ0q'A!#C>21rP3PbA8AgBS0qQ0uQ10!v]$0PDP|PoPZAtNOQS0uD@S1{Q14Q15=0p{Q0|9im!#Bn11vQ1wQ!tN'!#RN&}xS14P3PZC4Q17!#P=$15!#RR'xyS1|P=PuC4PDQ1C!#RN%1=!#RN-Q14!#RO%Q15PAP?Q1DQ1E12?xS1D!#BB%KS1=Q!s4%=Q1EP9CSPg!#BB&xP?P}Q1LQ!#B8%P~P2PLAtWVUS1ED@Pr!#Al%Q1GQ1F!sJ%LPKPzAtVUSS1FD@%:~S1}!#Ah$~P~P~P6PLC3S20,5VS21A0@U=PrQ1~Q1O,5WA0@W=P;%:JRbAFDwvS1OPJP3PfPY!#@+$P2!zI$r]9]2XC;AFDJjS22PvPbPYPX!sK$fQ1Q!sL$8%{PS1Q1zP6S23;jwRbQ1SPPQ1YP3P_D7Q!#@E$Q1T!s|+!#?g&WPwQ1XPbPfD7PcPcP6PPC3S1X=8ABPpQ1ZQ1c!{}&=PDQ1dQ1UPhQ1hQ1gP3FRPr]2XG@Q!#Ad&Q1VP=D7PpQ1jA0p3{XDpP2Q1g#<S1jQ1gQ1iQ1eQ1fPhPJ!#=|&Q1j!{n$pQ1]Q1]P6Q1dC3#<Q00P8Q0MP3Q0NPr!#`b6pQ0PP{!#`X$1fr3S0N!#7O$PdP9P1K0G!#7K%_P5!#7K/PfP1P5P>Gb!#7F'!#G,$WPVPUPZPu!#7F2<P9GbbE'fW6PZPC!#Ws&ZP>Pk!#7S/n!#T^$W8Pk!#7]%7P\!#7R']!#7R^!#7O0!#7M:;Q0S!#X&$!#Tf%5D7S0VQ0R12?5S0550AAOA<BQ0WP@PC%?>=~<=PXCmAQ0EXQ0XQ0^Q0cQ0DQ0jQ0gP3Q0dPnQ0`P@PH%?GS0d=~[=PkCmS0jAQ1]kQ0]Q0[Q0ZQ1t7hNQ0_12?iS1t50A%}O!#TT%Q!#SP6Q!#SL'P@PG%?]S0`=~H=PnCmR{AQg\nS0]Q0wQ0xQ1x7h:Q0yQ04!t$$N!#S@%Q!#Rk8jP3P{P@%?\,WG=E]=AQuiqR{!#P6'Q0u7h|S0uQ13Q!#V8$13AOAoBS12Q1zQ18!#5y40]!s}$41HZlQ19Q1:Q!#Q~'OD7Q1<Q0v!w,%RBP@%?MS1<,Wo=ER=S0vP=Q!#Qo:!tV%12P@%?RS19,WN=Eo=S1:PDQ1?P3PyC4P@%?S,WR=EM=R{P=11LSQ1BDXRp!#Hl'CQ1:P|C4P41HzM!sf$PLPzP{P3DMP@%?U,WM=ES=P=11~UQ1}Q205T~!#RG'Q1?Q0vQ1:!#RE4W!#RE712?VR{Q1MPAP{Q1L!s0$Q1LP{P9CSPZ!#6t%VKP?PzQ1I9DAjPDPvP2PjPXPWPV!#3X$]4X;?PAQ1HP?PzCs!#Ar&Q1ED@Q1J90;XR{Q1PA0@V=S1PPrPJPJP6PvC3S1J,5XQ0aP8PbPDPcPP%?3S1E,WY=Ef=1Hc3DMQ1bPcPdP2P_D7PAQ09P?P_CsAOA5B!#5z&]6X=8PDQ1R%?b,WX=EY=11PbH0@Q1SPPP^Q1XPfD7Q1Z12?fRc58AQ1V=OABPAQ1g#C!#d]$3XDAP2%ChS0l!#5U$<0EhE6PAQ0lP?P^CsPAQ1d#CQ0n!sV'3PBPPE6Q0mQ!#e'$Nb0b5b5!#3p%6PfP2P<P5PEP>N:0lWIWHXI{!vo$~!vo'PyP|!#4w-W!#4w+,fpW6PyPC!#o:%yP>!#EL;q!#4w'!#EKfU?!#4z4!#EK=!#4|'Q059OA9Q0tP@P<%?C>069=PVCmAQF>VQ1aQ08Q1kQ0BQ0AQ1pP3Q1`PeQ1mP@P[Q07%?H<06=P`CmRpAQ1G`Q1lQ1_Q1^12?\R{9OAlP@PtP=1dZZPZPZP6Pu!#Bn$sC9!~c+7]5[X:7Q!#D%'P@PHQ0d>06[=PeCmRZAQs]eRlQ1sQ1uQ1t9OAQQ1o!#4P+7]5!#gJ$ZP@Q0`,_H=EG=AQt\kRZ!#Am,_!#5@$RPP@P9P=Q0T!tW/!#y9$ZP41HgiQ0qQ10Q1{Q0y!#4z$P@%?o,_O=EN=S0yP=Q0p,J:!sh,!#C%-P@%?N,_Q=EO=RZPDQ1|P3PuC4P@Q19,_N=Eo=RNP=11}RQ0|DXRh!#3v%!z#$ZPgDMP41Hxo!se%4PN!#_I$Q1<,_o=ER=P=11KMQ17!#3n,|Q0yPZ!#3m4U!#3m:SRZ12?yRNPAPZ%G}R|PNPA!tP$:CSPt!#3p%SyP?PxQ1G!#Cf'LP2PzQ1F!#Ca/=Q1D!sE%zP}PKPUPSPMFRQ1@90;VR}Q1A,5UA0@S=PrQ21Q1PP8Q1KPDPJPvQ1E,_W=EX=1HJ3DMQ1OPJP_P2PYD712?YRY9OA1Pr]8!#3Y'PvPjQ1K#?,_V=EW=Q1K,HvDMQ22PvPfQ1JPXD7PwPwP6PJC312?X5OAPA%}bA0A3c!#3#&A%Cb%CwPBQ1QQ23<0EwP~E=-0kbE6A0ABY!#q]+Pc!#A^$!#3P$8W8W2W6PX!#3L%>M9u!#3I$}!#Fb&PV!v%$uPg!#3I-U!#Qb+,fhW6PuP<!#3I%uPCPeFLX8P!#AA+E6b1X7l!#AB&X5p!#ACC2!~X%!~f'O7!#3F1Y?!#ABN1\12?29DA5PDP:P1P5&0j;R;D@119:Q0K'IA0@=i%;iQ0YQ0Q'IQ0<Q0611Ro!$/Q$>oQ0?Q0>Q0;P2CrQ0=/>M1>TSP31>FUPV150VRVA0@=URS!#xc$HBPAQ0:P?PHCsPDP9PGP]P;D@P@PfP=Q0f!$,>$!#{>-FUP3PVPWQ16Q1NPAQ0hP?PG!sf$dP]P:!sf&_P=Q0i,Jf!$-%4Q16!#P#$WRIA8A_BRG12?]9DAdR]PDPaP\PdP;D@RdQ0GQ0C'A!#zp,Q1NP3PIA8A^BQ0E=0A{PDP`PiPaP;D@Q0F9im!$,B4e`RaP3P^C4Q0H!~o&Q0kP=P_C4PDQ0J!#zN&I!#zN/a!#N}&0H!~Y3O!~Y8Q0\12?`RaPAQ0\%GkRmPaPAPmQ0\P5CSPf!~X&Q`P?PeQ0!#O@+sP2Pq!v^$r]7!~W$12?e9DAnPDPqPkPn!sC$DPsPnPqP^P_P3K0iW7W4POP3P:P5!#Iu'^!#zj+^P<PUFLX7dX4]X1GPX!#It%5PW!{X&2S!$+'$!{Y%0!#wTS!{I'!{>06n104108!vD$3!v?%87110;10:10<1020!s#'5!s=&!s7=<!s_+>1051021071040!s#1;!sL5!sI3!so64109!soF10=!sI/6!sI,!s:+Q02Q1n,I1A0@1T1J1TP@P0P=1dHHPHPHP6P[!#=A$FC9[[[X>4X<@WTQ0!~v$O3P3Q02Q0@'g1g@>1g4CO3b0W6WOWRWSWQWPXB4W?WZXV8XW7o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tmw : machine_state -> Model -> list (list byte) -> word
                -> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    (forall e, In e mmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
    (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
       twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
           (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
    (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
    tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    tmw ms' model bf cf bs cs ->
    tmw ms model bf cf bs cs.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)



End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

End FPX2.
(* [comment removed for export] *)
