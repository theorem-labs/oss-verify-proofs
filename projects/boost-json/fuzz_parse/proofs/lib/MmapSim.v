(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision. *)
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

(* The post-state of [munmap_spec]'s exact arm at 08b1429: the range cut out of
   both ledgers ([mmap_fixed_destroyed_next]) and its sparse backing forgotten. *)
Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.

Lemma iv_subtract_outside : forall (b s : word) lo hi,
  (0 < bv_unsigned s)%Z -> (lo < hi)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  iv_subtract b s lo hi = [(b, s)].
Proof.
  intros b s lo hi Hs Hlh Hd. unfold iv_subtract. cbv zeta.
  destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.max_l by lia.
    replace (bv_unsigned b + bv_unsigned s - bv_unsigned b)%Z
      with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_exact : forall l (a n : word),
  (0 < bv_unsigned n)%Z ->
  (forall b s, In (b, s) l -> (0 < bv_unsigned s)%Z) ->
  (forall b s, In (b, s) l -> b = a -> s = n) ->
  (forall b s, In (b, s) l -> b <> a ->
     (bv_unsigned b + bv_unsigned s <= bv_unsigned a
      \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b)%Z) ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  = map_remove l a.
Proof.
  induction l as [|[b s] r IH]; intros a n Hn Hpos Hu Hd; [reflexivity|].
  assert (IHr : maps_subtract r (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
                = map_remove r a).
  { apply IH; [exact Hn
              | intros b' s' H; apply (Hpos b' s'); right; exact H
              | intros b' s' H; apply (Hu b' s'); right; exact H
              | intros b' s' H; apply (Hd b' s'); right; exact H]. }
  cbn [maps_subtract]. rewrite IHr.
  unfold map_remove. cbn [List.filter fst]. fold (map_remove r a).
  destruct (bv_eqb b a) eqn:E; cbn [negb].
  - apply bv_eqb_eq in E. subst b.
    rewrite (Hu a s (or_introl eq_refl) eq_refl).
    unfold iv_subtract. cbv zeta.
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a))).
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a + bv_unsigned n))).
    reflexivity.
  - assert (Hne : b <> a) by (intros ->; rewrite bv_eqb_refl in E; discriminate).
    rewrite (iv_subtract_outside b s); [reflexivity | | lia |].
    + exact (Hpos b s (or_introl eq_refl)).
    + exact (Hd b s (or_introl eq_refl) Hne).
Qed.

Definition mmap_model : ltac2:(zQ "30!h9!jt2!jc>1a@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "h10!jtb!h9!jc!hm5!ho1!hg3!jt2!kg6!kh6!ki0!kie!kja!kk5!kl5!km4!kn3!ksf\1a@1$2@1$1#k0\1n@1$2@1$1#k0\1m$6@2$h0@8$7@1$e@1$0^1@3$3@2$5@1$2@1$1#k0@1$2@1$1#k0@4$4@1$2@1$1#k0@1$2@1$1#k0^3^2@1$b@1$0^1@1$d@1$0^1@1$f@1$0^1@1$8@1$0^1@1$a@1$0^1@1$c@1$0^1@1$9@1$0^1^1").

(* [comment removed for export] *)
Definition page_round_up : ltac2:(zQ "20!h9!jc>3len@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!h9!kte!it1!jc!itb\3len@1$3@1$0#k0@2$2@1$0#k0@1$1@2$4@1$0#k0^1").

(* [comment removed for export] *)
Definition place_ok : ltac2:(zQ "50!vc!h9!nb!kv1!jc>1h$3>1a@1$4@1$1#k0>1n$2$0") := ltac2:(zQ "h30!h9!kvb!jc!itb!lg2!hg3!nb!kv1!lg8!lh5!li2!kja!km4!jp1!lj1!lj8!ljf!lk6!it1\1h$7\1a@1$2@1$0#k0\1n$6@2$1@2$1@2$1@2$e@2$h1@2$3@1$0#k0^2$9Z@2$h0Z@2$3@1$0#k0^2@2$f@2$d@2$3@1$0#k0^2^1@1$8^3@3$a@3$4@2$5@1$2@1$0#k0@1$2@1$0#k0@1$c^3@1$b^3^2@2$h2@1$0#k0^1").

(* [comment removed for export] *)
Definition grant_ok : ltac2:(zQ "50!h9!jc!vc!nb!jt2>4hint@1$1@1$0#k0>1m$4>1a@1$1@1$0#k0>1n$3$2") := ltac2:(zQ "h60!h9!kvb!jtb!jc!itb!jp1!lj8!lg2!hg3!nb!jt2!lg8!lh5!li2!ll0!kie!kja!km4!lj1!ljf!lk6!it1\4hint@1$3@1$0#k0\1m$a\1a@1$3@1$0#k0\1n$9@2$1@2$1@2$1@2$1@2$h2@2$h4@2$4@1$0#k0^2$cZ@2$h3Z@2$4@1$0#k0^2@2$6@2$5@2$4@1$0#k0^2^1@1$b@1$2^3@3$d@3$7@2$8@1$3@1$0#k0@1$3@1$0#k0@1$h1@1$2^3@1$h0@1$2^3^2@2$h5@1$0#k0^1@2$6@2$5@1$e^3^1@1$f@1$2^3").

Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
  intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
    vm_forget_range, with_vm_backing, with_vmmaps.
  cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.

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
Lemma munmap_outcome_si : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model o <->
  (exists e, In e munmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
  \/ o = Ok (munmap_eff ms)
            (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) [].
Proof.
  intros segs ms x8 model o Hno (Hal & Hlen & Hnw & Hhas).
  rewrite (syscall_spec_215 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input.
  unfold munmap_eff, munmap_model, page_round_up.
  apply munmap_exact_outcome; [exact Hal | unfold w_is0; apply bv_eqb_neq; exact Hlen | exact Hnw |].
  unfold page_round_up in Hhas. exact Hhas.
Qed.

Lemma munmap_ok : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model Hno Ha. apply (munmap_outcome_si segs ms x8 model _ Hno Ha).
  right. reflexivity.
Qed.

Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
     eff = mkEffect (errno_ret e) [] [] /\ model' = model)
   \/ (eff = munmap_eff ms /\
       model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  apply (munmap_outcome_si segs ms x8 model _ Hno Ha) in Hspec.
  destruct Hspec as [(e & HIn & Hs) | Hs]; apply Ok_inj in Hs as (-> & -> & ->).
  - split; [reflexivity|]. left. exists e. auto.
  - split; [reflexivity|]. right. auto.
Qed.

Lemma munmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hno Ha Hspec.
  apply (munmap_outcome_si segs ms x8 model _ Hno Ha) in Hspec.
  destruct Hspec as [(e & _ & Hs) | Hs]; exact (Unmodeled_Ok _ _ _ Hs).
Qed.

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

Lemma sstep_munmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e munmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + right.
      match goal with
      | Hmat : materialize_model_accesses
          (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite Hh in H6
      | rewrite munmap_model_halted, Hh in H6 ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6
      | rewrite (m_killed_of_m_halted_none _ (eq_trans (munmap_model_halted _ _ _) Hh)) in H6 ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

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
