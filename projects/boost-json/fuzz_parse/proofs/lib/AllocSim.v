(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RelSpec SimInv ExitSim PropExec CatSim CatExec WallSim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AllocSim () := KReplay.lz_vm "#$,ZC47Corelib7Classes9Morphisms6Proper!sI-Program6Basics4flip!sg?Krespectful_per_obligation_1C4ELinuxProcessSemantics?!s<22Fs4path!t65?Rel!ss$!tF'Reflexive!tb?Grewrite_r!sd&_eq_dom!sZ?Ceq_!s]3!sV,4Init5Logic8eq_ind_r!uTN2Fs!sTK5State7PipeBufK!u$,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!uX#s2bv00I!u^19Datatypes6op!sL#!sH>4prod00K!sFA1!sF=list!sFD2!v\K3Run;apply_zerosc79OSSVerify!{Q#ofs:boost_json:fuzz_parse3lib8AllocSim4zmemC13~~~C!v\@;bv_unsignedC56Stdlib6ZArith6BinInt1Z3leb!sC=ad!s`?tbC!v8<andb!tmA7Z_to_bvK!xNC1I!{P72eq!xH4!s@,1!th<3orbC4!uJ&4Bool!s'$;orb_false_r!sb=fst!sC=snd!t#+5Lists4!s+#7ex!s2#b!sB-!tt#HFunc!uV#alExtens!s1$ityIf!s?+_e!s@0!|~G3!{s=bool!vQ/!}F4Z!{Q?!sd$2!x|<2lt!sB>e!x19or00!s\<6leb_gtI!}3A0K!vu'9micromega6VarMap1t02!sD@1!sD@3I!sD?0!sD6=RingM!s4'7Formula!tq87Env!sT#5PExpr!tv8!st:1!|>D2C!ss55Tauto8B!sl&!sH6:Z!t:+=Z!sT$CheckerC!u}<4fi!{Y-!sq8C!sq0_sound!x`>tb_ge!vME3!{pG1!~D6<and!~E+K!vE<G!w3'4!sJF8!w5<5eKind!{#=uni!{#9!se%4kin!#:<?!sf$!#5t,!~/60!}/83and!{$8!x$-;!wc%!#:5#!ts8!z^13Op205!#3EA1!smI3!#?uP8m_haltedI!s]P6VmMaps!u~#!s]O5Model!s\M<MemImageType7Segment!seM>Riscv!sE+=machine_s!tZ#00C!smY6ms_gpr!wu<3na!yp$!v7JMonad7outcome!#9YA!#AdO9sys_input!y%Mpecs<syscall_spec!ydQ6in_argC6!ttJSys2Mm4Mmap8brk!t@&!}'7iff!#CxXA!s~#resolu!#JN#ok!#D,&!|5Rvmmap!#IcQ6vm_brk!v-W9!u-#!#Fh#!sdW:!sd#un!u$#K!u$P=S!xk%Effect01!w;Y!u3$m!~J#!w3%K!{sY!#F;:x!}r#!|5+!#OW3?eq_p!#R[#!s,#xy!sR?Mtrans_co_!#Oc#v_impl_m!sE&!y;Rin_sysno!vSYE!se'_!}o+214!zl&!sxO7Rel!~$#@!~#/_!sra;!x@#!w^&!sm%!u[YD!#3$$0!uZ6I!zg_0!#V`D>iff_T!x]#!#@r#!t=Q7MemCopy!#S7=!#8F#!#;WRev!#:p#!#VBQeff_ret!wIY>!x9-_si!y'^6Ok_inj!~B'!#Ac:1C8!t'N3Lib2Nd:and_elimF2!tp&!skV9ex!sj%1!#8C&!y;C=eq!y:-!#3@>:!#^]+!s}E<eq_!#]wGJr!sL'!#]p%_r!s]GI!s],!s0,!#5SC@!sR0perK!#6n:!x1b4!#39^!#:j#ok_iff!#9D_2!{JX<Un!#:g#ed_Ok!y\3!{P/not!#:M75False00!tLP8PropExec:bv_eqb_neq!tK&5!#>LL7!#5z%5w_is0!#PI@lt!#PID!#[_<4negb!#4sP?page_round_up_Z!#@uV!#4y#!sn%ange!#^r@6bv_sub!#B,[grant!#D/;5!#JC#7Prelude6!w}%!xbY;!xb&!}T#!xc'!x%::!x%#ir!sP$!#bJ;!uk#!{aWD!wh2_mono!t_B6modulo!#UQE7!sj<7div_mo!#dl=div!sC=mul!#VT59SatDivModC!u?#d_nonneg!s,&!sWC!t`#!sW1!tM;=!t&#pos_b!#ZM?!sM$!su#!sM15!tI$8PreO!s/#1Z;!tH#0_r_ext!sL>!st#!sL&!#QN@!#^kD5Psatz!sOM6K!#XYL2!#R<?3!#40=3P!#XQG!tb&4!#4zD5!sIE!#]WF5!xP<9!x$#small!{OAadd!#9G76!#t<$!#[<H1!#6zP9!~8$size!x'N1!#7H[!#</#_n!{%#!tuP;vm_reserved!#GHQvm_!#T]T!t>#noac!s;#!s`Q<vm_start!#UE#!#PDPvm_limit!t@Ummap_base!saQ:vm_init_sp!#UsP!#a+&!z+R=!wP#_subtrac!#rb=app!yyWD!t,0!#>H$!#xmY?!#Y,+_keep!#F5^@!#>r+_query!#Dk&!zPPwith!#\i&!v:V@forget_!|W#!v6^D!}|1!uF/".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16optionhfbbv_unsignedk14boolk14Somek14andb46Stdlib6ZArith6BinInt1Zo53addo53lebo53ltbhf7Z_to_bvk14prodk14consk13nilk14pair37Corelib4Init5Logict42eq3h5LinuxProcessSemanticsfLinuxProcessSem3Runudbapply_zeros79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AllocSim4FPX1~~~~~~hi74zmemt42oro52leo52lt3h5LinuxProcessSemanticsfLinuxProcessSem5Statehne8m_haltedhne5Modelhne6VmMapshnebwith_vmmapshne8m_vmmapsk14list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehud7Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsiiddmachine_stateud9sys_inputhne8in_sysnoiid6ms_gprhne6in_argk14true5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapiq88brk_r_okiq8dwith_brk_nexthnedSyscallEffect3h5LinuxProcessSemanticsfLinuxProcessSem5Monadjga7outcomehne6vm_brkk13natt43andt42ext43iff01Zjga2Ok3h5LinuxProcessSemanticsfLinuxProcessSem5Specsjmdcsyscall_spechne7MemCopyhne5eventhne9mkEffectUiq8abrk_unmapsiq89brk_zeroshi79brk_modelhi7h1brk_resolution_okhne7eff_rett43notjga9Unmodeledhnefpage_round_up_Ziq8ebrk_page_rangeiq8abrk_grantshf6bv_subhne9page_sizeo56moduloo53subhnebregion_freeo53powhi78growablehnecmkVmMapsFullhneavm_init_sphne8vm_limithne7vm_mapshnecvm_mmap_basehnebvm_noaccesshnebvm_reservedhnecvm_start_brkiq8ebrk_model_next" s.   (* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zmem : ltac2:(zQ "31!h9!jc!l9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3mem~0>1b@1$1@1$0#k0>1l@1$1@1$0#k0~0") := ltac2:(zQ "b0!h9!jc!m2!n0!l9!n7!ne!pd!q3!q9!qf\3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8\1b@1$1@1$0#k0\1l@1$1@1$0#k0\1a@1$1@1$0#k0M3\0$3@1$4@1$1@1$0#8@2$6@2$8@2$2@1$0#k0^3@2$2@1$0#k0^1@2$9@2$2@1$0#k0^1@2$7@2$2@1$0#k0^3@2$2@1$0#k0^2@2$5@1$1@1$0#8@2$a@1$0#8Z@1^4^1").

Lemma apply_zeros_one : ltac2:(zQ "a2!h9!jc!l9!r9!s0!s7!sd!u8!hh9!hm7&>0@1$1@1$0#k0@1$2@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0>3mem~0>1b@1$1@1$0#k0>1l@1$1@1$0#k0@3$7~0@2$8^3@3$4~1@4$6@1$1@1$0#k0@1$1@1$0#k0^2^1@1$5~1@3$9^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##1lh01bh11ah21lh33memh41zp;1p;2p;4p;3p;6p;5p-1R0p10000p4p710R1p9P!s8%SR2!s:%p9P0P!s2$2!s3/31!s4%p10011!se&0p9!s6$ip4p70R2P1p8P2p1002Y!sI&3!s8'3ER4!s|&R5p8P2P4!sI&4!sI'49!s8&6p8P2g004iR7!s9&8!sY$0p8p1005G!t?0P!t3$P!s|'8P2P!sh$P!s[065!s[Rg006kj11Tg007Pj1:!s/$nj18Tg008Qj1;Tg0093j2K!s/$Sj49Tg00:3j1C!s/$Sj37Tg00;3j2=j3E!s2$kj3<j4FTg00<lj20Tg00=Vj22Tg00>3j24!s/$Pj26!s/$mj25Tg00?Kj2JTg00@1j2I!s/$Sj33!s/$mj2HTg00AGj2B!s/$dj1@TP7j6ATg00BCj3?!s/$`j3>Tg00C=j3D!s/$Yj5GTg00D[#1#1#1R7!s-%#:R0#8R2%:7R7#8R8#;R6[P2P6f2R41K22R5P2P2f1R3f0R1C9%C5R937'=A<431g00E@R:1004R;1001R<'21003R=,4;,6<'5R<P:P6P!sQ$`,J7,I8R8f4P3O1R7n0!zi$0020000P:P6f3R>,00R?/2=14?;,6='5P8P!sQ2536X0:!t$$<P8P>P1!su5R?,H6g00F>,B<%@<EAP:P6A?221,00R:/2=A>!s3%,4:!t7$X4!ue$P4P3C9=759R95D!tM6=36?eAE>91P>P4P3P1CF536eX12DGX22X02W3o"). Qed.

Lemma zmem_out : ltac2:(zQ "a0!h9!jc!m2!l9!u8!hmf!hm7!pd!hn4!hn9>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1b@1$1@1$0#k0>1l@1$1@1$0#k0>1a@1$1@1$0#k0>0@2$5@2$9@2$2@1$0#k0^1@2$2@1$0#k0^3@2$8@2$7@2$2@1$0#k0^3@2$2@1$0#k0^2@2$2@1$0#k0^1@3$4@1$3@1$1@1$0#8@4$6^5^4^3^2@1^5^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##7ah04__x1h14__x2h21bh31xh41yh52Hdh63memh71Eh81Hh97__arithh:4__ffh;8__varmaph<5__with=4__x3h>1ah?1lp;1p;2p;3p;4p;7p;8p;6g006kj17Tg007Pj1C!s/$nj1@Tg008Qj1GTg00<lj20Tg00F^j28Tg00>3j22Tg00G:j26!s/$VR0j2JTg00=Vj23!sL$Pj25!s/$mj29Tg00?Kj2DTg00@1j2Z!s/$Sj34Tg00H0j2VTg00:3j1U!s8$Pj1TTg00I0j2A!s/$Nj1O!s/$lj4<Tg00JJj1L!s/$hj1KTg00KSj2:Tg00L6j4>!s/$aj1ITg00MCj2H!tC$mj2B!s8$ej2FTg00NQj3MTg00O0j4N!s/$bj2ETg00PBj3P!s/$ej1QTg00QJj1RTg00;kj4S!s8$jj7YTg00RNj8XTg004ij6WTg00E@R1f0R2g00F>R334p=1f1R4g00S2R5g00SQR6P6g00T1R7P2g00TQFYp==f3R8P5P6P6P7f2R5P4P2GXp=?P1P3P8P!s7$EWp=;g00D[R9#7R:#7#7R;#7!s$$CR<#@R=%C;R;#@R>#GR?[10<2R@10<5RA'810<4RB,2A/6@'JP010<8R0,8B120A/6BP1P?f4RB,0<R@/3A12@0RC,5A'9g00E`RD,D;,Z>R>f5R;P5O1REn010!s#$20000=4?EP218A@g00U1REg00UORF1342#11845RG[1824RH1354#1[RI1385#1\G1V42P2n20!sx'1!sy$000X4EW3PI^4E^3EP2f6,0<RIP@f7RJPBO1RKP?g00UjRL#URM%TLRLPE1AE5RNP4%OEC<%LERO%KERPPE1:E9RQg00VV1:E:R:C>,=PRR%I6R6PRC?1HP7R7P2P5g00W=RR,B11F25=41RdAMED4CNRDb:b;b<X0EX1EPG\H^0E^1EP2f8RH,0<RGPIP8O3b9b6O3b810<;RR/30#1P1P?10<JRJ/2I,5R,92P>PHP;O1R;!vo4;X211B?KRH13I@R<P2C;b7W5P2O116CAPF15!v|$645RF[162415!vz%C15!vz$F1E!vz>X3EPC!v{'P@12IRRCPKP?PMPLPEPNP41AE8C<POPPPEAPEQ:g00W]%Q9,:E!v\%PP6PPC?P7P!v70X=E1224/651245/68[!vE%^=EP2PIPJPGP8O4!vC+2R@,5!vA'3JR/!v9$!v39P1P?P!sE>H19<3%R<C;15@C!vU/!v#-211000!s'$PB!|w%CSPBP4O154?eW5X>=X?=X2=W6o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_vmmaps_halted : ltac2:(zQ "80!hqc!l9!u8!h9!hr8!hs1!hsb!jc>1h$5>1m$4@3$2@1$1@1$7@1$3#k0@1$0@2$6^2^1@1$0^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##$?h01hh11mp;1p;2g006kj10Tg007Pj15!s/$nj12Tg008Qj11Tg00XDj14Tg00@mj23Tg00Y;g00Z2g00D[#0!s$-5#2#1f0#4'3W1W0o"). Qed.
Lemma with_vmmaps_vm : ltac2:(zQ "50!hs1!u8!hr8!hta!hsb>1h$0>1m$2@3$1$0@1$3@2$4^2^1^2").
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSim ()) ["FPX1"] "h01hh11mp;2g00@mj20Tg00Y;R0g00Z2f1,00W1W0o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_sys_input214 : ltac2:(zQ "80!h9!jc!hu6!u8!ii2!im4!in5!io1>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@1$7@3$6^3^2^1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##$Bh02msh14segsh22x8p;1p;2g00HPj14Tg006kj10Tg007Pj12!s/$nj11Tg00@mj23Tg00Zh#4g00[gg00D[#0!s$-2#1R0f0,30W2W0W1o"). Qed.

Lemma in_arg0_sys_input214 : ltac2:(zQ "90!h9!jc!hu6!u8!ii2!im4!iod!in5!ip7>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N0@2$6^2N0").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##$Rh02msh14segsh22x8p;1p;2g00HPj15Tg006kj10Tg007Pj12!s/$nj11Tg00\nj24Tg00@mj23Tg00Zh#5g00[gg00D[#0!s$-2#1R0f1g00]l'4,30W2W0W1o"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_resolution_ok : ltac2:(zQ "30!h9!jc!hr8>1m$2>3req@1$1@1$0#k0>1r@1$1@1$0#k0P") := ltac2:(zQ "70!h9!jc!n0!iq1!u8!hr8!itc\1m$5\3req@1$1@1$0#k0\1r@1$1@1$0#k0@3$4$2@3$6^3^2^1$3").

(* [comment removed for export] *)
Definition brk_model : ltac2:(zQ "30!h9!hr8!jc>3req@1$2@1$0#k0>1r@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "40!h9!jc!hr8!iu8\3req@1$1@1$0#k0\1r@1$1@1$0#k0\1m$2@3$3^1^3^2").

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma brk_outcome_si : ltac2:(zQ "he0!h9!jc!s7!iod!iv9!hu6!r9!u8!jj8!hta!jk3!jkd!jl3!jl9!jle!jm4!ii2!jm7!im4!in5!jpb!jqb!hr8!jr6!jrf!jsc!jta!ju7!jv4!m2>4segs@1$5$h0>2ms$h2>2x8@1$1@1$0#k0>5model$h6>1o@1$8$4>0@3$7$f@2$hd@1$0#k0^3+t6@2$e@3$h4@3$h3^6^5^4^3^2@2$d@1$1@1$0#k0\1r@1$1@1$0#k0@2$c@3$hc^4@2$3^6N0^1@3$7@1$8$4^3@4$h1$4@6$h8^1@1$2@2$6@1$1@1$0#k0@1$5@1$1@1$0#8@3$ha@2$3^6N0^1@1$a@1$9^4@2$h9^1@1$a@1$9^4@1$2$h5@1$2@2$6@1$1@1$0#k0$b@3$hb@2$3^6N0^1^4@1$2$h7").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##0Sh01bh11rh23Hnoh35lemmah45modelh52msh61oh74segsh82x8p;1p;2p;3p;4p;6p;9g00HPj1ITg006kj10Tg007Pj1<!s/$nj17Tg00^Kj1RTg00<lj2@Tg00Pej12Tg00_Cj1QTg00@Sj34!s8$aj39Tg00`Wj3CTg00aRj2FTg00bGj41Tg00cDR0j26Tg00\nj25!s:$]j3HTg0093j2?Tg00:3j13Tg00dkj1>Tg00ebj1=Tg00fWj3ATg00gUj2BTg00hTj6;Tg00iRj3DTg00jXj4ETg00UOj2:Tg00kPj2G!s/$jj2PTg00lVl9OTg00mPj1NTg00nGj3MTg004ij68Tg00oYj4LTg010ej4KTg011lj3JTg00Zh#Ig00[gg00D[R1#0#0#0R2!s-%#<R3#7R4g00Z2g013=R5#RR6g00U1R7f2R8,@3%21#0#2!s&$2#0#QR134f5R9f4R:f3R;39R<f1R=7C8g00]lR>,F<R?P<P8P=C1'6p-0R@P0g014;f6R0?99:RA?C;81FA>PAP;P8C1f0RB150>R0=H:BP5PB%<2#7#I,?4#3R2%>:#=RC9A0B1BBCg014l#3RCg015d!sJ%DE;AD0B:g016C#3R0CE946;':X14,G4REPE1P@EM9OW3!tm%P4P;1@3B=471X04PB%N<AM9:;E8CLP415:>R1PB!tr'/6EX04P1!uR&K!s0+1159>R>=H;!u0$P2%>;#=R29A>B1BB2PCP!tk$>B;P!td%8!td''6eP?AJ!tB$O2W2W6W4W8W5W7o"). Qed.

Lemma brk_ok_iff : ltac2:(zQ "hd0!h9!kga!hu6!s7!u8!jc!jl3!iod!hr8!iv9!jr6!r9!hta!jk3!jkd!jle!jm4!ii2!jm7!im4!in5!jpb!jqb!jrf!jsc!jta!ju7!jv4!m2>4segs@1$2$h1>2ms$h3>2x8@1$5@1$0#k0>5model$8>3eff$9>6model'$8>3evs@1$2$a>0@3$4$h0@2$hc@1$0#k0^5+t6@2$f@3$h5@3$h4^8^7^6^5@4$h2$9^4^3^2@2$6@3$4$9^4@6$h7@1$1^4@1$3@2$b@1$5@1$0#k0@1$2@1$5@1$0#8@3$h9@2$7^7N0@1$1^4@1$d@1$c^5@2$h8@1$1^4@1$d@1$c^5@1$3$h6@1$3@2$b@1$5@1$0#k0$e@2$6@3$4@1$2$a^2@1$3$a@2$6@3$hb^5@2$7^7N0@1$1^4@3$4$8^3@3$ha@2$7^7N0@1$1^4^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##C?h01Hh11rh23evsh36model'h43effh55lemmah64Heffh73Hnoh83Hokh92Hrh:1mh;5!sY$h<2msh=5nd_i1h>!s-$2h?4segsh@1xhA2x8p;1p;2p;3p;9p;6p;8p;4p;5p;=p;7g00HPj1LTg006kj1<Tg007Pj1R!s/$nj1NTg00<lj2gTg00Pej1FTg00_Cj1ZTg00@Sj30j1I!s;$aj3QTg00`Wj3OTg00^Kj1VTg0093j2TTg00:3j1DTg00gUj25Tg00iRj34Tg00kPj2ETg00cDR0j2Y!s1$]j3>Tg00UOR1j23Tg0179j18Tg00fWj3;!s`$jj2CTg00lVl9P!sJ$oj6XTg019:j8W!tw$mj2GTg01:<j4@Tg004ij6A!s8$Wj4UTg01;\j5fTg01<`j1eTg01=Pj4KTg01>7j1d!s/$fj4JTg01?]j3cTg00jXj1bj4^Tg01@Sl=_Tg01A@j4]!s/$Zj7\Tg00\nj2[Tg00dkj1`Tg00ebj1aTg00hTj6STg013=R2f2R3f1R4f0R5C^p=2g00]l,[5p=1%`5#ap=6f7R6f6R7f5R8f4R9f3R:3;P3P4P5ESp=7A>:34/35p=?P7P8P915:!sD&9026p==g00Z2R;A434570:p=91345,33p=:A0245p=HA0;45p=B!s-$!sA$Mg00Zh#Lg00[gg00D[R<#!s$$R=!s-%#RR>#NR?g016CR@#LRAg00U11g>9%F<#<#F!s&$F#<#Z30AQ678A2:34R<7O9P8%16R>P5%V2RBA29:3RCP5%R=#N#L,T?#DR=P>P5%68RD155Dg014l#DREg015d!sH%FG7A4>58%D@R@3230C?X1?,E?RG'Yp-0RHP0g014;f8R0?Q67?O8C%10RC=>75RIA289:P5P=PCP5%67RJ155JPEP!t#$C57;2@50BRK'3X1?RL,E?RMP5P9%89RNP=A;>NDPNPD!sY$=RDA0A3@ROA>8>NRPP:P>PNP8C9RN'33:R>P>1CH>M9PW5P6!ww%P<P5EXP>\GP:%8:R<P=%17RH%69RQ7;<P<PQ!t,%A0A4@P9PHP<P3!s+$9C9C?3:R<PM[P?PLP>PIPKP8%88RKP=A;CKJPKPJ!sf+:@RJP7PCPKP9!s+$7!sh%A2789P4P=f9RK#1RCP4%66R>154>!v,+46!v,%P2P6P3P=f:R>#1RLP3%60RH153H!sR%RHP7A4L30R3P8P@P5GW1H6H1B73A0A8@3:P1P0P:P=f;R3#1RH%6KRQ7;:P:!uc'P6PHP:PKC9A0A7@'3%8KRRP=f<RS#1RTPR%6>RU15RU!tC&V,HKA0A6@P>PTPRA4TR>RR,B0C?3:P5P>P8P=f=RW#1RX%63RY7;8P8PY!t?&2P7P=f>R8#1RZP7%6SR[157[!t,%P3f?R[#1P6PWC9R\A0A>@R]'3P4%84R^P=f@R_#1R`%68Ra7;^P^Pa!w?+3@RbP8P`P^PS!s+$8!w?%[X42P>PZP7PS!ua$K@'3P1P\P]P0P=P`P0Pa150!sp%7R]%8]R]P=A;`]aP]!t0'!t%$]!t%$]!t%%7:bP5PWfARb#1PKP[C9P;fBR]#1?4>_!wN$PSP=fD#1R_PS%6]R`15S`!t7&a%8aRaP=A;_a`PaP!s>%=R`A0A[@A>]_aR[A4_a]Ra7M43:[X3;A0AW@PAP@A0A5@A4_S]=M[a5:`X2A!yI$C#1R`P3%6bRa153!uM'[/H[A0A@@R_A>b`3R]A4`3bRS/BSRW'3R\'31G2[P_P\1GA@P]PWP>1G;SC@C@C@P[%8[R[!v6$[aP[!v6+bP`P[!v6$[Pb!v6%_eP8P5EAW0!s-+4P5O2n200100001012!s/$00W0P3!sJ80!sJ,b0W0X9ICUX1?P5DfX=GPDPOPPPNPMPAP@%86RM9>0L%80RN=4HKRP,B6A>3X5ROA2>K!#42$XP5PY155Y!}$'X53;2@RX50B'3!#5/$[[X2A%879>6CP7PLPMP0C9P;PPA2>4@=0BX,3O!sR%X3;P?!{s$5A2KR@RO!t5$TP5PU155!|F&A4T5>!~7%C?X1?PNA>KHNA20P@PNP=PHPNPQ15N!}O%7RF?2P@RP50BP41H0FPB%IBRF%eBPOA2V!t6$B^2AR0^:;R4^@2REP2P4%I2P;P0%I;PAPB%IAPFCKRNCKRQCKRHP2P4PQP;P0PNPAPBPF%dBCJCJCJ9cEH%b2PKPVP5PRPR1C;RP@P@1CA@M=_POPO1CBO!#6V$:1GBPO2C@C]P6!x'%W8P9P5EAX0JX6DP5F\X><C@O2W7W2X3;X42X;;WAW<W?o"). Qed.

Lemma brk_ok_intro : ltac2:(zQ "ha0!h9!jc!s7!iod!hu6!r9!hta!jk3!jkd!u8!jm4!ii2!jm7!im4!in5!jpb!jqb!hr8!iv9!jr6!jrf!jsc!jta!ju7!jv4!m2>4segs@1$4$b>2ms$d>2x8@1$1@1$0#k0>5model$h1>1r@1$1@1$0#k0>0@3$9$a@2$h9@1$0#k0^3+t6>0@3$h8^3@2$3^5N0^2@3$f@3$e^7^6^5^4@4$c$h2@6$h4^3@1$2@2$5@1$1@1$0#k0@1$4@1$1@1$0#8@3$h6@2$3^6N0^3@1$7@1$6^4@2$h5^3@1$7@1$6^4@1$2$h0@1$2@2$5@1$1@1$0#k0$8@3$h7@2$3^6N0^3^4@1$2$h3").
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSim ()) ["FPX1"] "h01Hh13Hnoh23Hokh35modelh42msh51rh64segsh72x8p;1p;2p;3p;6p;4p;8g00HPj1;Tg006kj10Tg007Pj1ETg007nj1DTg00<lj2ITg00Pej19Tg00_Cj1HTg00@Sj32Tg00\nj2:Tg00c]j38Tg00_aj3=Tg0093j2CTg00:3j17Tg00dkj1BTg00ebj1ATg00fWj36Tg00gUj24Tg00hTj63Tg00iRj35Tg00jXj4@Tg00`Wj3<Tg0179j1FTg00UOR0j21Tg01B_j8GTg00@mj2?Tg01:<j4>Tg00Zh#;g00[gg00D[R1#0#0#0R2#0#0#0#ER3#DR4g00Z2R5g00U1f2R6,I3%91#0#9#0#9#9#0#H32f4R1g00]lR3':f1R7586P0f6R0f5R8;=1f3R9g013=R:P6%E2#D#;,C4#7R21:83R;%B9#AR<766146<g014l#7R=g015d,C4#7R>E3R?A5;69R6g016CR@#7RAC@3<P9P21:03RB%B1#ARC769149CP=P>E3RD%FDREP2A6BEC14ECP=P>E352:%;@R@?2AARCA81BEA5B91RFA5BE1525'1'1'1RE[%F?RGP2A6;G<14G<P=P>E392:?A89;GA5;G99256'1,1C'1f7RG?=08P:PDPFPAC@7<1[R;f8?=G0P:P1P21:G3RG%B8#AR37611413P=P>E3A5G18PAC@7<8\EP0P8P1P9P?P6PAP7GGf0R6n2111000010120000000P;P6A2:DDA81B9RBA25FFR9'1R1,1C1?:DPCP11?@APBP9P71?5FC>C>C>PEeO1b0W2W1X54W3W7W4W6o"). Qed.

(* [comment removed for export] *)
Lemma brk_no_unmodeled : ltac2:(zQ "e0!h9!hu6!u8!kh5!jm4!ii2!khb!im4!in5!jpb!hr8!iv9!jc!m2>4segs@1$1$5>2ms$7>2x8@1$c@1$0#k0>5model$a>0@3$2$4@2$d@1$0#k0^2+t6@1$3@3$9@3$8^5^4^3^2@1$6$b").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##1=h01rh11Hh22H0h33Hnoh42_Hh55modelh62msh74segsh82x8p;1p;2p;3p;6p;4p;5g00HPj1DTg006kj10Tg007Pj1B!s/$nj1ATg00<lj2MTg00Pej1:Tg00_Cj1KTg00@Sj36!s8$aj3@Tg01Cfj1ETg00`Wj3=Tg00\nj27Tg00c]j3<Tg00^Kj1LTg0093j2CTg00:3j1;Tg00dkj15Tg00ebj14Tg00fWj31Tg00gUj23Tg00hTj62Tg00iRj38Tg00jXj49Tg00UOR0j2?Tg00kPj2>Tg017oj6GTg01D^j5FTg01:Wj4HTg01;\j5ITg01Efj1JTg00Zh#Dg00[gg00D[R1#0#0#0R2!s-%#BR3#AR4g00Z2g00U1f1R5,M3%:1#0#:!s&$:#0#K36f4R1f3R3f2R63@g013=R7#ER87=5R9P0f5R0?@13?=68f6R:g00]lR;'7R<f0R=5<1%L7R>P7P=%B2#A#D,C4#;R2%51#4R?91<=13=?g014l#;R?g015d!sJ%@E2A8<=1g016C#;R<C9768'?X04,>4RA[RB170;RC=<3=P7P=P2%53#4RD91C=13=DP?P!sk$C=3P<C996>!se+A@:01?=38RC[f7RD/7;RE=<0=RF!sq'0#4RG91E=13=G!sq'E=0!sq'RE!ss$RG,>4\CP0P1P3P6P8P5EGP5n20010!s#$12!s-%0PBP=P5O1PAP4PGg01F?RGPFPEPGP7P5P2f8/7;RG%5:#4RE715135E!tI'G5:!tI'P7P6P2f9/7;R;%5D#4R27161362!sT';6DP<P=DFW1X4FCHX04P=DIb1b2W1%J9eW3W5W8W6W7o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_zeros_grow : ltac2:(zQ "c0!h9!jc!m2!u8!ki8!hn9!hu6!r9!kh5!kjb!jta!qf>3req@1$1@1$0#k0>1r@1$1@1$0#k0>3old@1$1@1$0#k0>0@1$8@3$3@1$1@1$0#k0^3@2$b@1$0#k0Z>0@2$5Z@2$2@1$0#k0^2>0@2$5@2$2@1$0#k0^3@2$2@1$0#k0^4@3$3@1$6@2$7@1$1@1$0#k0@1$1@1$0#k0@3$a^6^5^4@2$9@1$4@2$2@1$0#k0^4@1$4@2$2@1$0#k0^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##55h04__x1h11bh21Hh37__arithh44__ffh58__varmaph65__with74__x2h81mh91nh:2E1h;2E2h<2E3h=3Hlth>4Holdh?4Hreqh@3oldhA1rhB3reqp;1p;2p;3p;4p;6p;7p;8g006kj15Tg007Pj1W!s/$nj1OTg00?Kj2FTg00@Sj33Tg01Efj1VTg00<lj21Tg00F^j22Tg01F\j4LTg01Gcj1;Tg00>Pj20Tg01H]j2DTg00:3j1CTg00HPj1BTg00I0j2ATg00JJj1U!s/$hj1TTg01I=j2PTg00KSj2?Tg00L6j4@!s/$aj1NTg00MCj2M!tp$mj2<!s8$ej2KTg00NQj3HTg00O0j4G!t:$Nj1I!s/$lj4JTg0093j2E!t:$`j1=!u&$mj26Tg01J>j17Tg01K<j28Tg004ij69Tg00fWj3QTg00Qjj7RTg00RNj8STg00E@R0f0R1g00W=R233p=4f1R3g00S2R4g00SQR5P5g00T1R6P1g00TQFRp=:f3R7P4P5P5P6f2R4P3P1GSp=>g00D[R8#5R9#5!s$+WR:#OR;g00E`R<,F:R=93;4#V11:3,2<11:411:7R>'2P:f5R?P=P4CL%;?g00F>R=530R@eP@g00U1R!s,$O1031#41243RA[12311043#4[RB1074#4\A1D31P1n20010!s#$12!s-%0X8@W9RAPB^8@^9@RBP1P<11:?RCg00UjRD#CRE%BDRD1A@3%U@RF%T@RGP@1P@<g00VVRH1?@8R8C@,:GRI%N5R5PIC>1MG6R6P1P41<021K14#4dAH@<3CGRIb4b5b6X0@12<112<3[^0@P1f6,1:RJf4RKO2b3O3b211:KRL,0<#4PAPBP1PJf7,1:RBPEPDP@1A@4P3%I@CJPFPGP@P8PH1?@9!t_%GP5PGC>P6P!tB,X7@12131234[^0@^7@P1f8R@,1:R:PBPKO3!tJ&0CJ#4P0P=1E;;RC#BRIP0PI%=110<B'610B:R6'6%7BRG%7:'8R:%CCRCn!w2'!w1$;3:X10P0P2!sd%=R=/61/66P:P!sQ2=3I!sR/16=2/61!sN<%7J/8G,<I10JBP1E910<JP3E9%;@P4E9b<b;b:AQ?K7%7>%7L'853IeW=W>W?X@;XA;WBo"). Qed.

(* [comment removed for export] *)
Lemma brk_grants_grow : ltac2:(zQ "e1!h9!jc!r9!m2!u8!hn9!s0!hu6!s7!sd!kh5!kkd!qf!klb&@2$2@1$1@1$0#k0@1$1@1$0#k0>3req@1$1@1$0#k0>1r@1$1@1$0#k0>3old@1$1@1$0#k0>0@1$a@3$4@1$1@1$0#k0^3@2$c@1$0#k0Z>0@2$5Z@2$3@1$0#k0^2>0@2$5@2$3@1$0#k0^3@2$3@1$0#k0^4@3$4@1$7~0@3$b^6^5^4@3$6~0@4$9@1$1@1$0#k0@1$1@1$0#k0^4@3$d@1$0#k0^5^4@1$8~0").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##5Zh04__x1h11bh21Hh37__arithh44__ffh58__varmaph65__with74__x2h81mh91nh:2E1h;2E2h<2E3h=3Hlth>4Holdh?4Hreqh@3oldhA1rhB3reqp;1p;2p;3p;4p;6p;7p;8g006kj16Tg007Pj1X!s/$nj1PTg00?Kj2GTg00@Sj33Tg01Efj1VTg00<lj21Tg00F^j22Tg01F\j4MTg01Gcj1;Tg00>Pj20Tg01H]j2ETg00:3j1DTg00HPj1CTg00I0j2BTg00JJj1U!s/$hj1TTg01I=j2QTg00KSj2?Tg00L6j4@!s/$aj1OTg00MCj2N!tp$mj2<!s8$ej2LTg00NQj3KTg00O0j4H!t:$Nj1I!s/$lj4JTg0093j2F!t:$`j1=!u&$mj25Tg01L?j37!sJ$Sj48!u3$Sj3:Tg004ij69!sJ$dj3RTg00Qjj7STg00RNj8WTg00E@R0f0R1g00W=R233p=4f1R3g00S2R4g00SQR5P5g00T1R6P1g00TQFSp=Af3R7P4P5P5P6f2R4P3P1GWp=>g00D[R8#6R9#6!s$+XR:#PR;g00E`R<,G:R=93;4#V11:3,2<11:411:7'2P:f5R>P=P4CM%;>g00F>R=530R?eP?g00U1R!s,$O1031#41243R@[12311043#4[RA1074#4\@1E31P1n20010!s#$12!s-%0X8?W9R@PA^8?^9?RAP1P<11:>RBg00UjRC#DRD%CCRC1B?3%U?RE%T?RFP?1Q?<g00VVRG1??8R8C@,AFRH%O5R5PHC>1NF6R6P1P41<021L14#4dAK?<3CHRHb4b5b6X0?12<112<3[^0?P1f6RI,1:RJf4RKO2b3O3b211:K,0<#4P@PAP1PJf7RA,1:R@PDPCP?1B?4P3%I?CJPEPFP?P8PG1??9!ta%FP5PFC>P6P!tD,X7?12131234[^0?^7?P1f8R?,1:RHP@PKO3!tJ&0BJ#4P0P=1F;;RB#CR6P0P6%=110<@'510@HRH'5P;P;PAA7:?AC8%DBRF5:BR5PFn!w<'!w;$;35X10P0P2!sl%=R=/51/5HP!sQ4=36!sR/15=2/51!sN=;P;PIA7:AIC8=:BF,<610J@P1E910<JP3E9%;?P4E9b<b;b:AR>K7!s\$7A7:K7!s\%536eW=W>W?X@;XA;WBo"). Qed.

Lemma brk_zeros_query : ltac2:(zQ "81!h9!jc!r9!hu6!s7!u8!jta!qf&@2$2@1$1@1$0#k0@1$1@1$0#k0>1r@1$1@1$0#k0>3old@1$1@1$0#k0@3$5@1$3~0@3$6@2$7@1$0#k0Z^2^1@1$4~0").
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSim ()) ["FPX1"] "h01bh13oldh21rp;1p;2p;3p;6g006kj10Tg007Pj1BTg007nj17Tg0093j26Tg00HPj1ATg01I`j1:Tg00<lj23Tg00>Pj22Tg00>mj21Tg01J>j14Tg01K<j28Tg00:3j19Tg00@Sj35Tg00@mj2@Tg00?Kj2?Tg01Mcj3;Tg01NPj2<Tg004ij6=Tg00fWj3>Tg00D[#0#0#0#0#0#0#BR0#7R1g00E@R2g00W=1611R3#AR4P2P4f0R5#:g00E`R6f1R7,30R8'2'1f2,30R9,28'1%48%49'8%93R3n0100000020000;53X021@431?06R6=;061<06E=A>675=543eX11W2o"). Qed.

Lemma brk_grants_query : ltac2:(zQ "81!h9!jc!r9!hu6!s7!u8!kkd!qf&@2$2@1$1@1$0#k0@1$1@1$0#k0>1r@1$1@1$0#k0>3old@1$1@1$0#k0@3$5@1$3~0@3$6@2$7@1$0#k0Z^2^1@1$4~0").
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSim ()) ["FPX1"] "h01bh13oldh21rp;1p;2p;3p;4p;6g006kj10Tg007Pj1CTg007nj16Tg0093j25Tg00HPj1BTg01I`j1<Tg00<lj21Tg00>Pj22Tg00>mj23Tg01L?j37Tg009Sj48Tg00:3j19Tg00:Sj3:Tg00@Sj34Tg00@mj2ATg00?Kj2@Tg01Mcj3=Tg01NPj2>Tg004ij6?Tg01Ldj3;Tg00D[#0#0#0#0#0#0#CR0#6R1g00E@R2g00W=1511R3#BR4P2P4f0R5#<g00E`R6f1R7,10R8'2'3f2R9,10,28'3P1P1P7A7097C8%93R95:3P9n0100000020000;49X021A491@06R6==061>06E?A;675=449eX11W2o"). Qed.

Lemma brk_zeros_keep : ltac2:(zQ "71!h9!jc!r9!hu6!s7!u8!jta&@2$2@1$1@1$0#k0@1$1@1$0#k0>3req@1$1@1$0#k0>3old@1$1@1$0#k0@3$5@1$3~0@3$6^2^1^1@1$4~0").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##'`h01bh13oldh23reqp;1p;2p;3p;6g006kj10Tg007Pj1B!s/$nj1<Tg0093j2;Tg00HPj1ATg01Gcj17Tg01I`j15Tg00<lj24Tg00>Pj22!s/$mj21Tg01J>j1:Tg01K<j28Tg00:3j19Tg00@Sj33!s/$mj2@Tg00QJj1?Tg004ij66Tg01OXj1=Tg00fWj3>Tg00D[#0!s$-BR0#<R1g00E@R2g00F>R31;11R4#AR5P2P5f2#7#5g00E`R6f1R7,40R8'2'1f0R9'1%:8R8/88R8%94R4n010!s#$20000;34X02P2P3P2P5P9P8P!sH2=354X021@54%77#51409R0,26'1R6/13%?6E61200%=0E6A>799=354eX11W2o"). Qed.

Lemma brk_grants_keep : ltac2:(zQ "71!h9!jc!r9!hu6!s7!u8!kkd&@2$2@1$1@1$0#k0@1$1@1$0#k0>3req@1$1@1$0#k0>3old@1$1@1$0#k0@3$5@1$3~0@3$6^2^1^1@1$4~0").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##'th01bh13oldh23reqp;1p;2p;3p;4p;6g006kj10Tg007Pj1C!s/$nj1<Tg0093j2;Tg00HPj1BTg01Gcj16Tg01I`j17Tg00<lj24Tg00>Pj22!s/$mj21Tg01L?j3:!sn$Sj48Tg00:3j19!s/$Sj3ATg00@Sj33!s/$mj2@Tg00QJj1>Tg004ij65Tg01OXj1?!sw$dj3=Tg00D[#0!s$-CR0#<R1g00E@R2g00F>R31;11R4#BR5P2P5f2#6#7g00E`R6f1R7,40'2'1f0R8'1P1P1P7A:077C8%94R95A4R4P9n010!s#$20000;39X02P2P3P2P5P8P!sH4=359X021@59%67#71408R0,26'1R6/13%>6E51200%?0E5A=788=359eX11W2o"). Qed.

(* [comment removed for export] *)
Lemma brk_unmaps_keep : ltac2:(zQ "71!h9!jc!r9!hu6!s7!u8!jsc&@2$2@1$1@1$0#k0@1$1@1$0#k0>3old@1$1@1$0#k0@3$5@1$3~0@2$6^1^1@1$4~0").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##,+p'0h01Eh11bi001bh23oldp;1p;2p;3p;4p;6g006kj11Tg007Pj1B!s/$nj1;Tg00<lj22Tg00>Pj23Tg00@mj27!s/$Sj30Tg0093j2:Tg00HPj19Tg01J>j14Tg01K<j25Tg00:3j18Tg00?Kj26Tg01P<j2A!se$Sj4@!sJ$Sj3?Tg01OXj1<Tg004ij6=Tg00gUj2>Tg00D[#1!s$-BR0#;R1g00E`R2f0R3,20R4'3R5g00E@R61763f1R7,20,32=063P6f!sL$8!s6&1:11R9#9R:P6P:P7f4,20#4R;/5;%89R<n010!s#$20000;0<]0P7f2!sx%R2g00W=506P6g00F>R7!sm$3P1P1160;1A;;,60C@=?9<P!ss2=0:<X1617:<R9%48R8/38%<8E=1588=0:<eW0A0627P9W0n01!sc%20100P3O1b0b1!t=$5%44R4/54!t07e1>33!ss%2o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_unmaps_grow : ltac2:(zQ "91!h9!jc!r9!m2!hu6!s7!u8!jsc!hn4&@2$2@1$1@1$0#k0@1$1@1$0#k0>1r@1$1@1$0#k0>3old@1$1@1$0#k0>0@2$8@2$3@1$0#k0^1@2$3@1$0#k0^2@3$6@1$4~0@2$7^3^2@1$5~0").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##/Ap'0h02E0h11bi001bh21xh31yh41Eh51Hh62H0h73oldh81rp;1p;2p;3p;4p;6g006kj13Tg007Pj1E!s/$nj1=Tg00<lj22Tg00G:j26Tg00>Pj20Tg00@mj29!s/$Sj31Tg0093j2<Tg00HPj1;Tg01J>j14Tg01K<j27Tg00:3j1:Tg00Obj2DTg01PYj3CTg00?Kj28!s8$<j2@!sw$Sj4?!s\$Sj3>Tg004ij6ATg00gUj2BTg00E@R0f0R1g00F>R231p=5g00D[#3!s$-ER3#=R41231f1R5,23R6'6g00E`R7/06R8P01901f2R9,23R:,07=101P0f4R;,23R<!s8&1<44R=#;R>P0P>P5f6,23R?#4R@f!s~$A#4RB'7RC%:=RDn010!s#$20000;1D]0P5f3RE,23,07R7g00W=510g00U1RFg00UO1051#51659RG[16151095#5[RH10E9#5\G1D51P1n20!t,'1!t-$000X3FW2PH^3F^2FP1P@PBACA?;O3b6%4<,0B#5P0P2!u4$1P4P4f7,23#4R2,831@@2,83C?=>=DP!u42=1>DX1019>DR=10@BP1EAA1>CDeb4W0%57P=W0n01!s[%20100P1O1b0b1!t=$8%4:%46'7!t$7e1B95!s/$W5X74W8o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned : ltac2:(zQ "60!jm4!u8!ki8!km4!hn4!kn1>1z$0>0@2$4Z^1>0@3$1$0@2$5^2$3Z@3$1$0@1$2^3^3").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##<fh07__arithh14__ffh28__varmaph35__with44__x1h54__x2h64__x3h71zh81Hh92H0h:2H1h;2H2h<2H3h=6__sat0h>!s/%1h?1qh@1rhA4HdivhB4HmodhC2Hzp;2p;1p;6p;3p;4p;7p;8g01Qij24Tg006kj1>Tg00_Cj1GTg00:3j1`Tg00HPj1\Tg00INj1[Tg00JJj1Z!s/$hj1XTg01I=j2?Tg01RIj6nTg00MCj2mTg00@mj2d!s8$ej2c!s8$Sj3DTg00NQj3_Tg00O0j4^!se$mj3]j2OTg01SNj21!s/$kj23Tg00>3j22Tg01THj3STg01U9j3QTg01Efj1Y!s8$jj2MTg00F^j26Tg00UOj28Tg01VQj2LTg00G:j2BTg01W8j2K!s/$^j2PTg01XDj1J!s/$cj2HTg01YLj3ATg01Z5j2W!s/$aj1pTg01[?j2o!s/$`j3U!vS$Sj3N!vJ$0j2R!s/$lj4lTg00Laj1fTg00KSj2CTg01\Ij3FTg00Pej1E!s/$Bj3@!sA$lj3bTg01P<j2V!se$6j4ITg01]Oj7aTg01^3j3eTg004ij6T!s8$Vj4gTg01_7j6hTg01J>j1iTg00Qjj7jTg00RNj8kTg00E`R0f0R1'Bp=5g00U1R2?D10p=9%>1#>p=<P2f1R3g01_SP1CIp==P3g00S2R4g00SQR5P5g00T1R6P1g00TQFjp=7AD231p=0f3R7P4P5P5P6f2R8P3P1Gkp=;%E1#Ep=:%51g01`:,43#9g00D[R9#>R:#>#<!s$+GR;g00UjR<#`R=%\<R>%[2R?%Z2R@%X2RA!t2'1?2;RB1?20RC'=,7AEnRD1mA6REP1P8g00E@RFg00W=RG'd1c18=DFGdA_203C^RGb1b2b3%9;RFg01F?[RHP1b0RI5]8118;,3;148;'2,08AS7;8%5;RJf4RK/4;#5[AQK;7f5RL/1;RM#5\J1OL;%YFRNf6RO11O;RP!sk$O;'2'0[1MO;160;RQf7RR/4;RS#516S;'8[1LR;16;0RTf8RU/4;RV,6;1BV0'8[1KU;f9RW/1;#9\F1PW;f:RX/4;/0X\F11X;RYP2f;RZ/4;R[P2g00]lR\#JR]#J,H2R^1H2]R]1H2\R\5A25A2g01a2R_'W%p9,o2R`=U2^AU2`]=A2\5A2/W_=N<=5N<R<P>P21R28P31R27ClR_P@PAPAPD%f5RD1C2:R:1C29R\9F2B%E9R`,C2R]5@2!wd$C;R^PDPA1=]C,7AR]PD%:`#:!s$&GR`,?2RaAF2\B5@2A@2:B%G9R9,?25b!sj'C;PEP!x$&X42X52X6213;3/27,08\HRH%97Rb138;,2`127;/V9Rc'0[[^42^52^62P1P3f=P8PRPZO5b0b@b?b<b;b:b9b8b=b>117;/3;,2`/0cP211K;Rc!s7%Rd111;/3;/0LX72P211`;Re/2c131!s;+P0121M!sL+ASK;714L;#5\JAQL;K%5P\J1OO;11R;,3;/2S,0R\N1MR;%5V16V;'8\Q1LU;14W;RU!x|$U0'8\T1KW;%9Y\F1PX;10[Z\F11Z;P2f<!xo$P2P<P>P!wh%!w;$P]PDA@2C\=F2B/=:!vj>208!u,$7\b\H!vQ1>!vQ?PeP=P>P?!tC$!}Y&P2PCg00W]PaCI,7AP2Pag00VVPB!s6$Fa!tP,%5`16`;'8P1b09e`;ET11d;P`PcP;PICgET12K;/V9P1Ehb8bA%i8/08eWBWCX72o"). Qed.

Lemma page_round_up_Z_bounds : ltac2:(zQ "70!hn4!ki8!jl3!jm4!km4!pd!kna>1z$3>0@2$0Z^1@2$2@2$0^2@1$1^2@2$0@1$1^2@2$6@2$5^2$4+1").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##:Oh07__arithh14__ffh28__varmaph35__with44__x1h54__x2h64__x3h71Hh82H0h92H1h:2H2h;2H3h<2H4h=2H5h>4Hdivh?4Hmodh@2HzhA6__sat0hB!s/%1hC1qhD1rhE1zp;1p;2p;4p;6p;3p;7p;8g006kj1BTg00_Cj1ETg00:3j1_Tg00HPj1[Tg00INj1XTg00JJj1W!s/$hj1UTg01I=j2CTg00L6j48Tg01RIj6lTg00MCj2iTg00@mj2c!s8$ej2^!s8$Sj35Tg00NQj3\Tg00O0j4Z!se$mj3Yj2RTg01SNj2@!s/$kj29Tg01Qij23Tg00>3j2>Tg00F^j26Tg01Ujj3Vj2OTg00UOR0j27Tg01THj2T!sF$9j2STg01Efj1PTg01VQj2NTg00G:j24Tg01W8j2M!s/$^j2QTg01XDj1<!s/$cj2=Tg01Zaj1LTg01[?j2k!s/$`j3jTg01YLj3A!sJ$5j2K!vj$Sj3F!va$0j2G!s/$lj4b!vO$aj1aTg00Pej1`Tg00KSj2D!s8$Bj3ITg01\lj3]!s/$Ij3JTg01J>j1dTg01P<j2eTg00Qjj7fTg01]Oj7gTg00RNj8hTg00E`R1f0R2'4p=1%B2#Bp=;f2R3f1R4'>/e2p=0P4g00S2R5g00SQR6P6g00T1R7P2g00TQFfp=2g00U1R8!sR$W]P2C8p=?P3P5P6P6P7P4P2Fgp=Hf3R9!s;+3P4P2Ghp=:%12R:g00D[R;#BR<#B#;!s$+ER=%E;R>504R?g00UjR@#_RA%[@RB%X8RC%W8RD%U8RE!t&+81C8=R5g01_SRF1C81RGC8,2EElRH1iE7R7P2P3g00E@RIg00W=RJ'c1^23=5IJdA\814CZRJb1b2b3A58=1RIg01F?[RKP2b07Y=1@?=,9=13?='>958?A03=>R?PAPBPCPDP8PGg00VVRCP5!tL$RLP7P!sz&161=RM!sq$V!sj$RN#116N='7A09=>RN/T=%1N%1=ROf5RP?0=>RQ/3=#1[[f4RR!s7$S/S=%1Sf6RS!s6$T/@=RU#1\O[1RQ=%PI19=U13T!tr%T[1OT=f7!sR&3!sR$16U='7\M1NT=16=1f8!sE-,6=14U1'7[1MT=f9RT!sC$U/@==581\I1QU=f:RU!s=$1/3!s='@1=P8f;R1?0=>/3=P8P0P:162=f=R:193=R0'4A0:=>,40'7PT%13RT169=R0g00]lR:#<#<RI#<RQ#<,=8%L;,k81=8IRI5j81=8:R:5A85A8g01a2RO'K1=8QAA8I:5A8/KO=F@A5F@PBP81G83P41G89CbPDPEPEPL%a6R6%`;,D8RL,?G,2EP8PLP!wx'5HEC:P6!sS$HP6P81D8;R;=I851C8>5]8RHPF1D8<R<9J85=I8L!s_$!s\%1?G;,2EP6AJ8<5R<,?;,2E1?<H!t&'C:C:!y',X48X58X68%19/70\M19=9/>R958?\K19R=RR,4914RN'7\T[[^48^58^68P2PPPSfAPUP1f@O6b0W=W<P4P2O2n20010!s#$12!s/&bDbCb;b:b9b8b7bAbBb?b>%d4R2,44g01`:=04>,42'7eW@XE8o"). Qed.

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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition growable : ltac2:(zQ "50!h9!jc!jm4!hu6!r9>8reserved@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0>3lim$2>3top$2>1t@1$1@1$0#k0>1r@1$1@1$0#k0P") := ltac2:(zQ "h72!h9!m2!ki8!jc!pd!n0!qf!u8!ne!iq1!jl3!jm4!q3!hu6!r9!kh5!hmf!km4!ko0!hn9!q9!kof!kna&@2$4@2$1@1$0#k0^1@2$1@1$0#k0^2&@1$2~0\8reserved@1$d@2$e@1$3@1$0#k0@1$3@1$0#k0\3lim$b\3top$b\1t@1$3@1$0#k0\1r@1$3@1$0#k0@2$a@1$f@3$7@1$3@1$0#k0^1@2$6@1$0#k0Z@2$a@2$h3~0@2$h5+2+k0@2$h0@3$7@1$3@1$0#k0^2@2$6@1$0#k0Z@3$7$5@2$8M5\0$5$5@2$h4@1$2@2$1@1$0#k0^1~1@2$8@2$c~1^3@3$h2^5@2$6@1$0#k0@1$2@2$1@1$0#k0^1@2$6@1$0#k0@2$h6@2$4~1$h1@1$2@2$1@1$0#k0^1$9@2$c@2$1@1$0#k0^2^4$9").

(* [comment removed for export] *)
Definition T1 : ltac2:(zQ "50!h9!jc!hu6!r9!jm4>8reserved@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0>3lim$4>3top$4>1t@1$1@1$0#k0>4bufs@1$2@1$2@1$1@1$0#8>1r@1$1@1$0#k0>0@2$3@1$2@1$2@1$1@1$0#8@1$1@1$0#k0P") := ltac2:(zQ "h11!h9!jc!hu6!r9!u8!qf!hmf!sd!jl3!jm4!m2!s7!kh5!kp5!pd!hn4!kof&@2$3@1$2@1$2@1$1@1$0#8@1$1@1$0#k0\8reserved@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0\3lim$9\3top$9\1t@1$1@1$0#k0\4bufs@1$2@1$2@1$1@1$0#8\1r@1$1@1$0#k0\1o~0@2$6@2$8@3$4~0^1@4$7@1$2@1$2@1$1@1$0#8@1$1@1$0#k0@1$b@1$2@1$1@1$0#8@2$5@1$0#k0+4@2$6@3$4@1$1@1$0#k0^2@2$5@1$0#k0Z@2$6@2$f@2$h0+2+k0@2$e@2$a@1$0#k0^2@2$a@1$0#k0^4@1$c@3$4@1$1@1$0#k0^4@2$5@1$0#k0Z@2$8@5$d^7^6^5^4^2@3$4~0^1@4$7@1$2@1$2@1$1@1$0#8@1$1@1$0#k0^3@2$5@1$0#k0Z").

(* [comment removed for export] *)
Definition T2 : ltac2:(zQ "40!h9!jc!hu6!r9>4want@1$1@1$0#k0>4bufs@1$2@1$2@1$1@1$0#8>2r2@1$1@1$0#k0>0@2$3@1$2@1$2@1$1@1$0#8@1$1@1$0#k0P") := ltac2:(zQ "b1!h9!jc!hu6!u8!r9!sd!jl3!qf!s7!kh5!hmf&@2$4@1$2@1$2@1$1@1$0#8@1$1@1$0#k0\4want@1$1@1$0#k0\4bufs@1$2@1$2@1$1@1$0#8\2r2@1$1@1$0#k0\1o~0@2$a@2$6@3$3@1$1@1$0#k0^2^4@3$3~0^1@4$5@1$2@1$2@1$1@1$0#8@1$1@1$0#k0^3@2$7@1$0#k0Z@2$6@1$9@3$3@1$1@1$0#k0^2^4@3$3~0^1@4$5@1$2@1$2@1$1@1$0#8@1$1@1$0#k0@1$8@1$2@1$1@1$0#8@2$7@1$0#k0+4").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_model_next_query : ltac2:(zQ "f0!h9!u8!hs1!jc!kq1!jk3!kr1!krf!ksb!kt6!ku6!kv5!lg4!lh4!qf>1h$2>1r@1$3@1$0#k0>0@3$1@1$3@1$0#k0^1@1$5^2@3$1$2@3$d^3@2$e@1$0#k0Z^2@8$4@1$b^3@1$8^3@1$a^3@1$c^3^2@1$7^3@1$9^3@1$6^3").
Proof.
ltac2:(KReplay.run1z (kr_t_AllocSim ()) ["FPX1"] "##/{h01bh11lh21rh31Hh41hp;1p;3p;2p;8p;6g006kj12Tg007Pj1P!s/$nj1JTg00ebj15Tg00@Sj3DTg00?Kj2OTg01a^j3ATg01baj1=Tg01c[j1:Tg01dQj1BTg01eKj1?Tg01fFj17Tg01g=j19Tg01h8j1CTg01i1j80Tg0093j2NTg00HPj1MTg00<lj2@Tg00>Pj26!s/$mj2>!s\$hj3LTg01Ldj3<Tg01jdj34Tg00gUj28Tg01kAj2;Tg00:3j1I!u<$mj2HTg01lJj1GTg004ij63Tg01mVj2KTg00QJj1FTg01OXj1ETg00Y;R0f1R1f0R23Dp=1g00D[#2!s$-PR3#JR4%519D42P4f2R5#5R6f3R7g00E`R8,O3R9;A2%=7R:%:7R;%B7R<%?7R=P2%77R>%97R?%C7R@G0'1X24g00E@RAg00F>RBP:PA1N44R4#MRC%57R7,@3RD,68/>2AL;DDRDA<977=44;REn010!s#$200001877,;<RFP=P7P>P?P@G0P:P;P<!s8/RG'1X0APAP!t>$PCP2PDP!sr2P!sk0/1GX0APC%I4RAP:A442;!sH51CPCP!sE%A;1;<2!sG5%=5%:5%B5%?5P6%75%95%C5G0RC,H01866%G6E3A<9661K66E31@36R3,68R8/>B%F8E31633%E3E3AA596/1CeP1P2E3W3W2X40o"). Qed.

Lemma brk_model_query : ltac2:(zQ "h10!hta!h9!u8!hr8!jc!kq1!jk3!kr1!krf!ksb!kt6!ku6!kv5!lg4!hsb!ju7!qf>1r@1$4@1$1#k0>1m$3>0@3$2@1$4@1$1#k0^2@1$6@1$0^1@3$2$3@3$f@2$h0@1$1#k0Z^3^2@2$e@8$5@1$c@1$0^2@1$9@1$0^2@1$b@1$0^2@1$d@1$0^2^3@1$8@1$0^2@1$a@1$0^2@1$7@1$0^2^2").
Proof.
ltac2:(KReplay.run1 (kr_t_AllocSim ()) ["FPX1"] "h01rh11Hh21lh31mh41vp;1p;3p;2p;8p;6g006kj11Tg007Pj1KTg007nj1ETg00dkj14Tg00ebj17Tg00@Sj3>Tg00?Kj2ITg00iRj3?Tg01baj1=Tg01c[j1;Tg01dQj18Tg01eKj19Tg01fFj1:Tg01g=j1BTg01h8j1ATg01i1j86Tg01ncj20Tg0093j2JTg00HPj1HTg00:3j1FTg01a^j3<Tg01o]j23Tg00@mj2@Tg020bj3DTg004ij65Tg00gUj2CTg01lJj1GTg00Z2R0f1R1f0R23>p=2g00D[#1#1#1#1#1#1#KR3#ER4%42#79>41P4%41R5#7R6g00E`,I3R3f2R77?2%47R8#=R9%;8R:%88R;%98R<P2%:8R=%B8R>%A8R?G6/07'2X041J44R@#HRA%F@R@%78RB9<83/07,32P9P:P;P<PBP=P>P?G6/07R?'2X2Ag00Y;RA%=5%;5%85%95P6%:5%B5%A5G6R>1027/2?X4A10>1R>,@0A<536RA1@469D56E510A1RA,3@/2>e1C66R@%G6E513@A/2>eA?361/2>eP7P2E5W1X30W0o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hu6!ii2@1$0$1").

Inductive to_outcomes : machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tou_wexit : forall ms model bufs code (U : (list (list byte) * word) -> Prop),
    fd1chan model ->
    to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
    bufs_modeled bufs ->
    (forall o, U o <-> o = (bufs, code)) ->
    to_outcomes ms model U
| tou_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_outcomes ms' model U ->
    to_outcomes ms model U
| tou_brk : forall ms model x8
    (T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
    (U : (list (list byte) * word) -> Prop),
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 214%Z ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       to_outcomes (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_outcomes ms model U.

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


(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
