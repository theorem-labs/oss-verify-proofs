(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import CatSim LazyRestrict.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive dsteps : config -> config -> Prop :=
| ds_refl : forall c, dsteps c c
| ds_step : forall ms model ms' model' c3,
    m_halted model = None ->
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    dsteps (mkCfg ms' model') c3 ->
    dsteps (mkCfg ms model) c3.

Lemma dsteps_trans : forall c1 c2 c3, dsteps c1 c2 -> dsteps c2 c3 -> dsteps c1 c3.
Proof.
  intros c1 c2 c3 H; induction H; [auto|].
  intros H23. eapply ds_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma sstep_account_inv : forall ms model ms' model' e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  sstep segs (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms' model').
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.event); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.step_to); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending); constr:(@Corelib.Init.Datatypes.None); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result); constr:(@Corelib.Init.Datatypes.prod); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mi_account_step); constr:(segs); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sstep); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.config); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.nil); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.SNext); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_halted); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_refl); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineFault); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.SError); constr:(@Corelib.Init.Logic.eq_trans); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.False_ind); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineUnmodeled); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect); constr:(@Corelib.Init.Datatypes.Some); constr:(@LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.sys_input); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Ok); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_killed); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.cons); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.ExitEv); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_fs); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.KillEv); constr:(@LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled)|] [|@c; @cfg_ms; @cfg_model; @e0; @H1; @H0; @H; @H4; @H3; @m; @l; @s; @Hss; @e; @st; @p; @result; @H5; @Hacc; @ms'; @model'; @H2; @model'0; @ms'0; @model0; @ms0; @Heq; @H6; @o; @H7; @evs; @model''; @eff; @x8; @code; @sig; @ms; @model; @Hsvc|] "#3R#[$8###b#_#^#n#(#'#&#%#a#)#$#~#s#<#;#>#:#=#@#*#6#4#I#D#O$*#?#A#P#R#9#+#5#J#F#7#Q#B#G#H#8#K$%#,#E#3#L#N#0#-#2#S#C#/#.#M#T#V#U#W#1$'#k#X#d#[$&#l#y#j#c#Y#q#z#`#h#f#e#u#{#}$)#Z$9#r#v#t#w$##p#o#i$+$,$5$4#m$$$-$.$7#x$3$6$8$2$1$0$/#g#|$(D#j&#x%#y$#z%#{$#|)#l'#}'#~%$#$#m)$$%$%&#h)$&&$'&$(&#m*$)'$*&$+'$,$$-)$.$$/%$0%$1%$2$$3$$4%$5$$6%$7%US^LAS_A#A#A#A#A#US`#USa#UST#,HUSY%#%$#VSWFEUSR#3GMH*FEIJ+&##&%#$S'M)G#JK$SISJ#PJ##9JS?#DJS?USbL#<SJ#$SDSI%##DSE#&&#k##)#k##+#k##-#'K#<#:,I#>#<3GHI*FEJK+=##=%#$MH$S2S<#P$##s#/6S(%&#D#S($S?S3$QR#P$#nP#$#$EC#$%#%#&Cj#'P#$SES?$S%Q9PE%$#C#ES?QnP#$#$FC#$%#%#&Nj#'P#$SJSE$S#S%9PF%$#N#FSJS##FSIS.#FSDS&#ESPS/#s#Ds#+S.$SFSP%##D#S.'S)#s#@#s#>3GHS(*FES4S)+s#?##s#?%##s#NS+s#5$S6S@%##DSH#&&#k#((#k#)s#/#k#*.#k#+1#k#,5#k##7#j#-F##ESDS&#s#[s#BS&$SASF%##D#S&,S:#s#W#s#U3GS;I*FES(S4+s#V##s#V%##s#eS@s#L$S:S6%##DS+#&&#k#((#k#)-#k#*s#I#k#+1#k#,5#j#-E#$S)SA%##D#S/'S6#s#k#s#i,S;#s#m#s#k3GS*S;*FES7S(+s#l##s#l%##s#{Is#b$S;S:%##DS@#&&#k#((#k#)-#k#*0#k#+3#j#.s$(#$S4S)%#'S:#s$##s#},S*#s$%#s$#3GS5S**FES<S7+s$$##s$$%##s$3s#vs#v$S*S;%##DJ#&&#k#((#k#)-#k#*0#j#/D#$S=S5)G#CS6$S$S2%#$S5S*%##D%#&2#k#0)#j#1s$E#)G(s$-S@%s#x$SBS=)G#s$0C$RS$%#%2#D$#&=#k#0(#j#2D#)G7s$8,3GSBS=*FERS$+s$G##s$GC#j#-s$H#*FES5S*+s$K#-s$K)%K#S@*FES$S2+s$N##s$N&#*FES=S5+s$Q#*FES%Q+s$S##s$SN#%s$&$SCSK%##D%#&s#5#k##(##s$Z,6*FESBS=+s$]#*FEQR+s$_##s$_%#nSW%FE$#3EC#$%#-#-CnSR$s$b$#-EC#&$#4##SK#SKj#1s$b#*FESKSB+s$e#9s$eE%#5C#ESBQnSW%FE$#3FC#$%#-#-NnSR$s$i$#-FC#&$#4##S,#S,j#1s$i#*FESCSK+s$l#*FES#S%+s$n#9s$nF'%#N#FSCS##FS,S.#FS0S&#ES8S/$SHS9%#$NS1%##D%#&s#U#k##)#j#-F##ES0S&$S+SH%#$S+C%##D%#&s#^#j#-E#3GSMSN*FECSG+s%*##s%*%#*FENSL+s%-#*FES@S++s%/##s%/%##Ds$Ls$L&s#j#k#5%#k#6+#j#7F#3GSNSL*FESHS1+s%8##s%8%#*FES+SG+s%;#*FES+SH+s%=##s%=%#3GSSSO*FES6C+s%A##s%A%#*FES:N+s%D#*FES:S6+s%F##s%F%##Ds$6s$6&s$%#k#5%#k#6+#j#8E#3GSOSM#s%M#A*FES6S@+s%P##s%P###Ds$Vs$VBs%`s%GBDs$XXScs$1%$#j#5'#j#6+#\SXES+.#SLJNCj#5=#j#6s###\SXFSHs#(#SGJSCS30ES9s#7#S1Cl#+Cs#H#j#,s#@#0FS/s#B#S8Cl#,Cs#L#j#)s#N#U#Cl#)s#Rs#Q#U#Cl#)s#]s#\#j#*s#d#U#Cj#*s#k#nSZ%s%hs#v%#-##s#mC#$###s%iCs#i%s%B$SKSB%##D%#&s$K#k##(#j#-s%p#U#s$-Bs%rs#rUC#l#*.%#l#5s$,s$)#j#0s$5#4Ds$@s$7#S6HCj#0s$B#4s&+s%ns$D#S6MS9j#5s$l#j#9s$q#j#(s$t#-Ds$cs$R#S9Cl#(Cs$x#j#+s%1#-s&2s%us$h#S/Cl#(Cs%6#j#,s%N#0ES9s%$#SFCl#(Cs%Q#j#)s%;#0FS/s%=#SPCl#)Cs%U#j#*s%W#U#Cl#*s%[s%Z#U#Cl#*s%cs%b#j#9s%i#Z#KNCHIJj#+s%n#j#,s%q#j#9s%s#j#(s%w#j#)s%|#j#*s&##j#:E#j#;F#j#<E#j#=F#[#MHIJKNC'C#s&D#s&B,K#s&F#s&D3GJKUSds&D#s&D$#$IJ#P#s%-#s&Us&<SF#DOSF$S<S7#Ps&E#$S3S'9PEs&&#s&/C#ES'S<9PFs%~s&,s$|N#FS?S$#FSER#FSJQ#ESIS%#s&as&HR#DOR'SF#s&[#s&Y3GHS)#s&X#7#s&gS&s&N$S9S/%##DS.#&&#k#((#k#)s&H#k#*,#k#+/#k#,1#k##3#j#-F##ESJQ#s&ts&[Q#DOQ,SH#s&n#s&l3GS+I#s&k#s#*#s&zS/s&a#DS&s$W&$#k#(&#k#))#k#*s&\#k#+-#k#,/#j#-E##DOS%'S9#s&|#s&z,S+#s&~#s&|3GS@S+#s&{#s#:#DS/s$]&s%n#k#(%#k#)(#k#*+#k#+.#j#.s'4#'SH#s'-#s'+,S@#s'/#s'-3GS6S@#s',#s#G$S@S+%##DJ#&s%i#k#('#k#)*#k#*-#j#/D#)Gs&;CS9#DOs&R&s%p#k#0%#j#1s'G#)Gs&Ws'/S/)Gs&+s'0C#DOs&A&s%v#k#0%#j#2D#)Gs&Fs'5O3GS;S:5s'B#s#]K(s'Cs#^$s$R#S/#s'Ds#_s$SnSR$s'F$#-SUC#&$#4S>#SV#S>j#1s'F#-s'Gs#b#SQs$`C#DOs&7&s&&#C#Cl#*&S>#l#>+*#j#0/#4DO1#S9HCj#07#4s'^s'E9#S9MS#j#5s#4#j#9s#7#j#(s#:#-DOB#S#Cl#(Cs#>#j#+s#M#-s'es'Ls#3#S%Cl#(Cs#P#j#,s#d#0ES#s#D#SDCl#(Cs#g#j#)s#U#0FS%s#W#SICl#)Cs#k#j#*s#m#U#Cl#*s#qs#p#U#Cl#*s#us#t#j#9s#x#Z#KNCHIJj#+s#|#j#,s#~#j#9s$$#j#(s$'#j#)s$+#j#*s$.#j#<E#j#=F#Y#IJKNCUSes'p#s'ps$0##s'qs#x$k#(#s#sk#)s'\#k#*s#|#k#+s$##k#,s$%#k##s$'#j#-F##s'ys#m,k#(#s#jk#)s#p#k#*s'g#k#+s#t#k#,s#v#j#-E##s($s#d3k#(#s#bk#)s#g#k#*s#j#k#+s#m#j#.s(7##s(*s#]9k#(#s#Yk#)s#`#k#*s#c#j#/D#5s(/s#L>K(s(0?s#Ms%?#S/#s(1@s%@nSR$s(3$#-SUC#&$#4S>#S>#SVj#1s(3#-s(4s###SQs%MCl#*#S>s#Il#>('#j#0s#U#4DOs#W#S9HCj#0s#]#4s(Hs(/s#_#S9MS#j#59#j#9s#}#j#(s$$#-DO2#S#Cl#(Cs$(#j#+s$7#-s(Os(6:#S%Cl#(Cs$:#j#,s$N#0ES#s###SDCl#(Cs$Q#j#)s$?#0FS%s#-#SICl#)Cs$U#j#*s$W#U#Cl#*s$[s$Z#U#Cl#*s$_s$^#j#9s$b#Z#KNCHIJj#+s$f#j#,s$h#j#9s$j#j#(s#A#j#)s$q#j#*s$t#j#<E#j#=F#Y#IJKNC'H#s(_#s(],S'.s(bH#s(b$#6GS3M7S-HIK/$S'#USTE?S'@M#.EH#&$##Ps(9s&Q#s(uMS&=SDSE>#$#S3%##D#S&$SPSD#P#s(/9PEs(Is(:s'uC#ESPS69PFs(Es(%s'aN#FSAS;#FS)S*#FS4S5#ES(S=#s)(SFS*=KS(>#$#S)%##D#S*'S2#s)&#s)$.s)(S2#s)(s(i#6GHS$7S-S2S<S(/$R#?R@S$#.ES2#s#'$##s)9S0s(|$S1S8%##DS,#&&#k#,(#k#92#k#(.#k#)2#k#*5#k#?8#k#5>#k##@#j#-F##ES4S5#s)HSAS5=S,S7>#$#S4%##D#S5,S8.s)GS$#s)G$#6GS1R7S-S$S2S7/$I#'S$#s)L#s)J?Q@R#.ES$#s#H$##s)ZS8s)A$SGS1%##DS0#&&#k#,(#k#9-#k#(0#k#)4#k#*s)@#k#?9#k#5?#j#-E#=S0S<>#$#S(%##D#S='S0#s)d#s)b,S1.s)gR#s)g$#6GSGQ7S-RS$J/$S1#'R#s)l#s)j?S%@Q#.ER#s#h$##s)zS1s)a$SLSG%##DS8#&&#k#,(#k#9-#k#(0#k#)4#k#*8#k#?;#j#.s*)#=S8S2>#$#S7%#'S8#s*&#s*$,SG.s*)Q#s*)$#6GSLS%7S-QRS0/$SG#'Q#s*.#s*,?S#@S%#.EQ#s$*$##s*<SGs*#$SNSL%##DH#&&#k#,(#k#9-#k#(0#k#)4#k#*8#j#/D#7S-RS$S,/s#5S1#=SMS#>#$#Q%#$SOSM)G#SGC#s*OSLs*6=SSS&>#$#S#%#$SMSN%##D%#&*#k#0,#j#2D#)G(S10'S#.s*TS&5s*T$s*RK'SM5s*V#s*TH,SO5s*X#s*VS8(s*Ys*W$(#I(s*Z*s*X)K#(s*[s*Y+*)#(s*\)s*Z+H#(s*]s*[*,)#(s*^.s*\-K#(s*_s*]/.-##s*`s*^/nST$s*b$#@SUC#%$##S>#SVj#'s*b#.s*dS/-s*ds*b$SQ#C#s*nSNs*U=S[S/>#$#S.%#%s#(#D$#&)#C#Cl#*,S>#l#>21#j#0A#4Ds#0s###S8MSCj#As#`#j#+s#e#j#,s#7#j#9s#l#j#(s#p#-Ds#Us#<#SBCl#(Cs#t#j#?s$7#0s+'S=s#\#S)Cl#(Cs$>#j#5s$_#0ESBs#~#S7Cl#(Cs$b#j#)s$C#0FS=s$E#S(Cl#)Cs$f#j#*s$h#U#Cl#*s$ls$k#U#Cl#*s$ps$o#j#+s$r#\#KNCS'MHIJj#?s$v#j#5s$|#j#+s$~#j#,s%$#j#9s%0#j#(s%+#j#)s%/#j#*s%3#j#Bs+>#j#CE#j#:E#j#DS-#j#Es+:#j#<E#j#=F#`#SJSES?S3S'MHIJKNC'I#s+>#s+<,M.s+AI#s+A$#6GS'H7S-IJK/$M#?M@H#USYE#s%@$#$S/S&#Ps*z##s+Ts+;S##DOS##Ps+;s)*9PEs+#s%:s&zC#ESDS+9PFs*{s*rs*hN#FSFS6#FSAS:#FS)S;#ES4S*#s+^s+ES:#DOS:'S<#s+X#s+V.s+ZS<#s+Zs+?#6GHS27S-S<S7S(/$S$#?S$@S2##s%X#;#s+jSCs+Q$S0S,%##DSK#&&#k#,(#k#91#k#(-#k#)1#k#*4#k#?7#k#59#k##;#j#-F##ES)S;#s+ys+`S;#DOS;,S,#s+s#s%N6GS0S$7S-S2S<S7/$I##s%os%Ls#2#s,%S,s+h$S8S0%##DSC#&&#k#,(#k#9s%Z#k#(+#k#)/#k#*s+g#k#?3#k#55#j#-E##DOS*'SC#s,+#s,),S0#s,-#s%E6GS8R7S-S$S2S</$S0##s&)s%As#H#s,;Ms+~&#s%^k#,%#k#9s%G#k#((#k#),#k#*/#k#?2#j#.s,C#'S,#s,<#s,:#s,=s%Vs%56GS1Q7S-RS$S2/$S8##s&9s%1s#X#DHs%M&s*w#k#,%#k#9s%7#k#((#k#),#k#*.#j#/D#)Gs$tCS0#DOs%6&s+$#k#0%#j#1s,W#)Gs%;s,?S,)Gs$cs,@C#DOs$z&s+*#k#0%#j#2D#)Gs%#s,EO5s,Vs$bs,TJ'SN5s,X#s,VM,SM5s,Z#s,XS0(s,[s,Y$s$f#H(s,\s$hs,Zs$gJ#(s,]s,[s$is$h)#(s,^)s,\s$iM#(s,_s,]*s$j)#(s,`s$ls,^s$kJ#(s,as,_s$ms$l-#j#1s,bs$_-s,cs,a#SQs$^C#DOs$v&s+=#C#Cl#*&S>#l#>)s$f#j#06#4DO8#S0S'Cj#0>#4s,us,\@#S0S3SBj#As#>#j#+s&$#j#,s#A#j#9s#E#j#(s#H#-DOs#+#S5Cl#(Cs#L#j#?s#a#-s,~s,es#=#S*Cl#(Cs#d#j#5s$$#0ES5s#R#S(Cl#(Cs$'#j#)s#i#0FS*s#k#S4Cl#)Cs$+#j#*s$-#U#Cl#*s$1s$0#U#Cl#*s$5s$4#j#+s$7#\#KNCS'MHIJj#?s$:#j#5s$<#j#+s$>#j#,s$A#j#9s$L#j#(s$G#j#)s$K#j#*s$O#j#Bs-9#j#:E#j#DS-#j#Es-4#j#<E#j#=F#_#SES?S3S'MHIJKNC7S-HIJ/s'3S'#.s-:J#s-:s':#:M#s-<#s-:8S3;M#1L#s-/2LS'##s-J#S&$SDS?%##D#S&8S);SF#1L#s-72LSA##s-R#S*$KS4%##D#S*/s'&Rs$6.s-OS7#s-Os',#:S$#s-Q#s-Ok#,#s&|k#9&#k#()#k#)s'/#k#*s'2#k#?-#k#51#k##s'=#j#-F#8S4;SA#1L#s-M2LS)##s-h#S5$S,S(%##D#S5/s&yIs$6#s-ds&ws$i:R#s-f#s-dk#,#s&pk#9&#k#((#k#)s'%#k#*s-Q#k#?,#k#50#j#-E#8S(;S)#1L#s-a2LS4#$S0S7%##D#S=/s&lS1s$9#s-ws&js'R:Q#s-y#s-w&s$Js&dk#,$#k#9'#k#()#k#)s&u#k#*s&y#k#?-#j#.s..#$S8S<%#7S-QRS$/s&]SG##s.*s&[s'B:S%#s.,#s.*8S#;Q#1L#s-{2LS%##s.:#s-}&#s&Zk#,)#k#9,#k#(.#k#)s&k#k#*s&o#j#/D#8S%;R#1L#s.+2LQ#)Gs&WCS18S.;S%#1L#s.02LS###s.K#s.2$SSS.%##D#s&W&&#k#0,#j#1s.Q#)Gs&\/S8$SOS#%#$SSSO)G#.C8S&;S##1L#s.@2LS.##s.[#s.B$S[S&%##D#s&I&&#k#0,#j#2D#)Gs&ss#+0:S.5s.[#s.YK'SO5s.]#s.[M,SS5s._#s.]S1(s.`s.^$s&[#H(s.a)s._s&\K#(s.bs.`*s&])#(s.c)s.as&^M#(s.ds.b*s&_)#(s.e-s.cs&`K#(s.fs.d.s&a-##s.gs.es&b.s.iS9-s.is.gs$eSQ#C8S/;S.#1L#s.\2LS&##s.w#s.^$SfS/%#%s#'#D$#&'#C#Cl#*.S>#l#>21#j#0@#4Ds#/B#S1S'Cj#0s#2#4s/'s#@s#4#S1S3SCj#As#`#j#+s#c#j#,s#e#j#9s'u#j#(s'y#-Ds#[s#J#SBCl#(Cs#j#j#?s#~#-s/0s#os#`#S=Cl#(Cs$'#j#5s$>#0ESBs#v#S7Cl#(Cs(k#j#)s(L#0FS=s$1#S(Cl#)Cs(o#j#*s(q#U#Cl#*s(us(t#U#Cl#*s(ys(x#j#+s({#\#KNCS'MHIJj#?s$P#j#5s$T#j#+s)+#j#,s$[#j#9s$^#j#(s$a#j#)s)8#j#*s)<#j#Fs/?#j#Bs/H#j#:E#j#DS-#j#Es/C#j#<E#j#=F#`#SJSES?S3S'MHIJKNC:H#s/G#s$l8S'<H#1L#s/:2LM##s/U#S#$SIS3%##D#S#8SA<SP#1L#s/B2LSF##s/]#S:$KS)%##D#S::S<.s/ZS(#s/Z$##s/dSKs/K$S,SC%##DSB#&&#k#9(#k#(s&b#k#)s&f#k#*s&i#k#5/#k#+3#k##s&p#j#-F#<SFs%%1L#s/Y2LSA##s/t#S;$SKS4%##D#S;:S2#s/p#s%$k#9#s&jk#(s&Z#k#)s&^#k#*s/Z#k#5)#k#+-#j#-E#<SAs${1L#s/i2LS)#$SCS(%##D#S*#s/~s%0s''#s0,Hs/o&#s&ck#9%#k#(s&T#k#)s&X#k#*s&[#k#5*#j#.s03#$S,S7%##s0-s%&s)d8Q<S$#1L#s/|2LR##s0;#s/~#DIs)_&$#k#9*#k#(s&T#k#)s&X#k#*s&Z#j#/D#8R<S2#1L#s0,2LS$#)Gs)*CS,<Rs$d1L#s002LQ##s0K#s02$SNS%%##D#s)P&&#k#0+#j#1s0Q#)Gs)U.SC$SLQ%#)Gs(v-C<Qs$~1L#s0>2LS%##s0Y#s0@$SMS#%##D#s)>&&#k#0+#j#2D#)Gs)Cs#(..s0YS.,SN5s0Z#$I'SL5s0\#s0ZH(s0]s0[$s0[#H(s0^'s0\s0\S,#(s0_)(s0]'##s0`*s0^nST$s0b$#@SUC#%$##SV#S>j#1s0b#-s0cs(n#SQs0aC<S%s%(1L#s0U2LS###s0p#s0W$SOS.%##D#s)7&&#C#Cl#*,S>#l#>10#j#0:#4Ds#'<#S,MCj#0s#*#4s0{s#7s#,#S,S'S=j#?s#S#j#,s'F#j#9s'J#j#(s'M#-Ds#Ms#@#S5Cl#(Cs#Y#j#5s#i#-s1's#^s#R#S*Cl#(Cs#n#j#+s$*#0ES5s#d#S(Cl#(Cs(,#j#)s'n#0FS*s#w#S4Cl#)Cs(0#j#*s(2#U#Cl#*s(6s(5#U#Cl#*s(:s(9#j#,s(<#[#KNCMHIJj#5s$<#j#+s$@#j#,s(C#j#9s$G#j#(s&W#j#)s+.#j#*s+2#j#Gs15#j#Bs1>#j#:E#j#DS-#j#Es19#j#<E#j#=F#_#SES?S3S'MHIJKNC'N#s1=#s1;,J.s1@N#s1@$#6GIKUSgS-/$J#$HI$S7S(#P$##s1Ps17S)#DOS)#Ps-Ws/r9PEs0{s1#s/gC#ES3S$9PFs0ws0|s1$N#FSEQ#FSJS%#FSIS##ESDS.#s1Zs1AS%'SA#s1S#s1Q.s1USA#s1Us1:#6GHS)/#S47#s1aS9s1H&#s-6k#(%#k#)(#k#*+#k#+s-A#k#,/#k##1#j#-F##ESIS#.s1cS)#s1cs-7#6GS6S4/#Is#%#s1oSHs1V#DS9s-6&$#k#(&#k#))#k#*s1Q#k#+s(~#k#,s)$#j#-E##DOS.'S+#s1q#s1o,S6.s1tS4#s1t$#6GS:S(/#S6s#6&s0cs11k#($#k#)'#k#*+#k#+.#j#.s2)#'S@#s1~#s1|#s2#s1+s%(6GS;S7/#S:s#A#DJs1&&s0[#k#(%#k#)(#k#**#j#/D#)Gs0_CS+k#0#s-=j#1s27#)Gs0vs1{SH)Gs0Ws1|C#DOs0c&s0f#k#0%#j#2D#)Gs0hs2%O,S55s27#s+nJ'S*5s29#s27I(s2:s28$s28#I(s2;'s29s29S+#(s2<s+s(s2:'##s2=s+ts2;-s2>s+Vs$:SQs2<C#DOs0e&s0t#C#Cl#*&S>#l#>)(#j#01#4DO3#S+HCj#09#4s2Ps27;#S+MS&j#5s#0#j#9s#3#j#(s#7#-DOB#S&Cl#(Cs#;#j#+s)_#-s2Ws2>s#0#S.Cl#(Cs)b#j#,s#]#0ES&s#A#SPCl#(Cs#`#j#)s#P#0FS.s#R#SDCl#)Cs#d#j#*s#f#U#Cl#*s#js#i#U#Cl#*s#ns#m#j#9s#p#Z#KNCHIJj#+s#s#j#,s#u#j#9s#w#j#(s#{#j#)s$##j#*s$'#j#Es2d#j#<E#j#=F#Z#HIJKNCnS\$G'#$#.#/##s2OC#+*#H#I#7#8######s/'(#H#I######s-R(#H#I######s,h/#H#I#E#D#8#C#B##########s*-.#H#I#E#D#8#B##########s(3/#H#I#E#D#8#B#F##########s&$.#H#I#E#D#8#B#G########s$.)#H#I#E########PKs26#s2rKS3#DKS3#s2tSEs2[%s2`#DS?#&%#k##'#k##)#k##+#j#/D#j#.s2|#j#$P#W#s/'IJBPs2OBs3$HBDIWC%$#l#*5'#j#0s2p#j#6s2s#j#Js2z#j#2D#j#1s3,#j#8E#j#7F#j#IE#j#HF##"). Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_account_inv : forall cfg ms model ms' model' e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  sstep_cfg segs cfg (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms' model').
Proof.
  intros cfg ms model ms' model' e st Hsvc Hacc Hss.
  apply (sstep_account_inv ms model ms' model' e st Hsvc Hacc). eapply sstep_cfg_sub. exact Hss.
Qed.

Lemma dsteps_account : forall ms model ms' model' c3,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  dsteps (mkCfg ms' model') c3 ->
  dsteps (mkCfg ms model) c3.
Proof. intros. eapply ds_step; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLazy.
Variables L S : list (word * word).
Hypothesis HL : lazy_ranges_okb segs L = true.

Theorem account_step_restrict : forall msF ms1 model,
  lazy_inv L S model ->
  RiscvSemantics.step segs (restrict L S msF) = MachineOk ms1 ->
  exists model',
    mi_account_step segs msF model = MachineOk (unrestrict_to L S msF ms1, model')
    /\ lazy_inv L S model'
    /\ same_but_materialized model model'
    /\ (forall a, hiddenb L S a = true -> ms_mem ms1 a = None).
Proof.
  intros msF ms1 model Hinv Hstep.
  destruct (step_restrict segs L S msF ms1 HL Hstep) as (rep & Hsa & Hval & Hvis & Hnone & _).
  destruct (materialize_restrict L S model (accessed_ranges _ rep) Hinv Hvis) as (pages & Hmat & Hinv').
  exists (with_vm_backing (m_vm_lazy model) pages model).
  unfold mi_account_step. rewrite Hsa, Hmat, Hval.
  split; [reflexivity|]. split; [exact Hinv'|]. split; [|exact Hnone].
  apply same_but_materialized_with_vm_backing.
Qed.

(* [comment removed for export] *)
Theorem msteps_restrict_gen : forall ms0 ms1,
  msteps segs ms0 ms1 ->
  forall msF model,
    ms0 = restrict L S msF ->
    lazy_inv L S model ->
    m_halted model = None ->
    exists model',
      dsteps (mkCfg msF model) (mkCfg (unrestrict_to L S msF ms1) model')
      /\ lazy_inv L S model'
      /\ same_but_materialized model model'
      /\ restrict L S (unrestrict_to L S msF ms1) = ms1.
Proof.
  intros ms0 ms1 Hms; induction Hms as [ms | ms ms' ms'' Hsvc Hstep Hms IH];
    intros msF model -> Hinv Hh.
  - exists model. rewrite unrestrict_restrict_self.
    split; [apply ds_refl|]. split; [exact Hinv|].
    split; [apply same_but_materialized_refl | reflexivity].
  - destruct (account_step_restrict msF ms' model Hinv Hstep) as (model1 & Hacc & Hinv1 & Hsame1 & Hnone).
    specialize (IH (unrestrict_to L S msF ms') model1).
    rewrite (restrict_unrestrict_to L S msF ms' Hnone) in IH.
    assert (Hh1 : m_halted model1 = None)
      by (rewrite (same_but_materialized_halted _ _ Hsame1); exact Hh).
    destruct (IH eq_refl Hinv1 Hh1) as (model' & Hd & Hinv' & Hsame' & Hr).
    rewrite unrestrict_to_idem in Hd, Hr.
    exists model'. split; [|split; [exact Hinv'|split; [|exact Hr]]].
    + eapply dsteps_account; [exact Hh | exact Hsvc | exact Hacc | exact Hd].
    + eapply same_but_materialized_trans; eassumption.
Qed.

Theorem msteps_restrict : forall msF ms1 model,
  lazy_inv L S model ->
  m_halted model = None ->
  msteps segs (restrict L S msF) ms1 ->
  exists model',
    dsteps (mkCfg msF model) (mkCfg (unrestrict_to L S msF ms1) model')
    /\ lazy_inv L S model'
    /\ same_but_materialized model model'
    /\ m_halted model' = None
    /\ restrict L S (unrestrict_to L S msF ms1) = ms1.
Proof.
  intros msF ms1 model Hinv Hh Hms.
  destruct (msteps_restrict_gen _ _ Hms msF model eq_refl Hinv Hh) as (model' & Hd & Hinv' & Hsame & Hr).
  exists model'. repeat (split; [assumption|]).
  split; [|exact Hr].
  rewrite (same_but_materialized_halted _ _ Hsame). exact Hh.
Qed.

End WithLazy.
End WithSegs.
