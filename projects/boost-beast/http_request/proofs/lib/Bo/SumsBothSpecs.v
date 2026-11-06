(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import BothImages.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import SumsLib BothIMemset BothIMemcpy BothMemIsZero.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import MemsetLib.
From OSSVerify.Proofs.boost_beast.http_request.lib Require BothMemset BothMemset_code BothMemcpyBase BothMemcpy.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanPlanSoundSums.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation BSEGS2 := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kept_ok_of_regs_agree : forall (clob : list reg) regs regs',
  (forall r, In r clob -> In (AX2.ridx r) AP.caller_saved) ->
  regs_agree (fun r => In r clob) regs regs' -> APSX.kept_ok regs regs'.
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.

#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

#[local] Ltac clob_sub :=
  let r := fresh "r" in let H := fresh "H" in
  intros r H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [in_list|]); destruct H.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.False Sort Prop.

Lemma imemset_clob_sub : forall r, In r imemset_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.cons); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__1); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ridx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.caller_saved); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothIMemset.imemset_clob)|] [|@r; @H|] "#%>#,#F#>###=#@#$#%#8#&#'#3#9#(#)#0#/#D#*#+#G#H#;#4#C#5#B#<#?#1#2#7#6#F#E#A#:2#7&#8&#9$#:&#;&#<%#=$#>$#?$#@$#A&#B%#C&#D)#E)+L*#UP#UQ#*%,#-&#I*L+#+#,#-+#I*&,#-.#IUM.&/$#&0(#&1.#$2D##30G#4,G#5*G(#E(%#('#)H$C#Fj##%##<9H)D$C#Fj#$?#%R)>#C$#%%%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#UMC&C$#&C&#&C(#&C*#&C6#&C8#&C:#&C<#&C>#&C@#&CB#&Cs#$#&Cs#(#&Cs#*#&Cs#,#$Cs#2##Cs#.s#3$Cs#4&#Cs#/s#5$Cs#6)#Cs#0s#7$Cs#8,#Cs#/s#9$Cs#:/#Cs#0s#;$Cs#<2.Cs#=/%$#'('#'+*#'.-#'10#'s#B3#$Cs#DFm#$#0s#es#bs#H#JDj#%s#L#U#Dj##s#W##s#is#aH#s#js#_H(#E(%##s#ms#eJ#s#ns#cJ(#E(%#)K$C#Fj##%##s#ts#lK)s#m#Cs#X#$C$s#)#Cs#T%$C&s#,#Cs#U'$C(s#/#Cs#V)$C*s#2#Cs#U+$C,s#5#Cs#V-$C.s#8#Cs#W/$C0s#;.C1/%$#'('#'+*#'.-#'10#'43#'76#$C9Fm#$#0s$2s$*s#q#NDj#%=#U#Dj##s#&##s$6s$+K(#E#s$8s$-N(#E)O$C#Fj##%##s$=s$2O)s$3#Cs#}#$C$s#N#Cs#y%$C&s#Q#Cs#z'$C(s#T#Cs#{)$C*s#W#Cs#z+$C,s#Z#Cs#{-$C.s#]#Cs#|/$C0s#`#Cs#}1$C2s#c.C3/%$#'('#'+*#'.-#'10#'43#'76#':9#$C<Fm#$#0s$Zs$Os$=#S#Dj#%@#U#Dj##s#'#)S$$C#Fj##E#VS%#Dj#%E#U#Dj##E#1s#/Es#+*#Dj#%s#1#U#Dj##s#W#1s#Zs#Xs#Ts#6#Dj#%s#\#U#Dj##s$W#1s$\s$Xs$Ts#c#Dj#%s$^#j#$s$o#$s$pDS&)G$C#Fk##%#k#$s$t#m#(##"). Qed.
Lemma imemcpy_clob_sub : forall r, In r imemcpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.cons); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__1); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ridx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.caller_saved); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothIMemcpy.imemcpy_clob)|] [|@r; @H|] "#%|#.#H#@###?#B#$#%#:#&#'#(#)#5#;#*#+#2#1#F#,#-#I#J#=#6#E#D#7#>#A#3#4#9#8#H#G#C#<2#9&#:&#;$#<&#=&#>%#?$#@$#A$#B$#C&#D%#E&#F)#G)+N*#UR#US##*%,#-&#I*N+#+#,#-+#I*&,#-.#I**+#,#-2#IUO2'3$#'4)#'5-#'63#$7D##85G#91G#:/G#;,G(#E(%#('#()#)H$C#Fj##%##s##@H)D$C#Fj#$s#&#%S$)s#%#C$#%%%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#UOC'C$#'C&#'C(#'C*#'C6#'C8#'C:#'C<#'C>#'C@#'CB#'Cs#$#'Cs#(#'Cs#*#'Cs#,#$Cs#2##Cs#.s#3$Cs#4&#Cs#/s#5$Cs#6)#Cs#0s#7$Cs#8,#Cs#/s#9$Cs#:/#Cs#0s#;$Cs#<2.Cs#=/%$#&('#&+*#&.-#&10#&s#B3#$Cs#DFm#$#0s#ls#is#H#JDj#%s#L#U#Dj##s#Y##s#ps#hH#s#qs#fH#s#rs#cH(#E(%#('##s#vs#nJ#s#ws#lJ#s#xs#iJ(#E(%#('#)K$C#Fj##%##s$#s#wK)s#x#Cs#\#$C$s#-#Cs#X%$C&s#0#Cs#Y'$C(s#3#Cs#Z)$C*s#6#Cs#Y+$C,s#9#Cs#Z-$C.s#<#Cs#[/$C0s#?.C1/%$#&('#&+*#&.-#&10#&43#&76#$C9Fm#$#0s$=s$5s#u#LDj#%=#U#Dj##s#(##s$As$6K#s$Bs$3K(#E(%##s$Es$:L#s$Fs$7L(#E(%#)M$C#Fj##%##s$Ls$AM)s$B#Cs$)#$C$s#V#Cs$%%$C&s#Y#Cs$&'$C(s#\#Cs$')$C*s#_#Cs$&+$C,s#b#Cs$'-$C.s#e#Cs$(/$C0s#h#Cs$)1$C2s#k.C3/%$#&('#&+*#&.-#&10#&43#&76#&:9#$C<Fm#$#0s$is$^s$E#PDj#%@#U#Dj##s#)##s$ms$^M(#E#s$os$`P(#E)Q$C#Fj##%##s$ts$eQ)s$f#Cs$Q#$C$s#~#Cs$M%$C&s$%#Cs$N'$C(s$(#Cs$O)$C*s$+#Cs$N+$C,s$.#Cs$O-$C.s$1#Cs$P/$C0s$4#Cs$Q1$C2s$7#Cs$R3$C4s$:.C5/%$#&('#&+*#&.-#&10#&43#&76#&:9#&=<#$C?Fm#$#0s%8s%)s$p#S%Dj#%s###U#Dj##s#*#)S&$C#Fj##E#VS'#Dj#%E#U#Dj##E#1s#2Es#.*#Dj#%s#4#U#Dj##s#]#1s#`s#^s#Zs#9#Dj#%s#b#U#Dj##s$.#1s$3s$/s$+s#i#Dj#%s$5#U#Dj##s%2#1s%9s%3s%/s$>#Dj#%s%;#j#$s%Q#$s%RDS()G$C#Fk##%#k#$s%V#m#(##"). Qed.
Lemma memisz_clob_sub : forall r, In r memisz_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.cons); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__1); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ridx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.caller_saved); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothMemIsZero.memisz_clob)|] [|@r; @H|] "#(6#4#N#F###E#H#$#%#@#&#'#(#)#*#+#,#-#.#/#;#A#0#1#8#7#L#2#3#O#P#C#<#D#J#K#=#G#:#?#>#N#M#I#B#92#?&#@&#A%#B&#C$#D&#E$#F$#G$#H&#I%#J&#K)#L)#M$*S$1#US(#US)#*%+#,&#I1(+#,)#I1S$*#*#+#,.#I1&+#,1#I1**#+#,5#I1&+#,8#I*;*#*#+#,=#IUS%=(>$#(?*#(@.#(A3#(B7#(s##=#(s#$A#$s#%D##s#&s##G#s#'AG#s#(=G#s#);G#s#*8G#s#+6G#s#,2G%#E%%#%'#%)#%+#%-#%/#)H$C#Fj##%##s#7s#4H)D$C#Fj#$s#:#'S*)s#9#C$#'%'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#US%C(C$#(C&#(C(#(C*#(C6#(C8#(C:#(C<#(C>#(C@#(CB#(Cs#$#(Cs#(#(Cs#*#(Cs#,#$Cs#2##Cs#.s#3$Cs#4&#Cs#/s#5$Cs#6)#Cs#0s#7$Cs#8,#Cs#/s#9$Cs#:/-Cs#;.%$#&('#&+*#&.-#&s#?0#$Cs#AFm#$#/s#}s#zs#E#JDj#%s#I#U#Dj##s#\##s$%s#{H#s$&s#wH#s$'s#uH#s$(s#rH#s$)s#pH#s$*s#lH%#E%%#%'#%)#%+#%-##s$1s$+J#s$2s$'J#s$3s$%J#s$4s#~J#s$5s#|J#s$6s#xJ%#E%%#%'#%)#%+#%-#)K$C#Fj##%##s$@s$:K)s$;#Cs#e#$C$s#6#Cs#a%$C&s#9#Cs#b'$C(s#<#Cs#c)$C*s#?#Cs#b+$C,s#B#Cs#c-$C.s#E-C/.%$#&('#&+*#&.-#&10#&43#$C6Fm#$#/s$Ws$Qs#{#LDj#%:#U#Dj##s#+##s$[s$PK#s$\s$NK#s$]s$KK#s$^s$IK#s$_s$EK%#E%%#%'#%)#%+##s$es$ZL#s$fs$XL#s$gs$UL#s$hs$SL#s$is$OL%#E%%#%'#%)#%+#)M$C#Fj##%##s$rs$gM)s$h#Cs$;#$C$s#h#Cs$7%$C&s#k#Cs$8'$C(s#n#Cs$9)$C*s#q#Cs$8+$C,s#t#Cs$9-$C.s#w#Cs$:/$C0s#z-C1.%$#&('#&+*#&.-#&10#&43#&76#$C9Fm#$#/s%0s%%s$T#NDj#%=#U#Dj##s#,##s%4s%&M#s%5s%#M#s%6s$}M#s%7s$yM%#E%%#%'#%)##s%<s%.N#s%=s%+N#s%>s%)N#s%?s%%N%#E%%#%'#%)#)O$C#Fj##%##s%Gs%9O)s%:#Cs$l#$C$s$=#Cs$h%$C&s$@#Cs$i'$C(s$C#Cs$j)$C*s$F#Cs$i+$C,s$I#Cs$j-$C.s$L#Cs$k/$C0s$O#Cs$l1$C2s$R-C3.%$#&('#&+*#&.-#&10#&43#&76#&:9#$C<Fm#$#/s%ds%Vs%,#PDj#%@#U#Dj##s#-##s%hs%VO#s%is%TO#s%js%PO%#E%%#%'##s%ns%\P#s%os%ZP#s%ps%VP%#E%%#%'#)Q$C#Fj##%##s%ws%eQ)s%f#Cs%@#$C$s$m#Cs%<%$C&s$p#Cs%='$C(s$s#Cs%>)$C*s$v#Cs%=+$C,s$y#Cs%>-$C.s$|#Cs%?/$C0s%##Cs%@1$C2s%&#Cs%A3$C4s%)-C5.%$#&('#&+*#&.-#&10#&43#&76#&:9#&=<#$C?Fm#$#/s&;s&)s%_#RDj#%s###U#Dj##s#.##s&?s&*Q#s&@s&&Q%#E%%##s&Cs&.R#s&Ds&*R%#E%%#)S#$C#Fj##%##s&Js&5S#)s&6#Cs%o#$C$s%@#Cs%k%$C&s%C#Cs%l'$C(s%F#Cs%m)$C*s%I#Cs%l+$C,s%L#Cs%m-$C.s%O#Cs%n/$C0s%R#Cs%o1$C2s%U#Cs%p3$C4s%X#Cs%q5$C6s%[-C7.%$#&('#&+*#&.-#&10#&43#&76#&:9#&=<#&@?#$CBFm#$#/s&ms&Xs&5#S&Dj#%s#&#U#Dj##s#/##s&qs&WS#%#E#s&ss&YS&%#E)S'$C#Fj##%##s&xs&^S')s&_#Cs&A#$C$s%n#Cs&=%$C&s%q#Cs&>'$C(s%t#Cs&?)$C*s%w#Cs&>+$C,s%z#Cs&?-$C.s%}#Cs&@/$C0s&$#Cs&A1$C2s&'#Cs&B3$C4s&*#Cs&C5$C6s&-#Cs&D7$C8s&0-C9.%$#&('#&+*#&.-#&10#&43#&76#&:9#&=<#&@?#&s##B#$Cs#%Fm#$#/s'Bs'(s&f#S+Dj#%s#)#U#Dj##s#0#)S,$C#Fj##E#VS-#Dj#%E#U#Dj##E#0s#8Es#4*#Dj#%s#:#U#Dj##s#i#0s#ls#js#fs#?#Dj#%s#n#U#Dj##s$@#0s$Es$As$=s#u#Dj#%s$G#U#Dj##s$t#0s${s$us$qs$P#Dj#%s$}#U#Dj##s%M#0s%Vs%Ns%Js%,#Dj#%s%X#U#Dj##s&'#0s&2s&(s&$s%e#Dj#%s&4#U#Dj##s'4#0s'As'5s'1s&C#Dj#%s'C#j#$s'g#$s'hDS.)G$C#Fk##%#k#$s'l#m#(##"). Qed.
Lemma ms_clob_sub : forall r, In r ms_clob -> In (AX2.ridx r) AP.caller_saved.
Proof. ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.cons); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Datatypes.nil); constr:(@kc__1); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ridx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.caller_saved); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.MemsetLib.ms_clob)|] [|@r; @H|] "#'U#2#L#D###C#F#$#%#>#&#'#(#)#*#+#,#-#9#?#.#/#6#5#J#0#1#M#N#A#:#H#B#I#;#E#8#7#=#<#L#K#G#@2#=&#>&#?&#@%#A$#B&#C$#D$#E$#F$#G&#H%#I&#J)#K)*R+#US&#US'#+%,#-&#I+R*#*#,#-+#I+&,#-.#I+**#,#-2#I+&,#-5#I*8*#*#,#-:#IUS#:(;$#(<*#(=.#(>3#(?7#(@=#$AD##B?G#s##;G#s#$9G#s#%6G#s#&4G#s#'0G&#E&%#&'#&)#&+#&-#)H$C#Fj##%##s#1s#.H)D$C#Fj#$s#4#'S()s#3#C$#'%'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#US#C(C$#(C&#(C(#(C*#(C6#(C8#(C:#(C<#(C>#(C@#(CB#(Cs#$#(Cs#(#(Cs#*#(Cs#,#$Cs#2##Cs#.s#3$Cs#4&#Cs#/s#5$Cs#6)#Cs#0s#7$Cs#8,#Cs#/s#9$Cs#:/#Cs#0s#;$Cs#<2.Cs#=/%$#%('#%+*#%.-#%10#%s#B3#$Cs#DFm#$#0s#zs#ws#H#JDj#%s#L#U#Dj##s#]##s#~s#vH#s$#s#tH#s$$s#qH#s$%s#oH#s$&s#kH&#E&%#&'#&)#&+##s$,s$$J#s$-s#~J#s$.s#{J#s$/s#yJ#s$0s#uJ&#E&%#&'#&)#&+#)K$C#Fj##%##s$9s$1K)s$2#Cs#d#$C$s#5#Cs#`%$C&s#8#Cs#a'$C(s#;#Cs#b)$C*s#>#Cs#a+$C,s#A#Cs#b-$C.s#D#Cs#c/$C0s#G.C1/%$#%('#%+*#%.-#%10#%43#%76#$C9Fm#$#0s$Ss$Ks#}#LDj#%=#U#Dj##s#,##s$Ws$LK#s$Xs$IK#s$Ys$GK#s$Zs$CK&#E&%#&'#&)##s$_s$TL#s$`s$QL#s$as$OL#s$bs$KL&#E&%#&'#&)#)M$C#Fj##%##s$js$_M)s$`#Cs$9#$C$s#f#Cs$5%$C&s#i#Cs$6'$C(s#l#Cs$7)$C*s#o#Cs$6+$C,s#r#Cs$7-$C.s#u#Cs$8/$C0s#x#Cs$91$C2s#{.C3/%$#%('#%+*#%.-#%10#%43#%76#%:9#$C<Fm#$#0s%+s$|s$U#NDj#%@#U#Dj##s#-##s%/s$|M#s%0s$zM#s%1s$vM&#E&%#&'##s%5s%&N#s%6s%$N#s%7s$|N&#E&%#&'#)O$C#Fj##%##s%>s%/O)s%0#Cs$i#$C$s$:#Cs$e%$C&s$=#Cs$f'$C(s$@#Cs$g)$C*s$C#Cs$f+$C,s$F#Cs$g-$C.s$I#Cs$h/$C0s$L#Cs$i1$C2s$O#Cs$j3$C4s$R.C5/%$#%('#%+*#%.-#%10#%43#%76#%:9#%=<#$C?Fm#$#0s%^s%Os%,#PDj#%s###U#Dj##s#.##s%bs%PO#s%cs%LO&#E&%##s%fs%TP#s%gs%PP&#E&%#)Q$C#Fj##%##s%ms%[Q)s%\#Cs%<#$C$s$i#Cs%8%$C&s$l#Cs%9'$C(s$o#Cs%:)$C*s$r#Cs%9+$C,s$u#Cs%:-$C.s$x#Cs%;/$C0s${#Cs%<1$C2s$~#Cs%=3$C4s%%#Cs%>5$C6s%(.C7/%$#%('#%+*#%.-#%10#%43#%76#%:9#%=<#%@?#$CBFm#$#0s&4s%~s%^#S$Dj#%s#&#U#Dj##s#/##s&8s%}Q&#E#s&:s&#S$&#E)S%$C#Fj##%##s&?s&(S%)s&)#Cs%j#$C$s%;#Cs%f%$C&s%>#Cs%g'$C(s%A#Cs%h)$C*s%D#Cs%g+$C,s%G#Cs%h-$C.s%J#Cs%i/$C0s%M#Cs%j1$C2s%P#Cs%k3$C4s%S#Cs%l5$C6s%V#Cs%m7$C8s%Y.C9/%$#%('#%+*#%.-#%10#%43#%76#%:9#%=<#%@?#%s##B#$Cs#%Fm#$#0s&es&Ns&3#S)Dj#%s#)#U#Dj##s#0#)S*$C#Fj##E#VS+#Dj#%E#U#Dj##E#1s#8Es#4*#Dj#%s#:#U#Dj##s#i#1s#ls#js#fs#?#Dj#%s#n#U#Dj##s$@#1s$Es$As$=s#u#Dj#%s$G#U#Dj##s$t#1s${s$us$qs$P#Dj#%s$}#U#Dj##s%M#1s%Vs%Ns%Js%,#Dj#%s%X#U#Dj##s&Y#1s&ds&Zs&Vs%e#Dj#%s&f#j#$s'*#$s'+DS,)G$C#Fk##%#k#$s'/#m#(##"). Qed.
Scheme kc__3 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.ex Sort Prop.

(* [comment removed for export] *)
Lemma kept_ok_of_keeps : forall regs regs', keeps regs regs' -> APSX.kept_ok regs regs'.
Proof.
  ltac2:(KReplay.run [|constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@stdpp.bitvector.definitions.bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefMemcpyLib.keeps); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.I); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ridx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.caller_saved); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.ridx_range); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Numbers.BinNums.N); constr:(@kc__3); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Logic.and); constr:(@stdpp.bitvector.definitions.bv_eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSoundSums.APSX.reg_of_ridx); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.not_morph); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.ex); constr:(@kc__4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RefMemcpyLib.callee_kept); constr:(@kc__1); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.or_introl); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSoundSums.APSX.kept_ok); constr:(@kc__4 (@Corelib.Init.Datatypes.nat))|] [|@r; @b2; @b1; @n; @H; @X; @k; @y; @x; @__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @cstr; @Hnin0; @Hrr0; @Hr1; @Hrk; @Hink; @E; @Hr; @Hrr; @Hnin; @Hr0; @Hk; @regs'; @regs|] "#;r#P$K#`#l$0##$1$/#x#$#i$7$;#'#%#(#)#^#+#-#*#,#/#0#3#.#1#2#5#&#4#7#6#9#]#8#;#:#=#<#?#f#>#A#@#W$F#C#B#d#[$%#E#D#T#k#j#q#g$$$($)$9$@$A#P$D#G#F#S#Y#b#c#o#}#|#~$&$'$*$+$,$.$6$5$8$<$=$>$B$C$?#v#u#r#I#H#K#J#M#L#O#N$K$E$L#w$I#p#a#_#h$3$2#{$4#e#s#y#z$:#m#\#V#U$J$H$G#X#Z#n$-#t$#B#S&$/%$0&$1%$2$$3&#+$$4%$5'$6*$7/$8%$9$$:&$;$$<)$=*$>%$?&$@$#&'$A$$B&$C*$D)$E$$F$$G%$H+$I$$J'6S>8#USG#6%6#6#6#6#USG#<#VSV*#VSWJF<,5-S3R#$F#=#'J(C#SX=#USYO'O/S:/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#/#VSBs###'S.#C#S:)S:*s#9#j#$s#0s#.<F<J<O##JF4S.O4S.J#D$#k##&#4OJ4OF#D$#<S.##OJk##%#>)#<N##S.Ok##-#j##&#j##$Fj##/#WSZOJFYSH1+&$#j#%8#j#&:#j#'SI#k#%;/k#&=#k#'SI#4s#Xs#M&D#7s#Zs##s#O#l#()&#WSJNS:FZSKs#Ss#&s#%$N#US.#j#)s#*#=s#+m#$#@C0Cs#6#0Cs#8#0Cs#:#0Cs#<#0Cs#>#0Cs#@#0Cs#B#0Cs#D#0Cs#F#0Cs#H#0Cs#R#0Cs#T#0Cs#Y#0Cs#[#0Cs#]#(CF#'P#C#F>%#j#*C#'N(C#)#C$$#Cs#f%#Cs#f&#Cs#f'#Cs#c(#Cs#c)#Cs#[*#Cs#[+#Cs#[,#Cs#[-#Cs#[.#Cs#[/#Cs#[0#Cs#[1#Cs#[2#Cs#[3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#1s$>)s#$#D$#8S>1##D#&1s$A#D#(1s$B#D#*8s$E1##D#-6%1##D#08(1##D#36s$P6#1##D#78&1##D#:8s$W6#1##D#>8&1##D#A6@6#6#1##D#s#&8&1##D#s#)8*6#1##D#s#-8&1##D#s#0$#I$'#$,#$0#$6#$:#$?#$s###$s#(#$s#,#$s#0#$s#4#$s#7#$s#:#$s#>#USCCUSCD)J)F#D$##CJFVS[JFWS\%$#j#+C#j#,C#&Ds#K&Ds#K-CD.K-%s$ss#M$s#ns#L#&Ds#J-CD0K/'s$ts#K#s#ps#N%&Ds#J-CD2K1)s$us#K#s#rs#P'&Ds#J-CD4K3+s$ss#K#s#ts#R)&Ds#I-CD6K5-s$ts#J#s#vs#T+&Ds#H-CD8K7/s$ms#I#s#xs#V-&Ds#G-CD:K91s$ns#H#s#zs#X/&Ds#E-CD<K;3s$os#F#s#|s#Z1&Ds#D-CD>K=5s$ps#E#s#~s#\3&Ds#B-CD@K?7s$qs#C#s$$s#^5&Ds#A-CDBKA9s$rs#B#s$&s#`7&Ds#>-CDs#$Ks##;s$ss#?#s$(s#b9&Ds#=-CDs#&Ks#%=s$ts#>#s$*s#d;&Ds#;-CDs#(Ks#'?s$us#<#s$,s#f=&Ds#:-CDs#*Ks#)As$vs#;#s$.s#h?US]I2s#{Is#<I$#2s#}s#{s#@s#<'#2s$#s#{s#Es#<*#2s$%s#{s#Is#<-#2s$'s#{s#Os#<0#2s$)s#{s#Ss#<3#2s$+s#{s#Xs#<6#2s$-s#{s#\s#<9#2s$/s#{s#as#<<#2s$1s#{s#es#<?#2s$3s#{s#is#<B#2s$5s#{s#ms#<s#%#2s$7s#{s#ps#<s#(#2s$9s#{s#ss#<s#+#2s$;s#{s#ws#<s#.##Cs$?S:=##Ds#{S3=#&DS3-CDs#@Ks#?s#7s$Ds#~s#5S:S3#WSL(&#A(&#FVSBs$Ks%.)s$L1s%^VSD$#&D%&D%-CDSBKSDS^s$Q'$s%4&#A)&#O'Q#Cs%V##Cs%S$#Cs%S%#Cs%S&#Cs%Q'#Cs%Q(#Cs%Q)#Cs%Q*#Cs%Q+#Cs%Q,#Cs%Q-#Cs%Q.#Cs%G/#Cs%G0#Cs%G1#Cs%G2$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#=#1S>)s#%#D$#1s&2#D#%1s$4#D#'8s$T1##D#*1s$G#D#,1s$B#D#.1s$<#D#01s$7#D#26-1##D#5801##D#81s&C#D#:8s&F1##D#=6-1##D#@801##D#s##601##D#s#&831##D#s#)$#I$'#$+#$/#$3#$7#$:#$>#$B#$s#%#$s#(#$s#+#$s#.#$s#2#$s#5#$s#8#=#&Ds#<&Ds#<-CDs$MKs$Ls$Ds&Ws#>$s#`s#=#&Ds#<-CDs$OKs$Ns$Fs&Us#=#s#bs#?%&Ds#<-CDs$QKs$Ps$Hs&Vs#=#s#ds#A'&Ds#;-CDs$SKs$Rs$Js&Ws#<#s#fs#C)&Ds#;-CDs$UKs$Ts$Ls&Vs#<#s#hs#E+&Ds#;-CDs$WKs$Vs$Ns&Ws#<#s#js#G-&Ds#;-CDs$YKs$Xs$Ps&Xs#<#s#ls#I/&Ds#;-CDs$[Ks$Zs$Rs&Ys#<#s#ns#K1&Ds#:-CDs$]Ks$\s$Ts&Zs#;#s#ps#M3&Ds#9-CDs$_Ks$^s$Vs&[s#:#s#rs#O5&Ds#9-CDs$aKs$`s$Xs&\s#:#s#ts#Q7&Ds#8-CDs$cKs$bs$Zs&]s#9#s#vs#S9&Ds#7-CDs$eKs$ds$\s&Ts#8#s#xs#U;&Ds#6-CDs$gKs$fs$^s&Us#7#s#zs#W=&Ds#5-CDs$iKs$hs$`s&Vs#6#s#|s#Y?&Ds#4-CDs$kKs$js$bs&Ws#5#s#~s#[A2s#oIs#5I#s$C2s#qs#os#9s#5&#2s#ss#os#=s#5)#2s#us#os#As#5,#2s#ws#os#Es#5/#2s#ys#os#Is#52#2s#{s#os#Ls#55#2s#}s#os#Ps#58#2s$#s#os#Ts#5;#2s$%s#os#Ws#5>#2s$'s#os#Zs#5A#2s$)s#os#]s#5s#$#2s$+s#os#`s#5s#'#2s$-s#os#ds#5s#*#2s$/s#os#gs#5s#-#2s$1s#os#js#5s#0#WSLs#os#5#As#os#5#N'S%US_#)$VSMS3#@SNUS`SNVSaDJUSbDUScD.DS3VSdDS>+D$Se#,&HEEG#LUSfE.Ds#}+D#M',*HEEG#L.Ds#}+D#M*,-HEEG#L.Ds#~+D#M-,0HEEG#L.Ds#~+D#M0,3HEEG#L.Ds$#+D#M3,6HEEG#L.Ds$$+D#M6,9HEEG#L.Ds$%+D#M9,<HEEG#L.Ds$&+D#M<,?HEEG#L.Ds$&+D#M?,BHEEG#L.Ds$&+D#MB,s#%HEEG#L.Ds$'+D#Ms#%,s#(HEEG#L.Ds$'+D#Ms#(,s#+HEEG#L.Ds$'+D#Ms#+,s#.HEEG#L.Ds$'+D#Ms#.,s#1HEEG#L.Ds$'+D#Ms#1,s#4HEEG#L.Ds$'+D#Ms#4,s#7HEEG#LZSgs#8HEEGS.3s#9HEEG$#3s#:HEEG(#3s#;HEEG,#3s#<HEEG0#3s#=HEEG4#3s#>HEEG8#3s#?HEEG<#3s#@HEEG@#3s#AHEEGs#$#3s#BHEEGs#(#3s#CHEEGs#,#3s#DHEEGs#0#3s#EHEEGs#4#3s#FHEEGs#8#3s#GHEEGs#<#3s#HHEEGs#@#ZSOs#IHEEG#.Ds%/+Ds#ISh#,s#LHEEG#L+Ds#KMs#L,s#NHEEG#LZSOs#OHEEG#.Ds&[+D#Ms#O,s#RHEEG#L.Ds&Z+D#Ms#R,s#UHEEG#L.Ds&[+D#Ms#U,s#XHEEG#L.Ds&\+D#Ms#X,s#[HEEG#L.Ds&\+D#Ms#[,s#^HEEG#L.Ds&\+D#Ms#^,s#aHEEG#L.Ds&\+D#Ms#a,s#dHEEG#L.Ds&[+D#Ms#d,s#gHEEG#L.Ds&[+D#Ms#g,s#jHEEG#L.Ds&Z+D#Ms#j,s#mHEEG#L.Ds&Z+D#Ms#m,s#pHEEG#L.Ds&X+D#Ms#p,s#sHEEG#L.Ds&X+D#Ms#s,s#vHEEG#L.Ds&W+D#Ms#v,s#yHEEG#L.Ds&W+D#Ms#y,s#|HEEG#L3s#}HEEG#s#G3s#~HEEG'#3s$#HEEG+#3s$$HEEG/#3s$%HEEG3#3s$&HEEG7#3s$'HEEG;#3s$(HEEG?#3s$)HEEGs###3s$*HEEGs#'#3s$+HEEGs#+#3s$,HEEGs#/#3s$-HEEGs#3#3s$.HEEGs#7#3s$/HEEGs#;#?s$0HEEGs#?s$+#?s$1HEEGs#Cs$,#?s$2HEEGs#Gs$-#?s$3HEEGs$/s$.#VSis$4G&SPSQVSjFO#SP#SQm$%#WSkDS3JXSlFO$#l#-*)#l#.s$>s$=#l#/s$As$@#j#0D#j#1SR#VSMS3F#Ds%ZJ#Ds%XJ#Ds%WJ#Ds%UJ#Ds%TJ#Ds%SJ#Ds%RJ#Ds%QJ#Ds%OJ#Ds%MJ#Ds%LJ#Ds%JJ#Ds%HJ#Ds%FJ#Ds%DJ#Ds%BJ$#O$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#k###IVSDOs&G#DS.S3k###I#Ds'pN#Ds'mN#Ds'lN#Ds'kN#Ds'iN#Ds'gN#Ds'eN#Ds'bN#Ds'`N#Ds']N#Ds'[N#Ds'WN#Ds'UN#Ds'RN#Ds'PN$#P$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#k##A#k##s#$#k##s#&#k##s#H#k#0D#k#1SR#'S&)#ZFI#JOS.Nl#2s#O&#l#3s%8s%6#l#4s%;s%n#l#5s&os&s#l#6s&xs&|#XSms(As'^s'%#m##s(a&Cs(cXSns(cs(b$#XSoCs(fs(e#VSSCs(g#Cs&vF>s(m#j#*C#VSSC#(s)zQS?j##$##Cs%IF>s(s#j#*C#U#F'S##C#F>s(x#(CJs(z#C>J>$#(s**S$S?j##$#'S$#C#O(CS.s)%'S'#C#N)P*s*<#(s*3FS?j#$s*4##Cs*+P#Cs*+P#Cs*+P#Cs*(P#Cs*(P#Cs)|P#Cs)|P#Cs)|P#Cs)|P#Cs)|P#Cs)|P#Cs)|P#Cs)|P#Cs)|P#Cs)|P$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#)Q*s*^#5s*_s'3R5s*`s)&R5s*as)#R5s*bs(~R5s*cs(}R5s*ds({R5s*es'/R5s*fs(zR5s*gs(xR5s*hs(uR5s*is(sR5s*js(pR5s*ks(nR5s*ls(jR5s*ms(hR5s*ns(eR5s*os(cR@s*f0s*g$#0s*h&#0s*i(#0s*j*#0s*k,#0s*l.#0s*m0#0s*n2#0s*o4#0s*p6#0s*q8#0s*r:#0s*s<#0s*t>#0s*u@#0s*vB#0s*ws#$#(s*xs#&#j##s#)##Cs*pQ'S)#C#F*s++s(h(s*~#)k#7%#j#*C#'S,#C#s*x)s*y*s+2##s+)s#2##s+*s#2$#s++s#2%#s+,s#2&#s+-s#2'#s+.s#2(#s+/s#2)#s+0s#2*#s+1s#2+#s+2s#2,#s+3s#2-#s+4s#2.#s+5s#2/#s+6s#20#s+7s#21#s+8s#22#s+9s#23$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s+Ts#$&D#7s+Vs#Ts#&#l#(s*as*^#9s#&(#%s#((#(s+Ps#*s#7m#$#j#7s#.#:Cs+Is#1#S%FOj#(s#8#U#Fj##s$###Cs+LQ#Cs+LQ#Cs+IQ#Cs+IQ#Cs+AQ#Cs+AQ#Cs+AQ#Cs+AQ#Cs+AQ#Cs+AQ#Cs+AQ#Cs+AQ#Cs+AQ#Cs+AQ$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=##Cs+hS%#Cs+hS%#Cs+eS%#Cs+eS%#Cs+]S%#Cs+]S%#Cs+]S%#Cs+]S%#Cs+]S%#Cs+]S%#Cs+]S%#Cs+]S%#Cs+]S%#Cs+]S%$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#)S#*s,>#(s,5#s#xj##&##Cs,,S#'S-#C#Fk#7#s#vj#*C#'S/#C#s,2)s,3*s,I##s,@s$I##s,As$I$#s,Bs$I%#s,Cs$I&#s,Ds$I'#s,Es$I(#s,Fs$I)#s,Gs$I*#s,Hs$I+#s,Is$I,#s,Js$I-#s,Ks$I.#s,Ls$I/#s,Ms$I0#s,Ns$I1#s,Os$I2#s,Ps$I3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s,ks#$&D#7s,ms$js#&#l#(s+xs+u#9s#%)#%s#')#%s#))#(s,hs#+s$Om#$#j#7s#/#:Cs,`s#2#S&FNj#(s#7#U#Fj##s#Y##Cs,cS##Cs,`S##Cs,`S##Cs,XS##Cs,XS##Cs,XS##Cs,XS##Cs,XS##Cs,XS##Cs,XS##Cs,XS##Cs,XS##Cs,XS#$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;##Cs,}S&#Cs,zS&#Cs,zS&#Cs,rS&#Cs,rS&#Cs,rS&#Cs,rS&#Cs,rS&#Cs,rS&#Cs,rS&#Cs,rS&#Cs,rS&#Cs,rS&$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#)S$*s-R#(s-I#s%0j##&##Cs-?S$'S0#C#Fk#7#s%.j#*C#'S1#C#s-E)s-F*s-]##s-Ts%]##s-Us%]$#s-Vs%]%#s-Ws%]&#s-Xs%]'#s-Ys%](#s-Zs%])#s-[s%]*#s-\s%]+#s-]s%],#s-^s%]-#s-_s%].#s-`s%]/#s-as%]0#s-bs%]1#s-cs%]2#s-ds%]3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s.#s#$&D#7s.%s%}s#&#l#(s-0s--#9s#$*#%s#&*#%s#(*#%s#**#(s-}s#,s%dm#$#j#7s#0#:Cs-ts#3#S*FQj#(s#8#U#Fj##s#X##Cs-tS$#Cs-tS$#Cs-lS$#Cs-lS$#Cs-lS$#Cs-lS$#Cs-lS$#Cs-lS$#Cs-lS$#Cs-lS$#Cs-lS$#Cs-lS$$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9##Cs.0S*#Cs.0S*#Cs.(S*#Cs.(S*#Cs.(S*#Cs.(S*#Cs.(S*#Cs.(S*#Cs.(S*#Cs.(S*#Cs.(S*#Cs.(S*$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#)S'*s.c#(s.Z#s&Aj##&##Cs.LS''S2#C#Fk#7#s&?j#*C#'S4#C#s.R)s.S*s.n##s.es&n##s.fs&n$#s.gs&n%#s.hs&n&#s.is&n'#s.js&n(#s.ks&n)#s.ls&n*#s.ms&n+#s.ns&n,#s.os&n-#s.ps&n.#s.qs&n/#s.rs&n0#s.ss&n1#s.ts&n2#s.us&n3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s/4s#$&D#7s/6s'1s#&#l#(s.As.>#9s##+#%s#%+#%s#'+#%s#)+#%s#++#(s/3s#-s&vm#$#j#7s#1#:Cs/&s#4#S(FS#j#(s#9#U#Fj##s#W##Cs/)S'#Cs.}S'#Cs.}S'#Cs.}S'#Cs.}S'#Cs.}S'#Cs.}S'#Cs.}S'#Cs.}S'#Cs.}S'#Cs.}S'$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7##Cs/?S(#Cs/7S(#Cs/7S(#Cs/7S(#Cs/7S(#Cs/7S(#Cs/7S(#Cs/7S(#Cs/7S(#Cs/7S(#Cs/7S($#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#)S+*s/q#(s/h#s'Oj##&##Cs/YS+'S5#C#Fk#7#s'Mj#*C#'S6#C#s/_)s/`*s/|##s/ss'|##s/ts'|$#s/us'|%#s/vs'|&#s/ws'|'#s/xs'|(#s/ys'|)#s/zs'|*#s/{s'|+#s/|s'|,#s/}s'|-#s/~s'|.#s0#s'|/#s0$s'|0#s0%s'|1#s0&s'|2#s0's'|3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s0Bs#$&D#7s0Ds(>s#&#l#(s/Os/L#9B,#%s#$,#%s#&,#%s#(,#%s#*,#%s#,,#(s0Bs#.s()m#$#j#7s#2#:Cs04s#5#S,FS$j#(s#:#U#Fj##s#V##Cs0/S+#Cs0/S+#Cs0/S+#Cs0/S+#Cs0/S+#Cs0/S+#Cs0/S+#Cs0/S+#Cs0/S+#Cs0/S+$#I$%#$'#$)#$+#$-#$/#$1#$3#$5##Cs0CS,#Cs0CS,#Cs0CS,#Cs0CS,#Cs0CS,#Cs0CS,#Cs0CS,#Cs0CS,#Cs0CS,#Cs0CS,$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#)S)*s0|#(s0s#s(Zj##&##Cs0[S)'S7#C#Fk#7#s(Xj#*C#'S8#C#s0a)s0b*s1+##s0~s)+##s1#s)+$#s1$s)+%#s1%s)+&#s1&s)+'#s1's)+(#s1(s)+)#s1)s)+*#s1*s)++#s1+s)+,#s1,s)+-#s1-s)+.#s1.s)+/#s1/s)+0#s10s)+1#s11s)+2#s12s)+3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s1Ms#$&D#7s1Os)Gs#&#l#(s0Zs0W#9@.#%B.#%s#$.#%s#&.#%s#(.#%s#*.#%s#,.#%s#..#(s1Os#0s)6m#$#j#7s#4#:Cs18s#7#S/FS'j#(s#<#U#Fj##s#V##Cs1;S)#Cs1;S)#Cs1;S)#Cs1;S)#Cs1;S)#Cs1;S)#Cs1;S)#Cs1;S)#Cs1;S)$#I$%#$'#$)#$+#$-#$/#$1#$3##Cs1MS/#Cs1MS/#Cs1MS/#Cs1MS/#Cs1MS/#Cs1MS/#Cs1MS/#Cs1MS/#Cs1MS/$#I$%#$'#$)#$+#$-#$/#$1#$3#)S-*s2)#(s1|#s)cj##&##Cs1cS-'S9#C#Fk#7#s)aj#*C#'S;#C#s1i)s1j*s24##s2+s*4##s2,s*4$#s2-s*4%#s2.s*4&#s2/s*4'#s20s*4(#s21s*4)#s22s*4*#s23s*4+#s24s*4,#s25s*4-#s26s*4.#s27s*4/#s28s*40#s29s*41#s2:s*42#s2;s*43$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s2Vs#$&D#7s2Xs*Os#&#l#(s1cs1`#9?/#%A/#%s##/#%s#%/#%s#'/#%s#)/#%s#+/#%s#-/#%s#//#(s2Ys#1s*@m#$#j#7s#5#:Cs2As#8#S1FS+j#(s#=#U#Fj##s#U##Cs2DS-#Cs2DS-#Cs2DS-#Cs2DS-#Cs2DS-#Cs2DS-#Cs2DS-#Cs2DS-$#I$%#$'#$)#$+#$-#$/#$1##Cs2TS1#Cs2TS1#Cs2TS1#Cs2TS1#Cs2TS1#Cs2TS1#Cs2TS1#Cs2TS1$#I$%#$'#$)#$+#$-#$/#$1#)S0*s3/#(s3&#s*ij##&##Cs2hS0'S<#C#Fk#7#s*gj#*C#'S=#C#s2n)s2o*s3:##s31s+:##s32s+:$#s33s+:%#s34s+:&#s35s+:'#s36s+:(#s37s+:)#s38s+:*#s39s+:+#s3:s+:,#s3;s+:-#s3<s+:.#s3=s+:/#s3>s+:0#s3?s+:1#s3@s+:2#s3As+:3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s3\s#$&D#7s3^s+Ts#&#l#(s2is2f#9>0#%@0#%B0#%s#$0#%s#&0#%s#(0#%s#*0#%s#,0#%s#.0#%s#00#(s3`s#2s+Gm#$#j#7s#6#:Cs3Gs#9#S4FS)j#(s#>#U#Fj##s#T##Cs3JS0#Cs3JS0#Cs3JS0#Cs3JS0#Cs3JS0#Cs3JS0#Cs3JS0$#I$%#$'#$)#$+#$-#$/##Cs3XS4#Cs3XS4#Cs3XS4#Cs3XS4#Cs3XS4#Cs3XS4#Cs3XS4$#I$%#$'#$)#$+#$-#$/#)S2*s42#(s4)#s+lj##&##Cs3jS2'S@#C#Fk#7#s+jj#*C#'SA#C#s3p)s3q*s4=##s44s,=##s45s,=$#s46s,=%#s47s,=&#s48s,='#s49s,=(#s4:s,=)#s4;s,=*#s4<s,=+#s4=s,=,#s4>s,=-#s4?s,=.#s4@s,=/#s4As,=0#s4Bs,=1#s4Cs,=2#s4Ds,=3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s4_s#$&D#7s4as,Vs#&#l#(s3ls3i#9=1#%?1#%A1#%s##1#%s#%1#%s#'1#%s#)1#%s#+1#%s#-1#%s#/1#%s#11#(s4ds#3s,Km#$#j#7s#7#:Cs4Js#:#S6FS-j#(s#?#U#Fj##s#S##Cs4MS2#Cs4MS2#Cs4MS2#Cs4MS2#Cs4MS2#Cs4MS2$#I$%#$'#$)#$+#$-##Cs4YS6#Cs4YS6#Cs4YS6#Cs4YS6#Cs4YS6#Cs4YS6$#I$%#$'#$)#$+#$-#)S5*s52#(s5)#s,lj##&##Cs4iS5'SE#C#Fk#7#s,jj#*C#'SF#C#s4o)s4p*s5=##s54s-=##s55s-=$#s56s-=%#s57s-=&#s58s-='#s59s-=(#s5:s-=)#s5;s-=*#s5<s-=+#s5=s-=,#s5>s-=-#s5?s-=.#s5@s-=/#s5As-=0#s5Bs-=1#s5Cs-=2#s5Ds-=3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s5_s#$&D#7s5as-Us#&#l#(s4ls4i#9<2#%>2#%@2#%B2#%s#$2#%s#&2#%s#(2#%s#*2#%s#,2#%s#.2#%s#02#%s#22#(s5es#4s-Lm#$#j#7s#8#:Cs5Js#;#S8FS0j#(s#@#U#Fj##s#R##Cs5MS5#Cs5MS5#Cs5MS5#Cs5MS5#Cs5MS5$#I$%#$'#$)#$+##Cs5WS8#Cs5WS8#Cs5WS8#Cs5WS8#Cs5WS8$#I$%#$'#$)#$+#)S7*s6/#(s6&#s-ij##&##Cs5eS7'ST#C#Fk#7#s-gj#*C#'SU#C#s5k)s5l*s6:##s61s.:##s62s.:$#s63s.:%#s64s.:&#s65s.:'#s66s.:(#s67s.:)#s68s.:*#s69s.:+#s6:s.:,#s6;s.:-#s6<s.:.#s6=s.:/#s6>s.:0#s6?s.:1#s6@s.:2#s6As.:3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s6\s#$&D#7s6^s.Qs#&#l#(s5is5f#9;3#%=3#%?3#%A3#%s##3#%s#%3#%s#'3#%s#)3#%s#+3#%s#-3#%s#/3#%s#13#%s#33#(s6cs#5s.Jm#$#j#7s#9#:Cs6Gs#<#S;FS2j#(s#A#U#Fj##s#Q##Cs6JS7#Cs6JS7#Cs6JS7#Cs6JS7$#I$%#$'#$)##Cs6RS;#Cs6RS;#Cs6RS;#Cs6RS;$#I$%#$'#$)#)S9*s7)#(s6|#s.cj##&##Cs6^S9'Sp#C#Fk#7#s.aj#*C#'Sq#C#s6d)s6e*s74##s7+s/4##s7,s/4$#s7-s/4%#s7.s/4&#s7/s/4'#s70s/4(#s71s/4)#s72s/4*#s73s/4+#s74s/4,#s75s/4-#s76s/4.#s77s/4/#s78s/40#s79s/41#s7:s/42#s7;s/43$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s7Vs#$&D#7s7Xs/Js#&#l#(s6cs6`#9:4#%<4#%>4#%@4#%B4#%s#$4#%s#&4#%s#(4#%s#*4#%s#,4#%s#.4#%s#04#%s#24#%s#44#(s7^s#6s/Em#$#j#7s#:#:Cs7As#=#S=FS5j#(s#B#U#Fj##s#P##Cs7DS9#Cs7DS9#Cs7DS9$#I$%#$'##Cs7JS=#Cs7JS=#Cs7JS=$#I$%#$'#)S<*s7|#(s7s#s/Zj##&##Cs7TS<'Sr#C#Fk#7#s/Xj#*C#'Ss#C#s7Z)s7[*s8+##s7~s0+##s8#s0+$#s8$s0+%#s8%s0+&#s8&s0+'#s8's0+(#s8(s0+)#s8)s0+*#s8*s0++#s8+s0+,#s8,s0+-#s8-s0+.#s8.s0+/#s8/s0+0#s80s0+1#s81s0+2#s82s0+3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s8Ms#$&D#7s8Os0@s#&#l#(s7Zs7W#995#%;5#%=5#%?5#%A5#%s##5#%s#%5#%s#'5#%s#)5#%s#+5#%s#-5#%s#/5#%s#15#%s#35#%s#55#(s8Vs#7s0=m#$#j#7s#;#:Cs88s#>#SAFS7j#(s#C#U#Fj##s#O##Cs8;S<#Cs8;S<$#I$%##Cs8?SA#Cs8?SA$#I$%#)S@*s8p#(s8g#s0Nj##&##Cs8GS@'St#C#Fk#7#s0Lj#*C#'Su#C#s8M)s8N*s8{##s8rs0{##s8ss0{$#s8ts0{%#s8us0{&#s8vs0{'#s8ws0{(#s8xs0{)#s8ys0{*#s8zs0{+#s8{s0{,#s8|s0{-#s8}s0{.#s8~s0{/#s9#s0{0#s9$s0{1#s9%s0{2#s9&s0{3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s9As#$&D#7s9Cs13s#&#l#(s8Ns8K#986#%:6#%<6#%>6#%@6#%B6#%s#$6#%s#&6#%s#(6#%s#*6#%s#,6#%s#.6#%s#06#%s#26#%s#46#%s#66#(s9Ks#8s12m#$#j#7s#<#:Cs9,s#?#SFFS9j#(s#D#U#Fj##s#N##Cs9/S@$#I#Cs91SF$#I)SE*s9a#(s9X#s1?j##&##Cs97SE'Sv#C#Fk#7#s1=j#*C#'Sw#C#s9=)s9>*s9l##s9cs1l##s9ds1l$#s9es1l%#s9fs1l&#s9gs1l'#s9hs1l(#s9is1l)#s9js1l*#s9ks1l+#s9ls1l,#s9ms1l-#s9ns1l.#s9os1l/#s9ps1l0#s9qs1l1#s9rs1l2#s9ss1l3$#I$%#$'#$)#$+#$-#$/#$1#$3#$5#$7#$9#$;#$=#$?#$A#4s:2s#$&D#7s:4s2#s#&#l#(s9?s9<#97I#%97#%;7#%=7#%?7#%A7#%s##7#%s#%7#%s#'7#%s#)7#%s#+7#%s#-7#%s#/7#%s#17#%s#37#%s#57#%s#77#(s:=s#9s2$m#$#j#7s#=#:Cs9ys#@#SUFS<j#(s#E#U#Fj##s#M#)ST*s:O#(s:F#s2-j##I#VSx#Fj#8I#U#Fj##I#;s#VIs#Q+#Fj#8s#X#U#Fj##s$J#;s$Ms$Ks$Fs#]#Fj#8s$O#U#Fj##s%B#;s%Gs%Cs%>s$V#Fj#8s%I#U#Fj##s&=#;s&Ds&>s&9s%R#Fj#8s&F#U#Fj##s';#;s'Ds'<s'7s&Q#Fj#8s'F#U#Fj##s(<#;s(Gs(=s(8s'S#Fj#8s(I#U#Fj##s)@#;s)Ms)As)<s(X#Fj#8s)O#U#Fj##s*G#;s*Vs*Hs*Cs)`#Fj#8s*X#U#Fj##s+Q#;s+bs+Rs+Ms*k#Fj#8s+d#U#Fj##s,^#;s,qs,_s,Zs+y#Fj#8s,s#U#Fj##s-m#;s.&s-ns-is-.#Fj#8s.(#U#Fj##s/##;s/:s/$s.{s.A#Fj#8s/<#U#Fj##s08#;s0Qs09s04s/W#Fj#8s0S#U#Fj##s1P#;s1ks1Qs1Ls0p#Fj#8s1m#U#Fj##s34#;s3Qs35s2is20#J(s;)s3US?m#$#WSJS(PFZSKs;,s3Xs3V$S(#j#7s3[#j#8s3^#V#JFj##s3a#j##s3h#YSHs3is3hs3e#Fj#(s3k#j#*C#V#JFj##s3q#j#,C#YSyCs3zs3w#Fl#9s4#s3~#l#:s:As:B#l#;s;4s:n#VS.O#j#<s;7#j#=s;;#j#$s;?#VSzOJm#$#j#>s;C#j#?s;E#j#@s;F##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma segs_wr_of_forallb : forall segs,
  forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSX.segs_wr_ok segs.
Proof.
  intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
  rewrite Hw in Hs. exact Hs.
Qed.

Lemma both_segs_wr : APSX.segs_wr_ok BSEGS2.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.SumsBothSpecs.segs_wr_of_forallb); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.M.loaded_segments); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.forallb); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@Corelib.Init.Datatypes.orb); constr:(@Corelib.Init.Datatypes.negb); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_writable); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_readable)|] [|@seg|] "##-#$#0#*#+###.#(#)#1#0#2#/#-#,#'#VHCDUIEUJ#UKEVL$#j#$F#WMF#GWNC#Dm$*#VOG##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Derive.
Variable SEGS : list Segment.

(* [comment removed for export] *)
Lemma fill_spec_of_imemset : forall (entryw : word) (entry : Z),
  Z_to_bv 64 entry = entryw ->
  (forall mem0 (s c : word) n rom regs (ret : word),
    (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
    store_ok SEGS mem0 s (Z.to_nat n) = true ->
    (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs entryw mem0 rom)
                  (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
      /\ regs_agree (fun r => In r imemset_clob) regs regs') ->
  APSX.fill_spec SEGS entry 256.
Proof.
  intros entryw entry He SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  destruct (SUM mem0 s c n (seg_rom SEGS) regs ret Hn Hnw Hst ltac:(intros; exact Hc) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
  exists regs'. rewrite He. split; [exact Hms|]. split.
  - eapply kept_ok_of_regs_agree; [apply imemset_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold imemset_clob. cbn. intros [H|[H|[H|[]]]]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma fill_spec_of_memset : forall (entry : Z),
  (forall mem0 (d cv ret : word) (n : Z) rom,
    (0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
    store_ok SEGS mem0 d (Z.to_nat n) = true -> ret_ok ret ->
    forall regs, getr regs 10%bv = d -> getr regs 11%bv = cv -> getr regs 12%bv = Z_to_bv 64 n -> getr regs 1%bv = ret ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 rom)
                  (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10%bv = d /\ ms_agree regs regs') ->
  APSX.fill_spec SEGS entry AX2.two64.
Proof.
  intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  destruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
  exists regs'. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.

(* [comment removed for export] *)
Lemma copy_spec_of_imemcpy : forall (entryw : word) (entry : Z),
  Z_to_bv 64 entry = entryw ->
  (forall mem0 (dst src : word) n bs rom regs (ret : word),
    cpyH SEGS mem0 dst src n bs ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs entryw mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ regs_agree (fun r => In r imemcpy_clob) regs regs') ->
  APSX.copy_spec SEGS entry.
Proof.
  intros entryw entry He SUM mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  destruct (SUM mem0 dst src n bs (seg_rom SEGS) regs ret ltac:(constructor; assumption) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
  exists regs'. rewrite He. split; [exact Hms|]. split.
  - eapply kept_ok_of_regs_agree; [apply imemcpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold imemcpy_clob. cbn. intros [H|[H|[H|[H|[]]]]]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma miz_spec_of_summary : forall (entryw : word) (entry : Z),
  Z_to_bv 64 entry = entryw ->
  (forall mem (beg sp : word) N rom regs (ret : word),
    (0 <= N <= 2 ^ 40)%Z ->
    (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
    (16 <= bv_unsigned sp)%Z ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
    (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
    (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
       rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
    getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
    exists regs',
      msteps SEGS (mkst regs entryw mem rom)
                  (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
      /\ regs_agree (fun r => In r memisz_clob) regs regs'
      /\ getr regs' 10%bv = Z_to_bv 64 1 /\ getr regs' 2%bv = sp /\ getr regs' 1%bv = ret) ->
  APSX.miz_spec SEGS entry.
Proof.
  intros entryw entry He SUM mem beg sp N regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11.
  destruct (SUM mem beg sp N (seg_rom SEGS) regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11) as (regs' & Hms & Hag & H10 & _ & _).
  exists regs'. rewrite He. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply memisz_clob_sub | exact Hag].
Qed.
End Derive.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma both_fill_spec_imemset : APSX.fill_spec BSEGS2 (AP.x_imemset BOTH_H) 256.
Proof.
  apply (fill_spec_of_imemset _ both_imemset_entry); [apply bv_eq; reflexivity|].
  exact both_imemset.
Qed.

Lemma both_fill_spec_memset : APSX.fill_spec BSEGS2 (AP.x_memset BOTH_H) AX2.two64.
Proof.
  apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (BothMemset.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

Lemma both_copy_spec_imemcpy : APSX.copy_spec BSEGS2 (AP.x_imemcpy BOTH_H).
Proof.
  apply (copy_spec_of_imemcpy _ both_imemcpy_entry); [apply bv_eq; reflexivity|].
  exact both_imemcpy.
Qed.

Lemma both_copy_spec_memcpy : APSX.copy_spec BSEGS2 (AP.x_memcpy BOTH_H).
Proof.
  intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : BothMemcpyBase.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  destruct (BothMemcpy.ref_memcpy mem0 dst src n bs (seg_rom BSEGS2) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 (AP.x_memcpy BOTH_H)) with (0x111ab4%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma both_miz_spec : APSX.miz_spec BSEGS2 (AP.x_memiszero BOTH_H).
Proof.
  apply (miz_spec_of_summary _ both_mem_is_zero_entry); [apply bv_eq; reflexivity|].
  exact both_mem_is_zero.
Qed.

