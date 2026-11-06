(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXRep AXRep2 AXPRep AXRep_fields AXRep_mbuf X8_mbuf_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8_F_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma shvis_transport_awin : forall W m m' a b,
  shvis m a b -> munch W m m' -> wmono bsegs m m' -> Forall awin W -> 0 <= a <= b -> b <= AAPP_HI -> shvis m' a b.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shvis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shvis_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.hull_lo_le); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.hull_lo); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.hull_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.hull_hi_ge); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh_mono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsWalk.sh_ge_lowsh); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ALOWSH_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8Kit.awin_disjoint_shland); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ASHADOW_BASE_val); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AHI_LO)|] [|@__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @__x2; @__sat4; @Ha; @__x3; @__x4; @__sat11; @__sat10; @H1; @H6; @r0; @q0; @H9; @H8; @H7; @H5; @r; @q; @H4; @H3; @H2; @H; @H11; @H10; @__sat5; @z; @__sat8; @__sat6; @__sat7; @__sat9; @KM; @KL; @LE; @G3; @G2; @G1; @L3; @L2; @L1; @Hb; @H0; @FW; @WM; @MU; @SV; @b; @a; @m'; @m; @W|] "#+s#P$c#[#q#f#r#p###$#y#'#+#&#*#%#(#w#2#k#/#3$S#O#Y#g#P#5#,#-#.#0#1$:#4#8#6#7#9#?#@#I$]$a$b#S#V#c#z$#$$$9#<#:#>#A#C#D#E#F#G#H$F$E$J$L$U$V#B$\$[#L#)$`$c#T#Z#\#]#^#_#a#b#`#j#m#o#{#|$&$'#}#i$<$2#;$>#=$G$I$K$N$M$Q$P$R$W$X$Y#J#K#N$Z$d$_$e$^#h#U#e#X$H$*$,#d$%$)$($1$@#u#t#n$/$6$0#x$;$T$+$7#v$3$8$?#l$.$=$A$B$C$D$-#W#s#~$5$4$OL$;%$<$$=$$>%$?%$@%$A&$B%$C$$D$$E%$F'$G*$H+$I$$J&$K%$L%$M'$N&$O$$P%$Q%$R%$S$$T%$U%$V&$W%$X%$Y%$Z%$[%$\($]$$^*$_%#(&$`%$a&$b&US=S[$S($#$#$#$#$#E#US>#E(US>#US\#k##&#WS]MIHWS^PKMWS_S`PKVSaCCUSbS?WSc$#N#EP#PK($##PS)USdS#US=S#=CIUSeCUSfC9CE4CS(.C$Q#/&GDDF#JZS@'GDDFMF(GDDF$#USgD0*GDDF$#&VSh+FGSASBVSiHO)SA#SBm$%#WSjCEIXSkHO$#l#$*)#l#%54#l#&87#j#'C#j#(S*##EH(#I#EIk##$#k#'C#k#(S*##LNH#LOl#)+%##ENm#$#VSlN#+N##N7s#:&%#*N#''%)C#E(%#()#+L##L&$+*L#'&-)C#E(%#((#+S,1#,L1#3#%>S$&#j##)#&)8*S,#'+:)C#E(%#+S-##S-+S.&#@*S.#'%B)C#E(%#+S$&#s#&*S$#'%s#()C#E(%#+S/1#,S$1#3#%>S%&#j##)#')s#2)C#E+S0&#s#5*S0#+R'#s#8)C#E+S%:#s#;#E$#Es#=+S+'#s#?#E#k##&#k##(#;SC;#8C#8C%8CSC2C$#2C&#I#S1JS##s#r=COUSmC5C$I#4Cs$0.Cs#rQ#/s#tGDDF#J.C%Qs#s/s#vGDDF#JFs#wGDDF%#0s#xGDDF#s#qs#tl#$#s#ps#jl#%+s#{#l#&/s#~#j#'C#j#*C##IH(s#h#k###s#ik#'C#k#*C#HS+S2S$l#))$#l#+s#)B##ERm#$#VSnR#,R#R#&Rs#h*%#'&s#j)C#E(%#((#,S%#S%#&S%s#p*%#'&s#r)C#E(%#((#1s#:,S21#3#%>S3&#j##(#&S2s#|*(#')s#~)C#E(%#,S+#S+#,S4&S4s$(*$#'%s$*)C#E(%#,S5&S5s$.*$#'%s$0)C#E(%#+S61#,S31#3#%>SD&#j##)#''s$:)C#E,S6&S6s$=*$#,SE'#s$@)C#E,So?#s$C)Cs$DEUSp#,SD-#s$G<s$H#'%s$I&$#)C'#k##)#@)s$M*Es$N,Sq'#s$P#E#*$s$R($#k##(#A(s$U*s$VE,SF'#s$X*s$Y##$E($#k##(#B(s$],S7-#s$_)C#Ek##?#C&s$b,S8'#s$d)C#$k##s#$#-&s$g,SG'#s$i+SH?#s$k+SI-#s$m<s$n#'%s$o&$#)C'#k##s#/#@)s$s+SJ'#s$u#E#*$s$w($#k##s#-#A(s$z+SK'#s$|*s$}##$E($#k##s#,#B(s%%+SL-#s%')C#Ek##s#C#C&s%*+SM'#s%,)C#$k##s#H#-&s%/+S9'#s%1VSNEs%2GSO#m##s#DUP#*Hs%6(s%E#US/&#EL*Ls%:($#7s%y%s%z%#%#%#7#VSr(#*E)#E%VSs+&*E#k##%#k##'##E/WSt0+Ij##SP#j#,%##E*k##SP#k#,(#VSNE6GSO#m##1UI#;s$n;#8C#8C%2C#s$o2C%#VSuCs%ZWSvC#s$rUSwS(VSxC#;+8C#KC%#KC&-2C-s${2C$#2C&#2C,#I#S1VSQ0#JS##s&3=CM5Cs${K#=CK5Cs$}O#5C%I#9Cs%n.C#S&s&5/s&7GDDF#JZSys&8GDDF#%S(%#4C#WSRC)#$&4C#6C%#.Cs&>S&#/s&AGDDF#J0s&BGDDF,s&;#.C'S&s&B/s&DGDDF#J4C.6C#3.Cs&ESS#/s&HGDDF#J9Cs#HEs#EWSzC$#.C)Q#/s&MGDDF#J.Cs&LQ%/s&OGDDF#J0s&PGDDF%s&I#0s&QGDDF+s&J#0s&RGDDF0s&K#0s&SGDDF3s&L#l#$#s&Ks&El#%s##s&V#l#&s#)s&Y#j#'C#j#*C#j#-C#j#.C#k##s$RS{<s&9K&#M)CI#k##&#)CME&Ms&>*O##Ks#Yk####k##%#k##(#k##*#k#'C#k#*C#k#-C#k#.C#,S'\HS0S/S'#S4S5S3S9l#)6%#l#/s#Ws#c#l#0s#_s#\#l#/s#js#d#l#1s#us#r#l#2s#ys#w#l#3s#~C#l#4s$%C#l#5s$+s$'#l#6s$1s$-#l#7s$9s$3#l#2s$As$;#l#8s$Js$C#l#9s$MC#l#:s$PC#l#;s$Vs$R#l#<s$\s$X#l#=s$es$^#l#1s$ns$g#l#>s$ys$p##s${S)m#$#WS|s$yS)H1s$z1S)#$#+SF:#s&f#E$+S8'#s&i#E#k##s&0#k##'#:s$ts&m#Es$u#Es$ik##s&5#k##%#?s$rs&r<s&ss$j&#s$n)Cs$p#k##s%3#@s$rs&w#Es$m*s$ns&y($#k##s%/#As$rs&|,ST'#s&~*s'###$E($#k##s%.#B(s'',SH-#s'))C#Ek##s%E#C&s',,SI'#s'.)C#$k##s%J#VSU&s'1m#SV#?s$rs'3<s'4s$k's$ms'5&$#)Cs$o#k##s%Q#@s$qs'9#Es$l*s$ms';($#k##s%M#As$qs'>*s'?s$l#s$mE($#k##s%J#Bs$qs'C+S}-#s'E)C#Ek##s%a#C&s'H+S~'#s'J)C#$k##s%f#VSU&s'Mm#SV#UKs$y+SW'#s'Q#E#*$s'S($#US.s%#,SW'#s'W#E#*$s'Y($#KCs$\s$b2C#s&s2Cs$Z#2Cs$fs$Z2Cs$^#2Cs$c#I#S1VSQ'#JS##s(.5Cs$WKs&u5Cs$ZK#5Cs&xI#4Cs%+WSRCs$X#4Cs%.6C$#.Cs(0S&#/s(3GDDF#J0s(4GDDFs$Zs(-#.C'S&s(4/s(6GDDF#J6Cs(5s$`.Cs'$SS#/s(9GDDF#JZS@s(:GDDFSXFs(;GDDFs'%#0s(<GDDF#s(5s(80s(=GDDF&s(6#0s(>GDDF*s(7#0s(?GDDF-s(8#l#$#s(7s(1l#%6s(B#l#&:s(E#j#'C#j#*C#j#-C#j#.C#j#(S*#&Os(%*M##EK(#Nk###$k##&#k##s$L#k##s$N#k#'C#k#*C#k#-C#k#.C#k#(S*##S'T#+S'-#s(4'$s(5]H&$#S'%LS7S8S9l#)5(#l#1s#As#<#l#7s#Hs#C##Es#Hm#$#l#?s#Ls#M#l#@s#Ss#O#l#5s#Ys#U#l#6s#_s#[#l#7s#es#a#l#2s#ls#g#l#8s#ns#o#l#;s#us#q#l#<s#{s#w#l#=s$'s#}#l#1s$-s$)#l#>s$3s$/#l#+s$9s$5#l#As$As$;#m##s$AVT$s$D#1s$E#S:#+S71#1s&W3#$%s%=%#%#%#%#%#%#%#%#%#%#%#%#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#7#7s)N-s$f#&H#-s&r%&H#3#%&&#$s)R$#$#$#$#$#$#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#7##s#*#j#BC##S:s#0j#BC#ZSYCS;#Hs#5S<-s#Vs#5&s#7##S:#-s'Ds#8&H#-s&ds#:&H##%#j#BC#ZSYCS;#Os#?S<&s#@s#<&s#A(#$#+SGVSZ#s#C#E$#Es#E-s'Ks#F#E#k##%#k##'#:s'Ms)[#Es'N#Es'?k##s)##k##%#VSZs%5s#O#Es%6,SK-#s#R#E#k##1#k##'#,SJ:#s)h#E$,SL'#s)k#E#k##s)2#k##'#UKs&{9Cs#`6C#s)$9Cs#4.C$Q#/s*;GDDF#J6C's*:WT%C'#6C$#.C#Q(/s*@GDDF#J0s*AGDDF(s*:#l#$#s*9s*3l#%s)0s*D#l#&s*Hs*G#j#'C#j#*C#&s#pI##s#C&s#rO3#%&&###s#Gk##'#k#'C#k#*C#,SM-#s#y-s']s#zH$#Ll#)0'#l#CAs'I#l#+s#)s###l#As#2s#,#l#Ds#8s#4#l#Es'Hs'E#l#Cs'Ss'M#l#Fs#Bs#<#-s#Ds$(&s$*#&s$+s#P3#$&%###s#\m#)#l#Gs#Os#L#l#Hs#Zs#W#ZT&Cs$2s#^#S;S<&s$Rs$P##T'm#%#[T(S?STs$Us$SSEH#l#Hs$Zs$X#l#Gs&Es&B#l#Is&Gs&H#j#Js(g#j#Ks(k#V#IHj##s(p#j##s(}#Ds(~s(|s(t#Hj#>s)&#j#Ls)-#V#IHj##s)1#j##s)C#Ds)Ds)?s)8#Hl#>s)Os)G#j#Ms)|#j#Ns*$#V#IHj##s*)#j##s*6#Ds*7s*5s*-#Hj#>s*;#j#Os*B#V#IHj##s*F#j##s*Y#Ds*Zs*Us*M#Hl#>s*fs*]#]T)S-S,LNSXPKM#j#Ps+1#j#Qs+3#j#Rs+7#j#Ss+;#j#Ts+=#j#Us+?#j#VC#j#WC#j#Xs+C#j#YT*#j#Zs+Q##"). Qed.

(* [comment removed for export] *)
Lemma mwin_of_off : forall b es A n l h, aapp A n -> mb_off b es A n -> A <= l -> h <= A + n -> l <= h -> mwin b es (l, h).
Proof.
  intros b es A n l h AP [OB OE] H1 H2 H3. split; [eapply awin_aapp; [exact AP| exact H1| exact H2]|]. cbn [fst snd].
  split; [lia|]. intros x s IN. destruct (OE x s IN); lia.
Qed.

Lemma mb_off_sub : forall b es A n A' n', mb_off b es A n -> A <= A' -> A' + n' <= A + n -> mb_off b es A' n'.
Proof. intros b es A n A' n' [OB OE] H1 H2. split; [lia|]. intros x s IN. destruct (OE x s IN); lia. Qed.

(* [comment removed for export] *)
Lemma mwin_two : forall b es lo sp A n, mb_addr_ok b es -> aceil <= lo -> aapp A n -> 0 <= n -> mb_off b es A n ->
  Forall (mwin b es) [(lo, sp); (A, A + n)]%Z.
Proof.
  intros b es lo sp A n AOK CE AP Hn OFF. repeat apply Forall_cons; [apply mwin_stack; assumption| | apply Forall_nil].
  eapply mwin_of_off; [exact AP| exact OFF| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma AMBmid_after : forall W m m' b es insz n x,
  AMBmid m b es insz n x -> munch W m m' -> wmono bsegs m m' -> Forall (mwin b (mb_put_es es insz n x)) W ->
  AMBmid m' b es insz n x.
Proof. intros W m m' b es insz n x MID MU WM FW. unfold AMBmid in *. eapply AMBraw_transport_win; eauto. Qed.

(* [comment removed for export] *)
Lemma AMBraw_obj_rd0 : forall W m m' b es out insz outpos outend g,
  AMBraw m b es out insz outpos outend -> munch W m m' -> wmono bsegs m m' -> Forall (mwin b es) W ->
  b <= g -> g + 8 <= b + 64 -> g mod 8 = 0 ->
  ov_read_bytes bsegs m' (Z_to_bv 64 (Z.shiftr g 3 + 2147450880)) 1 = Some [b8 0].
Proof.
  intros W m m' b es out insz outpos outend g R MU WM FW H1 H2 H3.
  pose proof (AMBraw_acc _ _ _ _ _ _ _ (AMBraw_transport_win _ _ _ _ _ _ _ _ _ R MU WM FW)) as AC.
  exact (accessible_read0_sr m' b 64 g AC H1 H3 H2).
Qed.

Lemma AMBraw_elem_rd0 : forall W m m' b es out insz outpos outend x s g,
  AMBraw m b es out insz outpos outend -> munch W m m' -> wmono bsegs m m' -> Forall (mwin b es) W ->
  In (x, s) es -> x <= g -> g + 8 <= x + mb_block_size s -> g mod 8 = 0 ->
  ov_read_bytes bsegs m' (Z_to_bv 64 (Z.shiftr g 3 + 2147450880)) 1 = Some [b8 0].
Proof.
  intros W m m' b es out insz outpos outend x s g R MU WM FW IN H1 H2 H3.
  pose proof (AMBraw_elem_acc _ _ _ _ _ _ _ x s g 8 (AMBraw_transport_win _ _ _ _ _ _ _ _ _ R MU WM FW) IN H1 H2) as AC.
  exact (accessible_read0_sr m' g 8 g AC ltac:(lia) H3 ltac:(lia)).
Qed.

End HCW.
