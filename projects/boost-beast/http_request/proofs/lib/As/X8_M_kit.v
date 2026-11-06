(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXRep AXRep2 AXPRep AXRep_fields AXRep_mbuf X8_mbuf_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8_F_kit.
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
  shvis m a b -> munch W m m' -> wmono asegs m m' -> Forall awin W -> 0 <= a <= b -> b <= AAPP_HI -> shvis m' a b.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.shvis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8Kit.awin); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.shvis_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.hull_lo_le); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.hull_lo); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.sh); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.hull_hi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.hull_hi_ge); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.sh_mono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsWalk.sh_ge_lowsh); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.ALOWSH_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8Kit.awin_disjoint_shland); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.ASHADOW_BASE_val); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AHI_LO)|] [|@__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @__x2; @__sat4; @Ha; @__x3; @__x4; @__sat11; @__sat10; @H1; @H6; @r0; @q0; @H9; @H8; @H7; @H5; @r; @q; @H4; @H3; @H2; @H; @__x5; @__x6; @__x7; @__x8; @H11; @H10; @__sat5; @z; @__sat8; @__sat6; @__sat7; @__sat9; @KM; @KL; @LE; @G3; @G2; @G1; @L3; @L2; @L1; @Hb; @H0; @FW; @WM; @MU; @SV; @b; @a; @m'; @m; @W|] "#,J#P$d#[#q#f#r#p###y#$#+#(#*#'#%#&#w$S#2#k#/#3#Y#g#1#5#6#I#O#)#,#-#.#0$:#4#8#7#9#?#@#B$]$a$b#S#V#c$#$$#P$9#<#:#;#>#A#C#E#F#G#H$F$E$J$L$V$\$[#N$`$c#T#Z#\#]#^#_#a#b#`#j#m#o#z#{#|$&$'#}#i$<$2$>#=#D$G$I$K$N$M$Q$P$R$W$X$Y#J#K#M#L$Z$d$_$e$^#h#U#e#X$,$*$H$%#d$)$1$($@#u#t#n$6$/$;#x$0$8$7$T#l$+$?#v$3$.$=$A$B$C$D$-#W#s#~$5$4$O$UM$;%$<$$=%$>%$?$$@&$A%$B%$C$$D$$E%$F'$G*$H+$I&$J$$K'$L%$M%$N$$O%$P&$Q%$R$$S%$T%$U%$V&$W%$X%$Y%$Z%$[%$\($]$$^*$_%#(&$`%$a&$b&$c&US>SY$S'$#$#$#$#$#E#US?#E(US?#USZ#k##&#WS[PJHWS\LNPWS]S^LNVS_CCUS`S@WSa$#M#EL#LN)$##LS(USbS$US>S$9CJUScCUSdC<CE4CS'.C$Q#/&GDDF#IZSe'GDDFPF(GDDF$#USfD0*GDDF$#&VSg+FGSASBVShHO(SA#SBm$%#WSiCEJXSjHO$#l#$*)#l#%54#l#&87#j#'C#j#(SC##EH)#J#EJk##$#k#'C#k#(SC##KMH#KOl#)+%##EMm#$#VSkM#,M##M:s#:&%#*M#%'%(C#E)%#))#,K##K&$+*K#%&-(C#E)%#)(#,S/2#+K2#5#%>S%&#j##)#&)8*S/#%+:(C#E)%#,S0##S0,S1&#@*S1#%%B(C#E)%#,S%&#s#&*S%#%%s#((C#E)%#,S22#+S%2#5#%>S&&#j##)#%)s#2(C#E,S)&#s#5*S)#,S#%#s#8(C#E,S&=#s#;#E$#Es#=,S*%#s#?#E#k##&#k##(#6SD6#7C#7C%7CSD1C$#1C&#I#S3JS$#s#r9COUSlC3C$J#4Cs$0.Cs#rQ#/s#tGDDF#I.C%Qs#s/s#vGDDF#IFs#wGDDF%#0s#xGDDF#s#qs#tl#$#s#ps#jl#%+s#{#l#&/s#~#j#'C#j#*C##JH)s#h#k###s#ik#'C#k#*C#HS*S4S%l#))$#l#+s#)B##ES#m#$#VSmS##+S##S##&S#s#h*%#%&s#j(C#E)%#)(#+S&#S&#&S&s#p*%#%&s#r(C#E)%#)(#2s#:+S42#5#%>S5&#j##(#&S4s#|*(#%)s#~(C#E)%#+S*#S*#+S+&S+s$(*$#%%s$*(C#E)%#+S6&S6s$.*$#%%s$0(C#E)%#,S72#+S52#5#%>SE&#j##)#%'s$:(C#E+S7&S7s$=*$#+SF%#s$@(C#E+SG?#s$C(Cs$DEUSn#+SE-#s$G;s$H#%%s$I&$#(C'#k##)#@)s$M*Es$N+So%#s$P#E#*$s$R)$#k##(#A(s$U*s$VE+SH%#s$X*s$Y##$E)$#k##(#B(s$]+S8-#s$_(C#Ek##?#C&s$b+S9%#s$d(C#$k##s#$#-&s$g+SI%#s$i,SJ?#s$k,Sp-#s$m;s$n#%%s$o&$#(C'#k##s#/#@)s$s,SK%#s$u#E#*$s$w)$#k##s#-#A(s$z,SL%#s$|*s$}##$E)$#k##s#,#B(s%%,SM-#s%'(C#Ek##s#C#C&s%*,SN%#s%,(C#$k##s#H#-&s%/,S,%#s%1VSOEs%2GSP#m##s#DUL#*Hs%6)s%E#US2&#EK*Ks%:)$#:s%y's%z'#'#'#:#VSq(#*E)#E%VSr+&*E#k##%#k##'##E/WSs0+Jj##SQ#j#,%##E*k##SQ#k#,(#VSOE6GSP#m##1UJ#6s$n6#7C#7C%1C#s$o1C%#VStCs%ZWSuC#s$rUSvS'VSwC#6+7C#KC%#KC&-1C-s${1C$#1C&#1C,#I#S3VSR0#JS$#s&39CP3Cs${N#9CN3Cs$}O#3C%J#<Cs%n.C#Rs&5/s&7GDDF#IZSxs&8GDDF#'S''#4C#LC)#$&4C#8C%#.Cs&>R#/s&AGDDF#I0s&BGDDF,s&;#.C'Rs&B/s&DGDDF#I4C.8C#3.Cs&ESS#/s&HGDDF#I<Cs#HEs#EWSyC$#.C)Q#/s&MGDDF#I.Cs&LQ%/s&OGDDF#I0s&PGDDF%s&I#0s&QGDDF+s&J#0s&RGDDF0s&K#0s&SGDDF3s&L#l#$#s&Ks&El#%s##s&V#l#&s#)s&Y#j#'C#j#*C#j#-C#j#.C#k##s$RSz;s&9N&#P(CJ#k##&#(CPE&Ps&>*O##Ns#Yk####k##%#k##(#k##*#k#'C#k#*C#k#-C#k#.C#+S-\HS)S2S-#S+S6S5S,l#)6%#l#/s#Ws#c#l#0s#_s#\#l#/s#js#d#l#1s#us#r#l#2s#ys#w#l#3s#~C#l#4s$%C#l#5s$+s$'#l#6s$1s$-#l#7s$9s$3#l#2s$As$;#l#8s$Js$C#l#9s$MC#l#:s$PC#l#;s$Vs$R#l#<s$\s$X#l#=s$es$^#l#1s$ns$g#l#>s$ys$p##s${S(m#$#WS{s$yS(H2s$z2S(#$#,SH=s$us&f#Es$v%s$hs&h#E#k##s&/#k##&#,S8=#s&m#E$,SI%#s&p#E#k##s&7#k##'#,S9?#s&u-)s&v;s&w#&#*(C,#k##s%7#@.s&{,S:%#s&}#E#*$s'#)$#k##s%5#A(s'&%s$ws''*s'(##$E)$#k##s%3#Bs$|s',(Cs$zEk##s%H#Cs$}s'/(Cs$us$vk##s%K#VSTs$xs'2m#SU#+SK?#s'5+SL-#s'7;s'8#%%s'9&$#(C'#k##s%U#@)s'=+SM%#s'?#E#*$s'A)$#k##s%S#A(s'D+SN%#s'F*s'G##$E)$#k##s%R#B(s'K+S,-#s'M(C#Ek##s%i#C&s'P+S|%#s'R(C#$k##s%n#VST&s'Um#SU#UNs%%+S}%#s'Y#E#*$s'[)$#US1s%+,S~%#s'_#E#*$s'a)$#6s$c6#7C#KCs$g#1Cs$ds&~1C$#6'7C#1Cs$ss$r1Cs$k#1C%#1Cs$q#I#S3VSR*#JS$#s(<9CM3C#Ls'(3Cs')O#9CK3C#S.s'+3Cs$jP#3C&J#4Cs%=LCs$j#8C#s$e.Cs$cR#/s(DGDDF#I0s(EGDDFs$ks(>#$s%D4C#LCs$q#4Cs%G8C$#.Cs(IR#/s(LGDDF#I0s(MGDDFs$ss(F#.Cs$qRs(M/s(OGDDF#I.Cs$iQs$p/s(QGDDF#I.C+Rs(Q/s(SGDDF#I8Cs(Rs$}.Cs'ASS#/s(VGDDF#I.Cs'CQs$p/s(XGDDF#IFs(YGDDFs'C#0s(ZGDDF#s(Ss(V0s([GDDF's(T#0s(\GDDF+s(U#0s(]GDDF.s(V#0s(^GDDF1s(W#0s(_GDDF4s(X#0s(`GDDF=s(Y#l#$#s(Xs(Rl#%s#%s(c#l#&s#-s(f#j#'C#j#*C#j#-C#j#.C#j#?C#j#@C#j#AC#j#BC#;s(IK&#S.(CL#k##s$r#&&L(CO#k##s$u#(CME#LM&Ls(R*S.##MK)s(Z#k###s([k##&#k##*#k##*#k##,#k##.#k##2#k#'C#k#*C#k#-C#k#.C#k#?C#k#@C#k#AC#k#BC#+SV-#s(f,S--#s(h%&s(i%%s(jcH'%$(#SVS-&KS)S+SGS8S9S,l#)s#&*#l#1s#ns#i#l#7s#us#p#,T##E#m#%#l#Cs#zs#{#l#Ds$%s#}#l#5s$+s$'#l#6s$3s$-#l#7s$;s$5#l#2s$Ds$=#l#8s$Gs$H#l#;s$Ls$J#l#<s$Ps$N#l#=s$Ws$R#l#1s$_s$Y#l#>s$fs$a#l#+s$os$i#l#Es$ws$r##Es$ym#$#VT$s${#2s$|#S;#2s$w2s'15#$'s%s'#'#'#'#'#'#'#'#'#'#'#'#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#:#:s*(-s%4#&H#-s'L%&H#5#%&&#$s*,$#$#$#$#$#$#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#:##s#*#j#FC##S;s#0j#FC#ZSWCS<#Hs#5S=-s%ns#5&s#7##S;#-s'zs#8&H#-s'>s#:&H##%#j#FC#ZSWCS<#Os#?S=&s#@s#<&s#A(#$#VSXs((s#B#Es()#Es#D+S:-#s#F#E#k##&#k##(#+SJ=#s*6#E$%s%bs*8#E#k##s)[#k##&#VSXs(&s#Q#Es('-s'vs#S#E#k##3#k##&#=s(%s*B#Es(&#Es'vk##s)f#k##%#UNs'S<Cs#^8C#s)X<Cs#2.C$Q#/s*oGDDF#I8C's*nWT%C'#8C$#.C#Q(/s*tGDDF#I0s*uGDDF(s*n#l#$#s*ms*gl#%s)ds*x#l#&s*|s*{#j#'C#j#*C#&s#nJ##s#A&s#pO5#%&&###s#Ek##'#k#'C#k#*C#-s%zs#v-s(4s#wH$#Kl#)/&#l#G@s'|#l#+s#&B#l#Es#-s#(#l#Hs#4s#/#l#Is'{s'x#l#Gs(*s($#l#Js#@s#9#-s&[s$%&s$'#&s$(s#M5#$&%###s#Ym#)#l#Ks#Ls#I#l#Ls#Ws#T#ZT&Cs$/s#[#S<S=&s$Os$M##T'm#%#[T(S@S:s$Rs$PSFH#l#Ls$Vs$T#l#Ks&xs&u#l#Ms&zs&{#j#Ns)>#j#Os)B#V#JHj##s)G#j##s)T#Ds)Us)Ss)K#Hj#>s)Y#j#Ps)`#V#JHj##s)d#j##s)v#Ds)ws)rs)k#Hl#>s*&s)z#j#Qs*S#j#Rs*W#V#JHj##s*\#j##s*i#Ds*js*hs*`#Hj#>s*n#j#Ss*u#V#JHj##s*y#j##s+0#Ds+1s+,s+$#Hl#>s+=s+4#]T)S0S/KMS.LNP#j#Ts+d#j#Us+f#j#Vs+j#j#Ws+n#j#Xs+p#j#Ys+r#j#ZC#j#[C#j#\s+v#j#]T*#j#^s,(##"). Qed.

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
  AMBmid m b es insz n x -> munch W m m' -> wmono asegs m m' -> Forall (mwin b (mb_put_es es insz n x)) W ->
  AMBmid m' b es insz n x.
Proof. intros W m m' b es insz n x MID MU WM FW. unfold AMBmid in *. eapply AMBraw_transport_win; eauto. Qed.

(* [comment removed for export] *)
Lemma AMBraw_obj_rd0 : forall W m m' b es out insz outpos outend g,
  AMBraw m b es out insz outpos outend -> munch W m m' -> wmono asegs m m' -> Forall (mwin b es) W ->
  b <= g -> g + 8 <= b + 64 -> g mod 8 = 0 ->
  ov_read_bytes asegs m' (Z_to_bv 64 (Z.shiftr g 3 + 2147450880)) 1 = Some [b8 0].
Proof.
  intros W m m' b es out insz outpos outend g R MU WM FW H1 H2 H3.
  pose proof (AMBraw_acc _ _ _ _ _ _ _ (AMBraw_transport_win _ _ _ _ _ _ _ _ _ R MU WM FW)) as AC.
  exact (accessible_read0_sr m' b 64 g AC H1 H3 H2).
Qed.

Lemma AMBraw_elem_rd0 : forall W m m' b es out insz outpos outend x s g,
  AMBraw m b es out insz outpos outend -> munch W m m' -> wmono asegs m m' -> Forall (mwin b es) W ->
  In (x, s) es -> x <= g -> g + 8 <= x + mb_block_size s -> g mod 8 = 0 ->
  ov_read_bytes asegs m' (Z_to_bv 64 (Z.shiftr g 3 + 2147450880)) 1 = Some [b8 0].
Proof.
  intros W m m' b es out insz outpos outend x s g R MU WM FW IN H1 H2 H3.
  pose proof (AMBraw_elem_acc _ _ _ _ _ _ _ x s g 8 (AMBraw_transport_win _ _ _ _ _ _ _ _ _ R MU WM FW) IN H1 H2) as AC.
  exact (accessible_read0_sr m' g 8 g AC ltac:(lia) H3 ltac:(lia)).
Qed.

End HCW.
