(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsAtomics.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocWalkKit AW_LargeAlloc1 AW_PoisonRemap1 AllocTacX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition out_img (W : list ivl) : Prop := Forall (fun r : ivl => snd r <= 65536 \/ 6832128 <= fst r) W.

Lemma out_img_nil : out_img []. Proof. constructor. Qed.
Lemma out_img_cons : forall lo hi W, (hi <= 65536 \/ 6832128 <= lo) -> out_img W -> out_img ((lo, hi) :: W).
Proof. intros lo hi W H HW. constructor; [exact H| exact HW]. Qed.
Lemma out_img_app : forall W1 W2, out_img W1 -> out_img W2 -> out_img (W1 ++ W2).
Proof. intros W1 W2 H1 H2. apply Forall_app. split; assumption. Qed.

Lemma out_img_disjoint : forall W a n, out_img W -> 65536 <= a -> a + n <= 6832128 -> 0 <= n -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Ha Hn Hn0; [exact I|].
  inversion HW as [|r W' Hr HW']; subst. cbn [fst snd] in Hr. cbn [disjoint_from]. split; [| apply IH; assumption].
  destruct Hr as [Hr|Hr]; [right| left]; lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma renv_transport_img : forall g b m m' W,
    RENV g b m -> munch W m m' -> wmono bsegs m m' -> out_img W -> RENV g b m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.mem); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_PoisonRemap1.RENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocPerfKit.out_img); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_PoisonRemap1.renv_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocPerfKit.out_img_disjoint); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.ZArith.BinInt.Z.add)|] [|@__ff; @__varmap; @__wit; @__arith; @HW; @WM; @MU; @E; @W; @m'; @m; @b; @g|] "#*Q#,#W#C#H###I#L#G#M#'#V#&#%#2#$#0#/#5#A#Q#R#4#6#7#8#9#:#;#@#B#D#F#N#P#T#S#U#O#<#+#*#)#(#3#1#?#J#E#W#K#>#X#Y#=-#M$#N$#O'#P*#Q%#R%#S$#T&#U%#V*#N##########UP#UQ#UP(UQ#US&#k##&#URS'WS(JLMWS)OLMWS*S+JLUS,L$1$#$#$#$#$###############$#######)#$N$#$#######)#US-S#URS#US.CUS/CUS0C#s#,##################)#(C##N####$#$#$#$#$###$#$#####$#$###$#######)#$N##$#########$#############################)#$s#-##$#$###$###$#$#$#$###$#$#$#######)#$2####$#####$###$###########)#$s#9$#$#$#$#####$#$###$#$###########)#$)$#######)#$2$#########$#$#)#$)$#$#####)##s#J####$###$#$###########$#######)##s#8$#####$#####$#$###########)##s#|##$#$###$###$###$#$#########)##s#0####$#$#$#$#$#$#########)##<######$#$#########)#(Cs$P%Cs$fG#&s$sHDDF#IVS1s$tFVS2S$S%VS3EMWS4S$#S%m$%#WS5CKOXS6EM$#l#$*)#l#%s$~s$}#l#&s%%s%$#'s$ss$]l#'$#E(Cs%)*C2##s%1##$#$#####$#############################)#(Cs$`%C:G#&s%>HDDF#Il#$#s#)s##l#%s%Bs%A#l#&s%Es%D#+s$}s%G'#s$gl#'%#E(CK%C#Gs#$&s%GHDDF#Il#$#s#2s#,l#%s%Ks%J#l#&s%Ns%M#'Ks%Pl#'$#E,Js%,s%REs#,+#$s%{##$#$###$#$#####$###$#$#$#$#######)#)s&1(Cs$s%Cs%WG#&s%dHDDF#Il#$#s#Os#Il#%s%hs%g#l#&s%ks%j#'s%]s$yl#'$#E(C+*C+#%C#Gs#2&s%mHDDF#Il#$#s#Xs#Rl#%s%qs%p#l#&s%ts%s#+s%&2'#s%:l#'%#E%Cs#1G,&s%uHDDF#Il#$#s#`s#Zl#%s%ys%x#l#&s%|s%{#'K:l#'$#E,Js%0<E4*#$s#-####$#$#####$#$###########)##s#f)#(Cs%3%Cs&&G#&s&3HDDF#Il#$#s#zs#tl#%s&7s&6#l#&s&:s&9#'s&,s%9l#'$#E(C+*C+#%C#Gs#]&s&<HDDF#Il#$#s$'s#}l#%s&@s&?#l#&s&Cs&B#+s%B2'#s%el#'%#E%Cs#\G,&s&DHDDF#Il#$#s$/s$)l#%s&Hs&G#l#&s&Ks&J#'K:l#'$#E,Js%L<E4*#$s$'$#$#$#$#$###$###$#####$###########)#(Cs%N%Cs&SG#&s&`HDDF#Il#$#s$Ks$El#%s&ds&c#l#&s&gs&f#'s&Ys%Tl#'$#E*C*s#Z%C#Gs$-&s&hHDDF#Il#$#s$Ss$Ml#%s&ls&k#l#&s&os&n#+s%\s#i'#s&5l#'%#E,Js%_s#lE,#s#S$;$#######)#(Cs%`%Cs&kG#&s&xHDDF#Il#$#s$cs$]l#%s&|s&{#l#&s'#s&~#'s&qs%fl#'$#E*C*s#r%C#Gs$E&s'$HDDF#Il#$#s$ks$el#%s'(s''#l#&s'+s'*#+s%ns$%'#s&Ml#'%#E,Js%qs$(E,#s#k$s#6##########$#$#)#)N(Cs%s%Cs'+G#&s'8HDDF#Il#$#s%#s$yl#%s'<s';#l#&s'?s'>#'s'1s%yl#'$#E(C+*C+#%C#Gs$b&s'AHDDF#Il#$#s%,s%&l#%s'Es'D#l#&s'Hs'G#+s&&2'#s&jl#'%#E%Cs$aG,&s'IHDDF#Il#$#s%4s%.l#%s'Ms'L#l#&s'Ps'O#'K:l#'$#E,Js&0<E4*#$s#$$#$#####)#(Cs&1%Cs'KG#&s'XHDDF#Il#$#s%Cs%=l#%s'\s'[#l#&s'_s'^#'s'Qs&7l#'$#E*C*B%C#Gs%%&s'`HDDF#Il#$#s%Ks%El#%s'ds'c#l#&s'gs'f#+s&?s#1'#s'-l#'%#E,Js&Bs#4E,#;#s$w####$###$#$#$#$###$###$#######)#(Cs&C%Cs'nG#&s'{HDDF#Il#$#s%fs%`l#%s(#s'~#l#&s(&s(%#'s'ts&Il#'$#E*C*s$u%C#Gs%H&s('HDDF#Il#$#s%ns%hl#%s(+s(*#l#&s(.s(-#+s&Qs%('#s'Pl#'%#E,Js&Ts%+E,#s$n#s$?$###$#########$###########)#(Cs&U%Cs(3G#&s(@HDDF#Il#$#s&+s&%l#%s(Ds(C#l#&s(Gs(F#'s(9s&[l#'$#E*C*s%:%C#Gs%i&s(HHDDF#Il#$#s&3s&-l#%s(Ls(K#l#&s(Os(N#+s&cs%I'#s'ql#'%#E,Js&fs%LE,#s%3#s&'##$#$#$#####$#$#$#$#########)#(Cs&g%Cs(UG#&s(bHDDF#Il#$#s&Ms&Gl#%s(fs(e#l#&s(is(h#'s([s&ml#'$#E*C*s%\%C#Gs&/&s(jHDDF#Il#$#s&Us&Ol#%s(ns(m#l#&s(qs(p#+s&us%k'#s(7l#'%#E,Js&xs%nE,#s%U#s#f##$###$#$#####$#########)#(Cs&y%Cs(uG#&s)&HDDF#Il#$#s&ms&gl#%s)*s))#l#&s)-s),#'s({s'#l#'$#E*C*s%|%C#Gs&O&s).HDDF#Il#$#s&us&ol#%s)2s)1#l#&s)5s)4#+s'+s&/'#s(Wl#'%#E,Js'.s&2E,#s%u#s#A$#####$#$#$#########)#(Cs'0%Cs)7G#&s)DHDDF#Il#$#s'/s')l#%s)Hs)G#l#&s)Ks)J#'s)=s'6l#'$#E*C*s&>%C#Gs&m&s)LHDDF#Il#$#s'7s'1l#%s)Ps)O#l#&s)Ss)R#+s'>s&M'#s(ul#'%#E,Js'As&PE,#s&7hS7S8S9S:S;JLMOs&es&7s%hs%Cs%+s$cs$Ks$(s#cs#AA#j#(s)s#j#)s)u#j#*s)w#j#+s)y#j#,s){#j#-s)}#j#.S<#j#/s*%#j#0s*(##"). Qed.

  (* [comment removed for export] *)
  Lemma senv_transport_img : forall tp TSD CTX TH m m' W,
    SENV tp TSD CTX TH m -> munch W m m' -> wmono bsegs m m' -> out_img W ->
    65536 <= bv_unsigned tp + -88 -> bv_unsigned tp + -88 + 8 <= 6832128 ->
    65536 <= TSD -> TSD + 8 <= 6832128 ->
    disjoint_from W (CTX + 152) 8 ->
    SENV tp TSD CTX TH m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.mem); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_LargeAlloc1.SENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocPerfKit.out_img); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_LargeAlloc1.senv_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocPerfKit.out_img_disjoint); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None)|] [|@__ff; @__varmap; @__wit; @__arith; @__x1; @DC; @D2; @D1; @T2; @T1; @HW; @WM; @MU; @E; @W; @m'; @m; @TH; @CTX; @TSD; @tp|] "#*{#4#f#;#U#V#T###Y#Z#(#,#$#c#&#%#:#2#'#.#/#8#7#>#)#-#+#O#^#_#1#=#?#@#A#B#C#D#I#K#N#P#Q#S#[#]#a#`#b#\#e#g#h#3#L#0#*#<#9#J#E#W#R#G#X#F#d#M#H#f0#Z$#[$#\%#]'#^*#_%#`%#a$#b&#c*#d%#e+#'%#P##########US%#US&#US%(US&#US/#k##&#US'S0YS1S(JRNOWS2LNOWS3S4RNUS5N#.##################*#-8S)$?$#######US6#()#%+#-AS#(#&*s#'($#$P####$#$#####$#############################*#$P##$#########$#############################*##P##$###$#$###$#############$###########*##*$#$#$#####*##=$#$#$#$#$###$#$#####$#$###$#######*#$s#)$#$#$###$#$#$#######*#$s#8####$#####$###$###########*#$s#a$#$#$#$#####$#$###$#$###########*#$)$#######*#$2$#$###$#$#####*##s#j####$###$#$###########$#######*##s#2$#####$#####$#$###########*#$:############*#%s$hs$:%s$vS#(S$s$k%#s$=$s%7$#######*#(S$#WS7S*#s$t#*$#$###$#######$#$#$#$###########*#US8S+US'S+US9CUS:CUS;C)Cs%<)Cs$I&C$H#'&FDDE#IVS<'EVS=S,S-VS>GOWS?S,#S-m$%#WS@CMLXSAGO$#l#$*)#l#%10#l#&43#%s%Js$Vl#'$#G)Cs%@+C2#)Cs$o&C$H#'7FDDE#Il#$#3-l#%;:#l#&>=#(s$`s%H%#s$vl#'%#G)CM&C#H.'@FDDE#Il#$#<6l#%s#$s###l#&s#'s#&#%Ms%Ql#'$#G,Ks$ks%SJ6+#-s%uQ(#s%ZVSBCLVSCCP)Cs%]+C$#&Cs#,H#'s#.FDDE#IUSDD.s#0FDDE$#$l#$#s#,s#&l#%+s#3#l#&s#7s#6#j#(C#(Gs%g%s%o#(Ls%i%s%q#k##%#k#(C#-s&-SE/#Jl#'+%#+C4s#-&C#Hs#,'s#@FDDE#I.s#AFDDE#4#l#$#s#=s#7l#%<s#D#l#&s#Hs#G#j#(C#(3s%s%#s%E(3s%u%#s%Gk##%#k#(C#/3Rl#'*$#,Ks#(s%{J3#s#+&Cs#NHs#''s#PFDDE#I.s#QFDDE#s#$#l#$#s#Ms#Gl#%s#,s#T#l#&s#Xs#W#j#(C#%s&3G%s&4Lk##$#k#(C#/QNl#'($#+Cs#4s#K&C#Hs#J's#^FDDE#I.s#_FDDE#s#2#l#$#s#[s#Ul#%s#:s#b#l#&s#fs#e#j#(C#(Gs&5%#s%c(Ls&7%#s%ek##%#k#(C#/QOl#'*$#,KS.s&=J3#s#I#s#y$#$#$#####*#*P)Cs%W&Cs#uH#'s#wFDDE#Il#$#s#ss#ml#%s#{s#z#l#&s#~s#}#%s&Xs%]l#'$#G)C++C+#&C#Hs#l's$$FDDE#Il#$#s#|s#vl#%s$(s$'#l#&s$+s$*#(s%f2%#s&'l#'%#G&Cs#kH,'s$,FDDE#Il#$#s$(s#~l#%s$0s$/#l#&s$3s$2#%M:l#'$#G,Ks%p<J4*#$s')$#$#$#$#$###############$#######*#$s&p$#######*#)Cs%v&Cs$KH#'s$MFDDE#Il#$#s$Is$Cl#%s$Qs$P#l#&s$Ts$S#%s'.s%|l#'$#G)C++C+#&C#Hs$B's$VFDDE#Il#$#s$Rs$Ll#%s$Zs$Y#l#&s$]s$\#(s&)2%#s&Yl#'%#G&Cs$AH,'s$^FDDE#Il#$#s$Zs$Tl#%s$bs$a#l#&s$es$d#%M:l#'$#G,Ks&3<J4*#$s$w####$###$#$#$#$#######*#)Cs&5&Cs$rH#'s$tFDDE#Il#$#s$ps$jl#%s$xs$w#l#&s${s$z#%s'Us&;l#'$#G+C*s$i&C#Hs$h's$|FDDE#Il#$#s$xs$rl#%s%$s%##l#&s%'s%&#(s&Cs'Q%#s'#l#'%#G,Ks&Fs'TJ,#s$`$s%<####$#$#####$#$###########*##s'`*#)Cs&I&Cs%9H#'s%;FDDE#Il#$#s%7s%1l#%s%?s%>#l#&s%Bs%A#%s'xs&Ol#'$#G)C++C+#&C#Hs%0's%DFDDE#Il#$#s%@s%:l#%s%Hs%G#l#&s%Ks%J#(s&X2%#s'Gl#'%#G&Cs%/H,'s%LFDDE#Il#$#s%Hs%Bl#%s%Ps%O#l#&s%Ss%R#%M:l#'$#G,Ks&b<J4*#$s'}$#$#$#$#$###$###$#####$###########*#)Cs&d&Cs%fH#'s%hFDDE#Il#$#s%ds%^l#%s%ls%k#l#&s%os%n#%s(Is&jl#'$#G+C*s%]&C#Hs%\'s%pFDDE#Il#$#s%ls%fl#%s%ts%s#l#&s%ws%v#(s&rs(E%#s'sl#'%#G,Ks&us(HJ,#s%T$;$#######*#)Cs&v&Cs%~H#'s&$FDDE#Il#$#s%|s%vl#%s&(s&'#l#&s&+s&*#%s(as&|l#'$#G+C*s%u&C#Hs%t's&,FDDE#Il#$#s&(s%~l#%s&0s&/#l#&s&3s&2#(s'(s(]%#s(/l#'%#G,Ks'+s(`J,#s%l$s#6##$###$#$#####*#)Cs',&Cs&=H#'s&?FDDE#Il#$#s&;s&5l#%s&Cs&B#l#&s&Fs&E#%s(|s'2l#'$#G+C*s%&&C#Hs&3's&GFDDE#Il#$#s&Cs&=l#%s&Ks&J#l#&s&Ns&M#(s':s%5%#s(Jl#'%#G,Ks'=s%8J,#s${#s&e####$###$#$#$#$###$###$#######*#)Cs'>&Cs&`H#'s&bFDDE#Il#$#s&^s&Xl#%s&fs&e#l#&s&is&h#%s)Cs'Dl#'$#G+C*s&W&C#Hs&V's&jFDDE#Il#$#s&fs&`l#%s&ns&m#l#&s&qs&p#(s'Ls)?%#s(ml#'%#G,Ks'Os)BJ,#s&N#s#z$###$#########$###########*#)Cs'P&Cs'%H#'s''FDDE#Il#$#s'#s&yl#%s'+s'*#l#&s'.s'-#%s)ds'Vl#'$#G+C*s&x&C#Hs&w's'/FDDE#Il#$#s'+s'%l#%s'3s'2#l#&s'6s'5#(s'^s)`%#s)2l#'%#G,Ks'as)cJ,#s&o$s#>$###########*#)Cs'b&Cs'?H#'s'AFDDE#Il#$#s'=s'7l#%s'Es'D#l#&s'Hs'G#%s)~s'hl#'$#G+C*s'6&C#Hs'5's'IFDDE#Il#$#s'Es'?l#%s'Ms'L#l#&s'Ps'O#(s'ps)z%#s)Ll#'%#G,Ks'ss)}J,#s'-i#;SFQS.SGS$S#S)KS*SHS(s'-s&as&CGs%}s%Ks%,s$]s$8s#|s#as#>=#j#)s'i#j#*s'r#j#+s'u#j#,s'w#j#-s**#j#.s*?#j#/s*A#j#0s*C#j#1s*E#j#2s*G#j#3s*I#j#4SI#j#5C#j#6C#j#7C#j#8s*R##"). Qed.
End HCW.

(* [comment removed for export] *)
Ltac out_img_tac tac :=
  repeat first [ apply out_img_nil | apply out_img_cons; [ tac | ] ].

(* [comment removed for export] *)
Ltac renv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with AW_PoisonRemap1.RENV ?g ?b m =>
      assert (E' : AW_PoisonRemap1.RENV g b m');
      [ apply (renv_transport_img g b m m' W E MU WM); out_img_tac ltac:(cbn [fst snd]; region_decide) | ]
    end end.
Ltac senv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with SENV ?tp ?TSD ?CTX ?TH m =>
      assert (E' : SENV tp TSD CTX TH m');
      [ apply (senv_transport_img tp TSD CTX TH m m' W E MU WM);
        [ out_img_tac ltac:(cbn [fst snd]; region_decide) | .. ]; cbn [disjoint_from]; region_decide | ]
    end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parked (P : Prop) : Prop := P.
Lemma park : forall P : Prop, P -> parked P. Proof. intros P p. exact p. Qed.
Lemma unpark : forall P : Prop, parked P -> P. Proof. intros P p. exact p. Qed.
Global Opaque parked.

(* [comment removed for export] *)
Ltac park_mem m keep :=
  repeat match goal with
  | H : rw_cells _ m _ _ |- _ => tryif constr_eq H keep then fail else apply park in H
  | H : ro_cells _ m _ _ |- _ => apply park in H
  | H : stk _ m _ _ |- _ => tryif constr_eq H keep then fail else apply park in H
  | H : u8arr _ m _ _ |- _ => apply park in H
  | H : u32arr _ m _ _ |- _ => apply park in H
  | H : u64arr _ m _ _ |- _ => apply park in H
  | H : u8ro _ m _ _ |- _ => apply park in H
  | H : bytes_at _ m _ _ |- _ => apply park in H
  | H : wr_at _ m _ _ |- _ => apply park in H
  end.
Ltac unpark_all := repeat match goal with H : parked _ |- _ => apply unpark in H end.

(* [comment removed for export] *)
Ltac spill_block FR lo hi tac :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m0 _) =>
    let MUP := fresh "MUP" in let WMP := fresh "WMP" in
    pose proof (munch_refl [(lo, hi)] m0) as MUP; pose proof (wmono_refl segs m0) as WMP;
    park_mem m0 FR;
    tac;
    unpark_all;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      transport_after_call segs m0 m1 MUP WMP; clear MUP WMP
    end
  end.

(* [comment removed for export] *)
Ltac spill_frame tac :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    match goal with FRx : rw_cells _ m0 ?A [CB ?n _] |- _ =>
      let hi := lazymatch A with
                | (?b + ?k)%Z => let k' := eval vm_compute in (k + Z.of_nat n)%Z in constr:((b + k')%Z)
                | _ => constr:((A + Z.of_nat n)%Z)
                end in
      spill_block FRx A hi tac
    end
  end.

(* [comment removed for export] *)
Ltac st1f := step; fix_lit_store; try (rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned by lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac join_open JT JOIN := evar (JT : Prop); cut JT; [ intros JOIN | ].
Ltac join_here JT JOIN :=
  lazymatch goal with |- ?G => let e := eval unfold JT in JT in unify e G end; unfold JT in JOIN; exact JOIN.
Ltac join_here1 JT JOIN r :=
  lazymatch goal with |- evt ?s ?P (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    let e := eval unfold JT in JT in
    unify e (forall x : word, evt s P (MS (bvmap_set r x R) F pc fc rv mm ro)) end;
  unfold JT in JOIN; eapply JOIN.
Ltac join_here3 JT JOIN r1 r2 r3 :=
  lazymatch goal with |- evt ?s ?P (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    let e := eval unfold JT in JT in
    unify e (forall x y z : word, evt s P (MS (bvmap_set r1 x (bvmap_set r2 y (bvmap_set r3 z R))) F pc fc rv mm ro)) end;
  unfold JT in JOIN; eapply JOIN.
Ltac join_again JT JOIN := unfold JT in JOIN; first [ exact JOIN | eapply JOIN ].
