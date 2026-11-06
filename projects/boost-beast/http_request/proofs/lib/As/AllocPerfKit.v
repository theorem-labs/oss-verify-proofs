(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit AW_LargeAlloc1 AW_PoisonRemap1 AllocTacX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition out_img (W : list ivl) : Prop := Forall (fun r : ivl => snd r <= 65536 \/ 6811648 <= fst r) W.

Lemma out_img_nil : out_img []. Proof. constructor. Qed.
Lemma out_img_cons : forall lo hi W, (hi <= 65536 \/ 6811648 <= lo) -> out_img W -> out_img ((lo, hi) :: W).
Proof. intros lo hi W H HW. constructor; [exact H| exact HW]. Qed.
Lemma out_img_app : forall W1 W2, out_img W1 -> out_img W2 -> out_img (W1 ++ W2).
Proof. intros W1 W2 H1 H2. apply Forall_app. split; assumption. Qed.

Lemma out_img_disjoint : forall W a n, out_img W -> 65536 <= a -> a + n <= 6811648 -> 0 <= n -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Ha Hn Hn0; [exact I|].
  inversion HW as [|r W' Hr HW']; subst. cbn [fst snd] in Hr. cbn [disjoint_from]. split; [| apply IH; assumption].
  destruct Hr as [Hr|Hr]; [right| left]; lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma renv_transport_img : forall g b m m' W,
    RENV g b m -> munch W m m' -> wmono asegs m m' -> out_img W -> RENV g b m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.mem); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_PoisonRemap1.RENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocPerfKit.out_img); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_PoisonRemap1.renv_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocPerfKit.out_img_disjoint); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.ZArith.BinInt.Z.add)|] [|@__ff; @__varmap; @__wit; @__arith; @HW; @WM; @MU; @E; @W; @m'; @m; @b; @g|] "#*Q#,#W#C#H###I#L#G#M#'#V#&#%#2#$#0#/#5#A#Q#R#4#6#7#8#9#:#;#@#B#D#F#N#P#T#S#U#O#<#+#*#)#(#3#1#?#J#E#W#K#>#X#Y#=-#M$#N$#O'#P*#Q%#R%#S$#T&#U%#V*#N##########UP#UQ#UP(UQ#US&#k##&#URS'WS(JLMWS)OLMWS*S+JLUS,L$1$###$#$###$###$###$#####$#######)#$N$#$#######)#US-S#URS#US.CUS/CUS0C#s#,##################)#(C##N####$#$###$#$#####$#$#$###$###$#######)#$N####$#$#$#$#$#$#$#########################)#$s#-##$#####$###$#######$#$#$#$#######)#$2########$###$#$###########)#$s#:$#$###$#$#############$###########)#$)$#######)#$2##########$#$#)#$)$#$#####)#$s#t##$#####$#$###$#####$#######)##s#7##$#$#$#$#####$###########)##s#{$###$#$#$###$#$#$#########)##s#/######$#####$#$#########)##<##$#$#$#$#########)#(Cs$O%Cs$eG#&s$rHDDF#IVS1s$sFVS2S$S%VS3EMWS4S$#S%m$%#WS5CKOXS6EM$#l#$*)#l#%s$}s$|#l#&s%$s%##'s$rs$\l#'$#E(Cs%(*C2##s%0##$###$#$#$#$#$#########################)#(Cs$_%C:G#&s%=HDDF#Il#$#s#)s##l#%s%As%@#l#&s%Ds%C#+s$|s%F'#s$fl#'%#E(CK%C#Gs#$&s%FHDDF#Il#$#s#2s#,l#%s%Js%I#l#&s%Ms%L#'Ks%Ol#'$#E,Js%+s%QEs#,+#$s%z##$#####$###$#$#######$#$#$#######)#)s&0(Cs$r%Cs%VG#&s%cHDDF#Il#$#s#Os#Il#%s%gs%f#l#&s%js%i#'s%\s$xl#'$#E(C+*C+#%C#Gs#2&s%lHDDF#Il#$#s#Xs#Rl#%s%ps%o#l#&s%ss%r#+s%%2'#s%9l#'%#E%Cs#1G,&s%tHDDF#Il#$#s#`s#Zl#%s%xs%w#l#&s%{s%z#'K:l#'$#E,Js%/<E4*#$s#-######$#$#####$###########)##s#f)#(Cs%2%Cs&%G#&s&2HDDF#Il#$#s#zs#tl#%s&6s&5#l#&s&9s&8#'s&+s%8l#'$#E(C+*C+#%C#Gs#]&s&;HDDF#Il#$#s$'s#}l#%s&?s&>#l#&s&Bs&A#+s%A2'#s%dl#'%#E%Cs#\G,&s&CHDDF#Il#$#s$/s$)l#%s&Gs&F#l#&s&Js&I#'K:l#'$#E,Js%K<E4*#$s$'$#$###$#$#######$#$#$#$###########)#(Cs%L%Cs&RG#&s&_HDDF#Il#$#s$Ks$El#%s&cs&b#l#&s&fs&e#'s&Xs%Rl#'$#E*C*s#Z%C#Gs$-&s&gHDDF#Il#$#s$Ss$Ml#%s&ks&j#l#&s&ns&m#+s%Zs#i'#s&4l#'%#E,Js%]s#lE,#s#S$;$#######)#(Cs%^%Cs&jG#&s&wHDDF#Il#$#s$cs$]l#%s&{s&z#l#&s&~s&}#'s&ps%dl#'$#E*C*s#r%C#Gs$E&s'#HDDF#Il#$#s$ks$el#%s''s'&#l#&s'*s')#+s%ls$%'#s&Ll#'%#E,Js%os$(E,#s#k$s#8####$#########$#$#)#)N(Cs%s%Cs',G#&s'9HDDF#Il#$#s%%s${l#%s'=s'<#l#&s'@s'?#'s'2s%yl#'$#E(C+*C+#%C#Gs$d&s'BHDDF#Il#$#s%.s%(l#%s'Fs'E#l#&s'Is'H#+s&&2'#s&kl#'%#E%Cs$cG,&s'JHDDF#Il#$#s%6s%0l#%s'Ns'M#l#&s'Qs'P#'K:l#'$#E,Js&0<E4*#$s#$$#$#####)#(Cs&1%Cs'LG#&s'YHDDF#Il#$#s%Es%?l#%s']s'\#l#&s'`s'_#'s'Rs&7l#'$#E*C*B%C#Gs%'&s'aHDDF#Il#$#s%Ms%Gl#%s'es'd#l#&s'hs'g#+s&?s#1'#s'.l#'%#E,Js&Bs#4E,#;$s()##$###$#####$#$#$###$#######)#(Cs&C%Cs'nG#&s'{HDDF#Il#$#s%gs%al#%s(#s'~#l#&s(&s(%#'s'ts&Il#'$#E*C*s$v%C#Gs%I&s('HDDF#Il#$#s%os%il#%s(+s(*#l#&s(.s(-#+s&Qs%)'#s'Pl#'%#E,Js&Ts%,E,#s$o#s$@$#########$#$#$###########)#(Cs&U%Cs(3G#&s(@HDDF#Il#$#s&,s&&l#%s(Ds(C#l#&s(Gs(F#'s(9s&[l#'$#E*C*s%;%C#Gs%j&s(HHDDF#Il#$#s&4s&.l#%s(Ls(K#l#&s(Os(N#+s&cs%J'#s'ql#'%#E,Js&fs%ME,#s%4#s&'$#$#####$#$###$#$#########)#(Cs&g%Cs(TG#&s(aHDDF#Il#$#s&Ms&Gl#%s(es(d#l#&s(hs(g#'s(Zs&ml#'$#E*C*s%\%C#Gs&/&s(iHDDF#Il#$#s&Us&Ol#%s(ms(l#l#&s(ps(o#+s&us%k'#s(6l#'%#E,Js&xs%nE,#s%U#s#e####$###$#$###$#########)#(Cs&y%Cs(tG#&s)%HDDF#Il#$#s&ms&gl#%s))s)(#l#&s),s)+#'s(zs'#l#'$#E*C*s%|%C#Gs&O&s)-HDDF#Il#$#s&us&ol#%s)1s)0#l#&s)4s)3#+s'+s&/'#s(Vl#'%#E,Js'.s&2E,#s%u#s#B$#$#$#####$#$#########)#(Cs'1%Cs)7G#&s)DHDDF#Il#$#s'0s'*l#%s)Hs)G#l#&s)Ks)J#'s)=s'7l#'$#E*C*s&?%C#Gs&n&s)LHDDF#Il#$#s'8s'2l#%s)Ps)O#l#&s)Ss)R#+s'?s&N'#s(ul#'%#E,Js'Bs&QE,#s&8hS7S8S9S:S;JLMOs&fs&8s%is%Ds%,s$bs$Js$(s#cs#BB#j#(s)s#j#)s)u#j#*s)w#j#+s)y#j#,s){#j#-s)}#j#.S<#j#/s*%#j#0s*(##"). Qed.

  (* [comment removed for export] *)
  Lemma senv_transport_img : forall tp TSD CTX TH m m' W,
    SENV tp TSD CTX TH m -> munch W m m' -> wmono asegs m m' -> out_img W ->
    65536 <= bv_unsigned tp + -88 -> bv_unsigned tp + -88 + 8 <= 6811648 ->
    65536 <= TSD -> TSD + 8 <= 6811648 ->
    disjoint_from W (CTX + 152) 8 ->
    SENV tp TSD CTX TH m'.
  Proof.
    ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.mem); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_LargeAlloc1.SENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocPerfKit.out_img); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_LargeAlloc1.senv_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocPerfKit.out_img_disjoint); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None)|] [|@__ff; @__varmap; @__wit; @__arith; @__x1; @DC; @D2; @D1; @T2; @T1; @HW; @WM; @MU; @E; @W; @m'; @m; @TH; @CTX; @TSD; @tp|] "#+&#4#f#;#U#V#T###Y#Z#(#,#$#c#&#%#:#2#'#.#/#8#7#>#)#-#+#O#^#_#1#=#?#@#A#B#C#D#I#K#N#P#Q#S#[#]#a#`#b#\#e#g#h#3#L#0#*#<#9#J#E#W#R#G#X#F#d#M#H#f0#Z$#[$#\%#]'#^*#_%#`%#a$#b&#c*#d%#e+#'%#P##########US%#US&#US%(US&#US/#k##&#US'S0YS1S(JRNOWS2LNOWS3S4RNUS5N#.##################*#-8S)$?$#######US6#()#%+#-AS#(#&*s#'($#$P####$###$#$#$#$#$#########################*#$P####$#$#$#$#$#$#$#########################*##P##$###$#######$#$#####$#$#$###########*##*$#$#$#####*##=$#$###$#$#####$#$#$###$###$#######*#$s#+##$#######$#$#$#$#######*#$s#:########$###$#$###########*#$s#d$#$###$#$#############$###########*#$)$#######*#$2##$###$#$#####*#$s#R##$#####$#$###$#####$#######*##s#1##$#$#$#$#####$###########*#$;##############*#%s$ks$=%s$yS#(S$s$n%#s$@$s%:$#######*#(S$#WS7S*#s$w#*$#######$#$#$###$###$###########*#US8S+US'S+US9CUS:CUS;C)Cs%?)Cs$L&C$H#'&FDDE#IVS<'EVS=S,S-VS>GOWS?S,#S-m$%#WS@CMLXSAGO$#l#$*)#l#%10#l#&43#%s%Ms$Yl#'$#G)Cs%C+C2#)Cs$r&C$H#'7FDDE#Il#$#3-l#%;:#l#&>=#(s$cs%K%#s$yl#'%#G)CM&C#H.'@FDDE#Il#$#<6l#%s#$s###l#&s#'s#&#%Ms%Tl#'$#G,Ks$ns%VJ6+#-s%xQ(#s%]VSBCLVSCCP)Cs%`+C$#&Cs#,H#'s#.FDDE#IUSDD.s#0FDDE$#$l#$#s#,s#&l#%+s#3#l#&s#7s#6#j#(C#(Gs%j%s%r#(Ls%l%s%t#k##%#k#(C#-s&0SE/#Jl#'+%#+C4s#-&C#Hs#,'s#@FDDE#I.s#AFDDE#4#l#$#s#=s#7l#%<s#D#l#&s#Hs#G#j#(C#(3s%v%#s%H(3s%x%#s%Jk##%#k#(C#/3Rl#'*$#,Ks#(s%~J3#s#+&Cs#NHs#''s#PFDDE#I.s#QFDDE#s#$#l#$#s#Ms#Gl#%s#,s#T#l#&s#Xs#W#j#(C#%s&6G%s&7Lk##$#k#(C#/QNl#'($#+Cs#4s#K&C#Hs#J's#^FDDE#I.s#_FDDE#s#2#l#$#s#[s#Ul#%s#:s#b#l#&s#fs#e#j#(C#(Gs&8%#s%f(Ls&:%#s%hk##%#k#(C#/QOl#'*$#,KS.s&@J3#s#I#s#y$#$#$#####*#*P)Cs%Z&Cs#uH#'s#wFDDE#Il#$#s#ss#ml#%s#{s#z#l#&s#~s#}#%s&[s%`l#'$#G)C++C+#&C#Hs#l's$$FDDE#Il#$#s#|s#vl#%s$(s$'#l#&s$+s$*#(s%i2%#s&*l#'%#G&Cs#kH,'s$,FDDE#Il#$#s$(s#~l#%s$0s$/#l#&s$3s$2#%M:l#'$#G,Ks%s<J4*#$s',$###$#$###$###$###$#####$#######*#$s&s$#######*#)Cs%y&Cs$KH#'s$MFDDE#Il#$#s$Is$Cl#%s$Qs$P#l#&s$Ts$S#%s'1s&#l#'$#G)C++C+#&C#Hs$B's$VFDDE#Il#$#s$Rs$Ll#%s$Zs$Y#l#&s$]s$\#(s&,2%#s&\l#'%#G&Cs$AH,'s$^FDDE#Il#$#s$Zs$Tl#%s$bs$a#l#&s$es$d#%M:l#'$#G,Ks&6<J4*#$s$x##$#$#######$#$#$#######*#)Cs&7&Cs$sH#'s$uFDDE#Il#$#s$qs$kl#%s$ys$x#l#&s$|s${#%s'Ys&=l#'$#G+C*s$j&C#Hs$i's$}FDDE#Il#$#s$ys$sl#%s%%s%$#l#&s%(s%'#(s&Es'U%#s''l#'%#G,Ks&Hs'XJ,#s$a$s%=######$#$#####$###########*##s'd*#)Cs&K&Cs%:H#'s%<FDDE#Il#$#s%8s%2l#%s%@s%?#l#&s%Cs%B#%s'|s&Ql#'$#G)C++C+#&C#Hs%1's%EFDDE#Il#$#s%As%;l#%s%Is%H#l#&s%Ls%K#(s&Z2%#s'Kl#'%#G&Cs%0H,'s%MFDDE#Il#$#s%Is%Cl#%s%Qs%P#l#&s%Ts%S#%M:l#'$#G,Ks&d<J4*#$s(%$#$###$#$#######$#$#$#$###########*#)Cs&e&Cs%gH#'s%iFDDE#Il#$#s%es%_l#%s%ms%l#l#&s%ps%o#%s(Ms&kl#'$#G+C*s%^&C#Hs%]'s%qFDDE#Il#$#s%ms%gl#%s%us%t#l#&s%xs%w#(s&ss(I%#s'wl#'%#G,Ks&vs(LJ,#s%U$;$#######*#)Cs&w&Cs&#H#'s&%FDDE#Il#$#s%}s%wl#%s&)s&(#l#&s&,s&+#%s(es&}l#'$#G+C*s%v&C#Hs%u's&-FDDE#Il#$#s&)s&#l#%s&1s&0#l#&s&4s&3#(s')s(a%#s(3l#'%#G,Ks',s(dJ,#s%m$s#8####$#$###$#$#####*#)Cs'/&Cs&@H#'s&BFDDE#Il#$#s&>s&8l#%s&Fs&E#l#&s&Is&H#%s)&s'5l#'$#G+C*s%)&C#Hs&6's&JFDDE#Il#$#s&Fs&@l#%s&Ns&M#l#&s&Qs&P#(s'=s%8%#s(Pl#'%#G,Ks'@s%;J,#s$~$s$|##$###$#####$#$#$###$#######*#)Cs'A&Cs&bH#'s&dFDDE#Il#$#s&`s&Zl#%s&hs&g#l#&s&ks&j#%s)Hs'Gl#'$#G+C*s&Y&C#Hs&X's&lFDDE#Il#$#s&hs&bl#%s&ps&o#l#&s&ss&r#(s'Os)D%#s(rl#'%#G,Ks'Rs)GJ,#s&P#s#{$#########$#$#$###########*#)Cs'S&Cs''H#'s')FDDE#Il#$#s'%s&{l#%s'-s',#l#&s'0s'/#%s)is'Yl#'$#G+C*s&z&C#Hs&y's'1FDDE#Il#$#s'-s''l#%s'5s'4#l#&s'8s'7#(s'as)e%#s)7l#'%#G,Ks'ds)hJ,#s&q$s#@####$###########*#)Cs'f&Cs'CH#'s'EFDDE#Il#$#s'As';l#%s'Is'H#l#&s'Ls'K#%s*)s'll#'$#G+C*s':&C#Hs'9's'MFDDE#Il#$#s'Is'Cl#%s'Qs'P#l#&s'Ts'S#(s'ts*%%#s)Sl#'%#G,Ks'ws*(J,#s'1i#;SFQS.SGS$S#S)KS*SHS(s'1s&es&GGs&%s%Os%/s$`s$;s$#s#bs#@?#j#)s'm#j#*s'v#j#+s'y#j#,s'{#j#-s*1#j#.s*F#j#/s*H#j#0s*J#j#1s*L#j#2s*N#j#3s*P#j#4SI#j#5C#j#6C#j#7C#j#8s*Y##"). Qed.
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
