(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame TacX Bytes StoreDj.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AXRep AXRep2 AXPRep AXPRep2 AXRep_leafP N8Kit N8Kit2 N8Kit3 X8Kit X8Call X8LeafKit X8StateKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section KIT.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition ex_bnd (B lo shi : Z) (sp : word) (E : Z) : Prop :=
    lo + B <= bv_unsigned sp /\ aceil <= lo /\ bv_unsigned sp + 64 <= shi /\ 0 <= bv_unsigned sp < 2^64
    /\ 6811648 <= E /\ E + 24 <= aceil /\ E + 24 < 2^47 /\ 0 < E
    /\ 140735332483072 <= aceil <= 140737479966720.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

  Lemma ex_bnd_intro : forall B lo shi sp E,
    lo + B <= bv_unsigned sp -> aceil <= lo -> bv_unsigned sp + 64 <= shi -> aapp E 24 -> ex_bnd B lo shi sp E.
  Proof.
    ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil); constr:(HCEIL); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aapp); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aapp_bounds); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.AIMG_TOP); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8StateKit2.KIT.ex_bnd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil_facts); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof)|] [|@__ff; @__varmap; @__wit; @__arith; @Ha; @__x1; @__x2; @__x3; @__sat8; @__sat6; @__sat7; @__p1; @__sat10; @__sat9; @SPR; @AF3; @AF2; @H; @AF1; @EB5; @EB4; @EB3; @EB2; @EB1; @APE; @SHI; @CEIL; @LO; @E; @sp; @shi; @lo; @B|] "#*B#L$:#O#e#i#f#d#$###k#j#%#w#L#'#B#&#(#X#-#1#.#E$&#S#^#u#,#+#)#0#/#>#F#D#J$3#Q#n#o#p#q#*#5#4#3#2#6#;#?#C$$$%$'$4#G$9$:$7#P#W#Z#]#_#`#a#c#l#r#s#m#\#x#9#8#7#{#|#=#<#:#A#@#}#~$($*$)$0#H#K#I$2$6$;$5#R#T#t#[#v#U#g#b$-$##Y#h#z#y#V$1$+$/$,$.$89$%$$&%$'%$($$)%$*%$+'$,*$-+$.'$/$$0%$1(#)&$2($3%$4*$5'$6%$7%$8&$9%#S)##########US6#USL#(QO2%H$$#USMS#$#O2)Q-+($#$#O&S)######-#WSNS#Q#USOS*USPS*USQCUSRCUSSC.CE.C*)C$K#*&GDDF#JVST'FVS7S8S9VSUILWS:S8#S9m$%#WSVCEHXSWIL$#l#$*)#l#%10#l#&43#$E7l#'$#Im##$YSXS#O:I#$S+O(O<$#s#''$M'EOUSYS#$s#+#%%#%'#%)#%,#$S+R(Rs#'$#s#2'$M'ER%#,%%#%'#%*#/S$S,S-S;S.j##$#(S.s#1$#s#<'$M'ES.%#6%%#%'#$S+S;(S-s#9$#s#D'$M'ES-%#>%%#%'#(S,s#@$#s#K'$M'ES,%#s#%%%#%'#/S%S/S0S&S$j##$#(S$s#I'#M'ES$%#s#-%%#(S&s#N$#s#Y(S0s#P'#M'ES0%#s#4%%#(S/s#U'#M'ES/%#s#9%%#/S<S=S>S?S%j##$#'ES%%#s#>(S?s#^'#M'ES>%#s#B'ES=%#s#D/SZS[S\S@S<j##$#'ES@US]S#&s#l&#&#&#&#&#&#&#&#&#&#&#&###&#&#&#&#&#&#&#&###############################################-#$#s$D&s#%&#&#&#&#&#&#&#&###############################################-#$s$f#%s#%##s$n##########-#VS^s$o#WS:C#E(s$q%'s$J#%s$J#%&#%0#/S1S_S`SASaj##$#/PSbScSBS1j##'#VSds%#P2s%$P$E#USes%&'%#%%#(S'S22s%*SC$$#$s%'S'(%s%%$#S3$E'-s%6VSD#s%)'*#%&#&s%'##&#&#&#&#&#########################-#&S)####&#&#&#&#&#&#&#########################-#$#P(Ps%Q$#s%\&s%h&#&#&#-#VSDs#9#'*#'EP%#s#\%%#%-#%0#%s#=#%s#C#%s#F#VSEs#Cs%i'Es#D$Es%k'Es#Ek##$#k##&#$Es#IWSFs#Js%pHj##S(#j#(%#$Es#Lk##S(#k#((#VSfs%ys#i$Es%z$Es#k$Es#kk##$#k##&#VSgEs#VVS7Sh#m##6UL#6CL6CQ4C$H#5CS)5Cs&67C$#5Cs&')C$K#*s%{GDDF#JUSiD+s%}GDDF$#$l#$#s%ys%sl#%,s&$#l#&s&(s&'#j#)C#j#*C#j#+C#(IH$#L(HL$#Qk##%#k#)C#k#*C#k#+C#2s&ESjXI#SkS4S2l#'-%#l#,?s#1#l#-s#)s#$#l#.s#.s#+#l#,s#8s#3#m##s$#4Cs##Hs&:)CAK@*s&:GDDF#J+s&;GDDF#=#l#$#s&7s&1l#%'s&>#l#&s&Bs&A#j#)C#j#*C#$IH$HLk##$#k#)C#k#*C#0S4s&VS'l#')$#l#,s#4s#F#l#-s#>s#9#l#.s#Cs#@#l#,s#Ms#H#m##s$7.Cs&Z7Cs#6#)C#Ks#6*s&PGDDF#J+s&QGDDF#s#3#l#$#s&Ms&Gl#%=s&T#l#&s&Xs&W#j#)C#j#*C#(Is&d$#H(Hs&f$#Lk##%#k#)C#k#*C#0Sls#0S3l#'+$#l#,s#Ls#^#l#-s#Vs#Q#l#.s#[s#X#l#,s#es#`#m##s$M6CH)Cs&eKs#N*s&gGDDF#JZSms&hGDDFQ3s&iGDDF$#+s&jGDDF#s#L%l#$#s&fs&`l#%)s&m#l#&s&qs&p#j#)C#j#/N#$EI%#H$EHk##$#k#)C#k#/N#'s#Hs$\0#s#IRl#'+%#l#,s#es#w#l#-s#os#j#l#.s#ts#q#l#,s#~s#y#m##s$e.Cs$eWSGC#s'8)Cs#hS5#*s'%GDDF#J3s'&GDDF<#+s''GDDF#s#e$l#$#s'#s&yl#%Bs'*#l#&s'.s'-#j#)C#j#/N#'Is$o%H#'Hs$qk##$#k#)C#k#/N#$Es#a0#s#bRl#'+%#l#,s#~s$4#l#-s$,s$'#l#.s$1s$.#l#,s$;s$6#m##s${,s%#s$|<#.Cs$Q)C#Ks$%*s'>GDDF#J+s'?GDDF#s#}#l#$#s';s'5l#%s#:s'B#l#&s'Fs'E#j#)C#$s$YI$s$ZHk##$#k#)C#VISHSBl#'($#l#,s$6s$H#l#-s$@s$;#l#.s$Es$B#l#,s$Os$J#m##s$b7Cs$7s'M)C#Ks$7*s'QGDDF#J+s'RGDDF#s$4#l#$#s'Ns'Hl#%s#zs'U#l#&s'Ys'X#j#)C#j#*C#(Is'^$#H(Hs'`$#Lk##%#k#)C#k#*C#0s'oSHSAl#'+$#l#,s$Ms$_#l#-s$Ws$R#l#.s$\s$Y#l#,s$fs$a#m##s$wVSEs%Ms$s$Es$t'Es$tk##$#k##s$k#WSFs%Rs$xHj##S(#j#(s$i#$Es$zk##S(#k#(s$l#URs$^USISJUSI#8C#8C%8CSJWSKC$#WSKC&#VSn#SoWSpS*#s'~4Cs$fLs'}4Cs'~H#.Cs&L5Cs%3)C$K#*s($GDDF#J.Cs&.)C&K#*s('GDDF#J3s((GDDF&#)Cs#8K)*s(*GDDF#JUS6s%9WSGCs#h#)Cs#<S5#*s(.GDDF#J+s(/GDDF's$m#+s(0GDDF*s$n#l#$#s(,s(&l#%4s(3#l#&7s(6#j#)C#j#*C#$s&aH$Hs&@%$#(Ls(?'#s%Fk##s#>#k##&#k#)C#k#*C#XIs(OS4S%S1l#'-$#l#0s#.s#6#l#,s%.s%@#l#-s%8s%3#l#.s%=s%:#l#,s%Gs%B#l#1s#7s#4#l#0s#?s#;#m##s%S)Cs(HS5s%1*s(JGDDF#J+s(KGDDFs#ks%-#l#$#s(Gs(Al#%s$Fs(N#l#&s(Rs(Q#j#)C#'EHk##s#k#k#)C#l#'&#s#il#,s%@s%R#l#-s%Js%E#l#.s%Os%L#l#,s%Ys%T#m##s%b)Cs#:Ks%A*s(ZGDDF#J3s([GDDF#s$Q+s(\GDDF#s%>$l#$#s(Xs(Rl#%s$Ws(_#l#&s(cs(b#j#)C#j#/N#$s'1I%#Hk###s#0k#)C#k#/N#0s&os(wS&l#')$#l#,s%Us%g#l#-s%_s%Z#l#.s%ds%a#l#,s%ns%i#m##s';)Cs%VKs#K*s(oGDDF#J3s(pGDDFs$f#+s(qGDDF#s%S$l#$#s(ms(gl#%s$ls(t#l#&s(xs(w#j#)C#j#/N#$Is'$%H#k###s#Dk#)C#k#/N#0s'Js)0S&l#')$#l#,s%js%|#l#-s%ts%o#l#.s%ys%v#l#,s&'s%~#m##s'.,s'Qs'/8#,s&2s'/s#.#,s&4s&2s#?#,s&<s&2s$##,s&?s&2s$;#,s&ls&2s$O#,s&rs&2s%'#,s&us&2s%@#,s&ws&2s%V#/S2S'S3SCPm#$#l#2s'&s&}#j#3s'.#j#4s'2#V#HIj##s'1#j##s'5#1s'6s'3s'-#Ij#5s'3#j#6s'A#V#HIj##s'6#j##s'D#1s'Es'8s'5#Il#5s(<s'8#j#7s)'#j#8s(?#V#HIj##s)*#j##s(F#1s(Gs),s(D#Ij#5s(I#j#9s(L#V#HIj##s(P#j##s(X#1s(Ys(Ws(T#Ij#5s(\#j#:s(b#V#HIj##s(f#j##s(s#1s(ts(ps(m#Ij#5s(w#j#;s)##V#HIj##s)&#j##s)8#1s)9s)2s)/#Il#5s)Fs);#j#<s)^#j#=s)e#j#>s)j#j#?s)m#j#@C#j#As)r#j#BC#j#CC#j#DC##"). Qed.

  Lemma ecloc_cells : forall m E e loc, 1 <= e < 2^31 ->
    rw_cells asegs m E [CB 16 (le8 (Z_to_bv 64 e) ++ le8 (Z_to_bv 64 AG_HTTP_CAT)); C8 (Z_to_bv 64 (loc + 1))] ->
    rw_cells asegs m E (ErrCodeCells (EC_http_loc e loc)).
  Proof.
    intros m E e loc He V.
    eapply rw_cells_reshape; [exact V| cbn; repeat split; reflexivity
      | unfold ErrCodeCells, EC_http_loc, ec_make_loc, wz; cbn [ec_val ec_cat ec_flags cells_bytes cbytes app];
        replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma cat_over_ec : forall m2 m4 (sp : word) E lo B shi,
    AHttpCat m2 true -> munch [(lo, bv_unsigned sp); (E, E + 24)]%Z m2 m4 -> wmono asegs m2 m4 ->
    ex_bnd B lo shi sp E -> AHttpCat m4 true.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AHttpCat); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8StateKit2.KIT.ex_bnd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AHttpCat_transport); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil); constr:(HCEIL); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AG_HTTP_CAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AG_HTTP_CAT_GUARD)|] [|@Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__p2; @__p3; @__p4; @__p5; @__p6; @__p7; @__p8; @__p9; @__arith; @__sat8; @__sat6; @__sat5; @__sat7; @BND; @WM; @MU; @HC; @shi; @B; @lo; @E; @sp; @m4; @m2|] "#))#3$##h#3#<#i#g#*#S#$#)#P###'#%#&#(#o#p#1#>#+#.#0#~$$#:#Y#,#8#7#G#Q#T#U#V#]#^#[#b#a#n#-#t#/#w#}$##;#=#A#?#H#I#J#X#W#Z#_#`#c#d#f#r#u#y#x#z#v#2#{#|#K#6#9#F#N#O#j#M#E#k#D#R#q#@#m#l#B#s#e#L#C#\7#k$#l$#m%#n%#o*#p%#q$#r)#s%#t%#u%#v&#w'#x*#y'#z*#{+#|'#}%#~%#S+##########US.#US/#US.(US/#USA#k##&#VSBKS%VSCEE5*Q1EEP#$S+######)#+N#1EEN#US0,.-$#..,#WSD#HKWSESFS&HYSGNQPHK59S&1EEK#+H-1EEH#.6#,.7&#$3##$#$###$#$#$#$###$###$###$#########)#$s#)######)#$S+####$###$#$###$#$#$###$#$#$#####$#########)#$6$#$#$#$#$#########################)#$>####$#######)#+>s#5%#K%s#U@($#%&H%s#Vs##($#&#L)s#x$s#y$#$#$#)#VS1(#,I)%I%VS2+&,I#k##%#k##'#%I/WS30+Jj##L#j#$%#%I*k##L#k#$(#)s$+VS17#%I$VS29%,I#k##%#k##5#WS3=)Jj##L#j#$2#%I)k##L#k#$5#VSHIs##VS4SI#m##>UJ#UN$US5S6US5#6E#6E%6ES6WS7E$#WS7E&#VSJ#SKUS0S,.S,$#USLS,VS8EOUSMEXS9E$O#XS9E#J$USNEUSOE*#GCCFNVS:Es$SVS:ES+/E$R#0'GCCF#S#*(GCCFQ*)GCCFK**GCCFH*+GCCFS&*,GCCFS-*-GCCFS;$s$'$#$#$#$#$#$#$#$#$#$#$###$#$#$#$#$#$#$#$###############################################)#-E#/E#Rs#:0s#=GCCF#S#*s#>GCCFS''s#?GCCF$#'s#@GCCFs#5#'s#AGCCFs#7#'s#BGCCFs#9#'s#CGCCFs#;#'s#DGCCFs#=#'s#EGCCFs#?#'s#FGCCFs#A#'s#GGCCFs#F#USPC-Es$G-Es$_WS<E$#/E#Rs#I0s#MGCCF#S#*s#NGCCFS=2s#OGCCF$#3s#PGCCF+*#VSQs#QFVS4S>S%VSRMOWSSS>#S%m$%#WSTEIJXSUMO$#l#%*)#l#&s#[s#Z#l#'s#as#`#j#(E#j#)E#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#j#0D#j#1D#j#2D#%JM%s#/J&#S-&S&#&H#&K#&Q#&N#&P#&+#&O#%s$SJ(#S'k##%#k#(E#k#)E#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#k#0D#k#1D#k#2D#5s%mSV%#s$~USWSX$s#k$#$#$#$#$#$#$#$###############################################)#%s#$#,IS$+S$s&),#s$w%$s#($s%v$#$#########################)#%s%GS$%Is#<,s#=s$}&$#+s#?s%&%#S'+S(S=%#s#B`Ms#B?><;*'%#s#AS(Hl#3s#^s#E#l#4s$ws%5#l#5s$ys%(#l#6s%%s$~#l#5s%.s%)#l#7s%4s%1#l#4s%?s%9#m##s%KVS8EJ*s$nGCCFP-Es%Z/E#Rs$m0s$qGCCF#S#'s$rGCCF#s$j's$sGCCFs$l#'s$tGCCFs$n#'s$uGCCFs$t#'s$vGCCF*#2s$wGCCFs$,s$n3s$xGCCF$s$2#l#%#s$*s$$l#&/s${#l#'s%'s%%#j#(E#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#%s%nM&#Q&N#&P#&O#&J#(s#vHk##$#k#(E#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#%s#Ks&4%s$[s#p&#s#O&s#O#&s#N#&s#N#%s#uS(\M)$s#<s#:#s#8S$Hl#3:+#l#4s%Ps%j#l#5s%Rs%]#l#6s%Zs%W#l#5s%cs%^#l#7s%is%f#l#4s%ts%n#m##s%}4s%~L#S?4s&&s%~s#9#+S)s&]%#K%s&}S)($#%&H%s&~S)($#&#L&'#m#,#WS@s'$S)s&gm#$#$s&w######$#######)#)s'O+s&A#%#K%s'7s&C($#%&H%s'8s&F($#&#L-Es&I-E,WS<E$#/E#Rs%f0s%jGCCF#S#2s%kGCCF#s${3s%lGCCFs%'s%&#l#%#s$zs$tl#&s%ps%o#l#'s%vs%u#j#(E#j#)E#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#j#0D#j#1D#j#2D#%?J(#S'k##s$k#k#(E#k#)E#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#k#0D#k#1D#k#2D#%s$hs&l`M#s$Es$Ds$Bs$As$0s$-s$+s$)s$gS(Hl#33%#l#4s&As&[#l#5s&Cs&N#l#6s&Ks&H#l#5s&Ts&O#l#7s&Zs&W#l#4s&es&_#m##s#32s&7GCCFs#+s&.3s&8GCCFs#|s%N#l#%#s%Fs%@l#&s$+s&;#l#'s&Cs&A#j#(E#j#*D#j#+D#j#,D#j#-D#j#.D#j#/D#(s#&Hk##s#v#k#(E#k#*D#k#+D#k#,D#k#-D#k#.D#k#/D#%s$as'/\M#s#ps$Ls$Js#os$HS$Hl#3.%#l#4s&`s&z#l#5s&bs&m#l#6s&js&g#l#5s&ss&n#l#7s&ys&v#l#4s'(s&~#m##s#O4s#PL#S?4s#Ts#Ps###+S*s#Y%#K%s(1S*($#%&H%s(2S*($#&#L&'#m#,#WS@s(4S*s#cm#$#]SYs(6S;S-S%POJs#o#j#8s(=#j#9s(?#j#:s(A#j#;s(P#j#<E#j#=E#j#>E#j#?E#j#@s(Z#j#As(W#j#BSZ##"). Qed.
End KIT.

Ltac bnd_lia BND := clear - BND; unfold ex_bnd in BND; lia.

Ltac assign_loc_core MEMCPY ASSIGNA SIDE MU WM FW HC1 TMP EC ST MI APE D8 BND D E e loc lo shi sp g j24 ej m :=
  steps_to 0xb8c60%Z;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let AS := fresh "AS" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SIDE MU WM FW) as SDc;
    pose proof ASSIGNA as AS;
    unfold aassignA_stmt, aassign_stmt, aassign_post, aassign_W, P_A_EC_CTOR_HTTP, AG_HTTP_CAT, AASSIGN_STACK, AINTRIN_STACK in AS;
    callZc (AS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D e lo shi g j24) (clear TMP ST AS);
    [ exact TMP | exact HC1 | exact (pside2_statics _ _ _ _ _ SDc) | rewrite ?unsigned_lit by (bnd_lia BND); exact ST
    | rewrite ?unsigned_lit by (bnd_lia BND); bnd_lia BND | bnd_lia BND | rewrite ?unsigned_lit by (bnd_lia BND); bnd_lia BND | bnd_lia BND
    | exact D8 | clear; lia
    | exact MI | exact (pside2_aconst _ _ _ _ _ SDc) | exact (pside2_stack0 _ _ _ _ _ SDc)
    | rewrite ?unsigned_lit by (bnd_lia BND); bnd_lia BND | ];
    clear SDc HC1 D8
  end;
  lazymatch goal with
  | TMP2 : rw_cells _ ?m2 D (ErrCodeCells _), HC2 : AHttpCat ?m2 true,
    AC2 : ACONST ?m2, SK2 : stack0 ?m2 lo shi, ST2 : stk _ ?m2 lo ?spc, MU' : munch _ m ?m2, WM' : wmono _ m ?m2 |- _ =>
    let SD2 := fresh "SD2" in let KF := fresh "KF" in
    let TMPa := fresh "TMPa" in let TMPb := fresh "TMPb" in let ECa := fresh "ECa" in let ECb := fresh "ECb" in
    let SRC := fresh "SRC" in let MU3 := fresh "MU3" in let WM3 := fresh "WM3" in
    pose proof (pside2_transport _ _ m2 _ _ _ _ SIDE ltac:(unfold AG_HTTP_CAT; exact MU') WM' FW) as SD2;
    (* [comment removed for export] *)
    unfold ErrCodeCells, EC_http, ec_make in TMP2; cbn [ec_val ec_cat ec_flags Z.eqb] in TMP2; unfold AG_HTTP_CAT, wz in TMP2;
    repeat (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ _ _) => step end);
    if_cases KF; zify_cond KF; [exfalso; clear - KF; lia|];
    (* [comment removed for export] *)
    zstep; change (Z.land 3 1) with 1; step; step; zstep;
    replace (Z.lor 1 loc) with (loc + 1) by (vm_compute; reflexivity);
    (* [comment removed for export] *)
    steps_to 0x716f4%Z;
    split_frameA TMP2 [C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 6667152)] [C8 (Z_to_bv 64 3)] TMPa TMPb;
    pose proof (rw_cells_bytes_at _ _ _ _ TMPa) as SRC; cbn [cells_bytes cbytes app] in SRC; rewrite app_nil_r in SRC;
    destruct (rw_cells_CB_split asegs _ E 24 16 ej EC ltac:(clear; lia)) as [ECa ECb]; clear EC;
    cbn [Nat.sub] in ECb; change (Z.of_nat 16) with 16 in ECb;
    pose proof (munch_refl [(lo, bv_unsigned sp); (E, E + 24)]%Z m2) as MU3; pose proof (wmono_refl asegs m2) as WM3;
    callZc (asan_memcpy_specZ MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ spc E D 16
              (le8 (Z_to_bv 64 e) ++ le8 (Z_to_bv 64 6667152)) (firstn 16 ej) lo)
           (clear ECa ST2 SRC);
    [ exact SRC | rewrite length_app, !length_le8; reflexivity | exact ECa
    | right; bnd_lia BND | clear; lia | bnd_lia BND | bnd_lia BND
    | eapply stack0_accessible; [exact SK2| bnd_lia BND| clear; lia| bnd_lia BND]
    | eapply accessible_sub; [exact (pside2_acc _ _ _ _ _ E 24 SD2 ltac:(ps_in))| clear; lia| clear; lia| clear; lia]
    | eapply stack0_shvis; [exact SK2| bnd_lia BND| clear; lia| bnd_lia BND]
    | eapply shvis_sub; [exact (pside2_shvis _ _ _ _ _ E 24 SD2 ltac:(ps_in))| bnd_lia BND| clear; lia| clear; lia| clear; lia| bnd_lia BND]
    | eapply stack0_in_app_mem; [exact SK2| bnd_lia BND| bnd_lia BND]
    | eapply aapp_in_app_mem; [exact APE| clear; lia| clear; lia]
    | eapply aconst_ok_aapp; [exact APE| clear; lia| clear; lia]
    | exact ST2 | bnd_lia BND | bnd_lia BND | bnd_lia BND
    | left; bnd_lia BND | right; clear; lia
    | assumption | exact AC2 | ];
    clear SK2 AC2 SD2
  end.

(* [comment removed for export] *)
Ltac assign_loc_chk SIDE FW EAL E m PRE :=
  lazymatch goal with
  | DST3 : rw_cells _ ?m3 E [CB _ _], MU'' : munch _ m ?m3, WM'' : wmono _ m ?m3 |- _ =>
    let SD3 := fresh "SD3" in let RD := fresh "RD" in
    pose proof (pside2_transport _ _ m3 _ _ _ _ SIDE ltac:(unfold AG_HTTP_CAT; exact MU'') WM'' FW) as SD3;
    pose proof (accessible_read0_sr m3 E 24 (E + 16) (pside2_acc _ _ _ _ _ E 24 SD3 ltac:(ps_in)) ltac:(clear; lia)
                  ltac:(clear - EAL; unfold hideL in EAL; Z.div_mod_to_equations; lia) ltac:(clear; lia)) as RD;
    clear SD3;
    PRE; clear RD; sh0_lit;
    shchk_br
  end.

Ltac assign_loc_block MEMCPY ASSIGNA SIDE MU WM FW HC1 TMP EC ST MI APE EAL D8 BND D E e loc lo shi sp g j24 ej m :=
  assign_loc_core MEMCPY ASSIGNA SIDE MU WM FW HC1 TMP EC ST MI APE D8 BND D E e loc lo shi sp g j24 ej m;
  assign_loc_chk SIDE FW EAL E m ltac:(step; zstep; zstep; step).

(* [comment removed for export] *)
Ltac assign_loc_close SIDE FW BND E e loc m :=
  lazymatch goal with
  | DST : rw_cells _ ?m4 E [CB _ _], ECb' : rw_cells _ ?m4 (E + 16) [C8 _], MU4 : munch _ m ?m4, WM4 : wmono _ m ?m4,
    HC2 : AHttpCat ?m2 true, MU3' : munch _ ?m2 ?m4, WM3' : wmono _ ?m2 ?m4 |- _ =>
    let SD4 := fresh "SD4" in let HC4 := fresh "HC4" in
    let AC4 := fresh "AC4" in let SK4 := fresh "SK4" in let XS4 := fresh "XS4" in
    pose proof (pside2_transport _ _ m4 _ _ _ _ SIDE ltac:(unfold AG_HTTP_CAT; exact MU4) WM4 FW) as SD4;
    pose proof (cat_over_ec _ _ _ _ _ _ _ HC2 MU3' WM3' BND) as HC4;
    pose proof (pside2_aconst _ _ _ _ _ SD4) as AC4; pose proof (pside2_stack0 _ _ _ _ _ SD4) as SK4;
    pose proof (pside2_statics2 _ _ _ _ _ SD4) as XS4;
    join_frameA DST ECb' E;
    apply (ecloc_cells _ _ e loc ltac:(clear; lia)) in DST
  end.
