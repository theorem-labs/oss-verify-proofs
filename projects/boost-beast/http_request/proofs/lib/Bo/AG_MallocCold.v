(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proof of malloc_arep_cold replaced by the text proof of openssl/echconfiglist_parser's Both/As/AG_MallocCold.v with this tree's addresses, over the guarded amaps_in_ledger and this tree's refill premises). *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit AllocBudget.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AllocRep AllocRepFacts AllocRepFacts2 AllocRepX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import CidBits CidBits2.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsDepotInv AsDepotHash AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_InitCache AW_Efs AW_Populate AW_Refill AW_MallocHead AW_MallocTail.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AG_WFHit AG_MallocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AG_RefillModel AG_ColdModel AG_Malloc AG_Malloc2 AG_WriteSet AS_Refill1 AS_Refill2 AS_Refill4 AG_Refill1 AG_Refill2 AG_Refill3 SecLazy AllocWalkKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma icW_avoids : forall CA a b, (b <= CA + 84 \/ CA + 2496 <= a) -> avoids (icW CA) a b.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Lists.ListDef.Forall_cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Lists.ListDef.Forall_nil); constr:(@Corelib.Lists.ListDef.Forall); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_InitCache.icW_from); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_DepotFrame.avoids); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_InitCache.icW)|] [|@iv; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @H; @b; @a; @CA|] "#2J#(#\#+#C#D#B#%#$#&#I#L###2#:#;#>#R#S#4#<#=#?#A#M#O#Q#U#T#V#W#P#'#X#\#Z#Y#^#]#.#-#J#,#G#F#5#6#E#8#7#N#@#3#[#9#0#1#/#K#H8#G%#H%#I&#J%#K'#L*#M&#N&#O*#P%#Q'#R&#S+#T)#U$#V&#W$#X$#Y$#Z%#[%3M4#3#4#3#3#5##G#$L#3+4#4#4#3#3#3#3#3#3#5##G#$#H&0#VS#CC)CCL$#I*CCL$G#&%#j#$(#3>3#3#5#5M,$##I#5>#$#3@3#5##(#-CC'##,,,.##I###,#$)-CC$##(2,4##I###2#$/-CC$##(8,:##I###8#$5-CC$##(>,@##I###>#$;-CC$##(s#$,s#&##I###s#$#$A-CC$##(s#*,s#,##I###s#*#$s#'-CC$##(s#0,s#2##I###s#0#$s#--CC$##(s#6,s#8##I###s#6#$s#3-CC$##(s#<,s#>##I###s#<#$s#9-CC$##(s#B,s#D##I###s#B#$s#?-CC$##(s#H,s#J##I###s#H#$s#E-CC$##(s#N,s#P##I###s#N#$s#K-CC$##(s#T,s#V##I###s#T#$s#Q-CC$##(s#Z,s#\##I###s#Z#$s#W-CC$##(s#`,s#b##I###s#`#$s#]-CC$##(s#f,s#h##I###s#f#$s#c-CC$##(s#l,s#n##I###s#l#$s#i-CC$##(s#r,s#t##I###s#r#$s#o-CC$##(s#x,s#z##I###s#x#$s#u-CC$##(s#~,s$$##I###s#~#$s#{-CC$##(s$(,s$*##I###s$(#$s$%-CC$##(s$.,s$0##I###s$.#$s$+-CC$##(s$4,s$6##I###s$4#$s$1-CC$##(s$:,s$<##I###s$:#$s$7-CC$##(s$@,s$B##I###s$@#$s$=-CC$##(s$F,s$H##I###s$F#$s$C-CC$##(s$L,s$N##I###s$L#$s$I-CC$##(s$R,s$T##I###s$R#$s$O-CC$##(s$X,s$Z##I###s$X#$s$U-CC$##(s$^,s$`##I###s$^#$s$[-CC$#UNs$o2s$p$#2s$q+#2s$r2#2s$s9#2s$t@#2s$us#'#2s$vs#.#2s$ws#5#2s$xs#<#2s$ys#C#2s$zs#J#2s${s#Q#2s$|s#X#2s$}s#_#2s$~s#f#2s%#s#m#2s%$s#t#2s%%s#{#2s%&s$&#2s%'s$-#2s%(s$4#2s%)s$;#2s%*s$B#2s%+s$I#2s%,s$P#2s%-s$W#2s%.s$^#2s%/s$e#2s%0s$l#2s%1s$s#UNOUS$OVPCGVPCIXS%C$H#US&CUS'C4M7C#7CM6Cs%M%C$#'C&J#()FDDE#K6Cs%D%C(#7Cs%Y'C$J#(.FDDE#K+/FDDE(#US(D6Cs%=6Cs%=.C$#%C1#6Cs%9%C$#'C#J-(8FDDE#K6Cs%A%C(#'C9J#(<FDDE#K+=FDDE'#/>FDDE10#VS)?EVS*QRVS+LGWS,Q#Rm$%#WS-CS.HXS/LG$#l#%*)#l#&s#)s#(#l#'s#.s#-#j#(C#j#)C#j#*C##Ls%s$G##Ls%h$#H&%##Hs%[##s%V$#G#%s%\$I#&%#k##)#k#(C#k#)C#k#*C#XLGIS0Hl#+3$#)CCs%_$#G*CCs%a$H#&%#m#(#%Cs#3s#3.Cs#5#%Cs#B#%C#s#3'C#Js#=(s#HFDDE#K%C&s#2'Cs#HJ#(s#KFDDE#K+s#LFDDE&#/s#MFDDEs#@s#?#l#%#s#1s#+l#&s#Qs#P#l#'s#Vs#U#j#(C#j#)C#j#*C##Hs%t##s%y$#G#%s&#$I#&%#k##s#,#k#(C#k#)C#k#*C#l#+-#s#%)CCs%{$#G*CCs%}$H#&%#m#(#%Cs#$s#U.Cs#W#%Cs#d#%C#s#U'C#Js#_(s#jFDDE#K%C&s#T'Cs#jJ#(s#mFDDE#K+s#nFDDE&#/s#oFDDEs#bs#a#l#%#s#Ss#Ml#&s#ss#r#l#'s#xs#w#j#(C#j#)C#j#*C##Hs&4##s&?$#G#%s&E$I#&%#k##s#N#k#(C#k#)C#k#*C#l#+-#s#G)CCs&;$#G*CCs&=$H#&%#m#(#%Cs#$s#w.Cs#y#%Cs$*#%C#s#w'C#Js$%(s$0FDDE#K%C&s#v'Cs$0J#(s$3FDDE#K+s$4FDDE&#/s$5FDDEs$(s$'#l#%#s#us#ol#&s$9s$8#l#'s$>s$=#j#(C#j#)C#j#*C##Hs&P##s&a$#G#%s&g$I#&%#k##s#p#k#(C#k#)C#k#*C#l#+-#s#i)CCs&W$#G*CCs&Y$H#&%#m#(#%Cs#$s$=.Cs$?#%Cs$L#%C#s$='C#Js$G(s$RFDDE#K%C&s$<'Cs$RJ#(s$UFDDE#K+s$VFDDE&#/s$WFDDEs$Js$I#l#%#s$;s$5l#&s$[s$Z#l#'s$`s$_#j#(C#j#)C#j#*C##Hs&l##s''$#G#%s'-$I#&%#k##s$6#k#(C#k#)C#k#*C#l#+-#s$/)CCs&s$#G*CCs&u$H#&%#m#(#%Cs#$s$_.Cs$a#%Cs$n#%C#s$_'C#Js$i(s$tFDDE#K%C&s$^'Cs$tJ#(s$wFDDE#K+s$xFDDE&#/s$yFDDEs$ls$k#l#%#s$]s$Wl#&s$}s$|#l#'s%&s%%#j#(C#j#)C#j#*C##Hs',##s'I$#G#%s'O$I#&%#k##s$X#k#(C#k#)C#k#*C#l#+-#s$Q)CCs'3$#G*CCs'5$H#&%#m#(#%Cs#$s%%.Cs%'#%Cs%4#%C#s%%'C#Js%/(s%:FDDE#K%C&s%$'Cs%:J#(s%=FDDE#K+s%>FDDE&#/s%?FDDEs%2s%1#l#%#s%#s$yl#&s%Cs%B#l#'s%Hs%G#j#(C#j#)C#j#*C##Hs'H##s'k$#G#%s'q$I#&%#k##s$z#k#(C#k#)C#k#*C#l#+-#s$s)CCs'O$#G*CCs'Q$H#&%#m#(#%Cs#$s%G.Cs%I#%Cs%V#%C#s%G'C#Js%Q(s%\FDDE#K%C&s%F'Cs%\J#(s%_FDDE#K+s%`FDDE&#/s%aFDDEs%Ts%S#l#%#s%Es%?l#&s%es%d#l#'s%js%i#j#(C#j#)C#j#*C##Hs'd##s(1$#G#%s(7$I#&%#k##s%@#k#(C#k#)C#k#*C#l#+-#s%9)CCs'k$#G*CCs'm$H#&%#m#(#%Cs#$s%i.Cs%k#%Cs%x#%C#s%i'C#Js%s(s%~FDDE#K%C&s%h'Cs%~J#(s&%FDDE#K+s&&FDDE&#/s&'FDDEs%vs%u#l#%#s%gs%al#&s&+s&*#l#'s&0s&/#j#(C#j#)C#j#*C##Hs($##s(S$#G#%s(Y$I#&%#k##s%b#k#(C#k#)C#k#*C#l#+-#s%[)CCs(+$#G*CCs(-$H#&%#m#(#%Cs#$s&/.Cs&1#%Cs&>#%C#s&/'C#Js&9(s&DFDDE#K%C&s&.'Cs&DJ#(s&GFDDE#K+s&HFDDE&#/s&IFDDEs&<s&;#l#%#s&-s&'l#&s&Ms&L#l#'s&Rs&Q#j#(C#j#)C#j#*C##Hs(@##s(u$#G#%s({$I#&%#k##s&(#k#(C#k#)C#k#*C#l#+-#s%})CCs(G$#G*CCs(I$H#&%#m#(#%Cs#$s&Q.Cs&S#%Cs&`#%C#s&Q'C#Js&[(s&fFDDE#K%C&s&P'Cs&fJ#(s&iFDDE#K+s&jFDDE&#/s&kFDDEs&^s&]#l#%#s&Os&Il#&s&os&n#l#'s&ts&s#j#(C#j#)C#j#*C##Hs(\##s);$#G#%s)A$I#&%#k##s&J#k#(C#k#)C#k#*C#l#+-#s&C)CCs(c$#G*CCs(e$H#&%#m#(#%Cs#$s&s.Cs&u#%Cs'&#%C#s&s'C#Js&}(s',FDDE#K%C&s&r'Cs',J#(s'/FDDE#K+s'0FDDE&#/s'1FDDEs'$s'##l#%#s&qs&kl#&s'5s'4#l#'s':s'9#j#(C#j#)C#j#*C##Hs(x##s)]$#G#%s)c$I#&%#k##s&l#k#(C#k#)C#k#*C#l#+-#s&e)CCs)#$#G*CCs)%$H#&%#m#(#%Cs#$s'9.Cs';#%Cs'H#%C#s'9'C#Js'C(s'NFDDE#K%C&s'8'Cs'NJ#(s'QFDDE#K+s'RFDDE&#/s'SFDDEs'Fs'E#l#%#s'7s'1l#&s'Ws'V#l#'s'\s'[#j#(C#j#)C#j#*C##Hs)8##s*#$#G#%s*)$I#&%#k##s'2#k#(C#k#)C#k#*C#l#+-#s'+)CCs)?$#G*CCs)A$H#&%#m#(#%Cs#$s'[.Cs']#%Cs'j#%C#s'['C#Js'e(s'pFDDE#K%C&s'Z'Cs'pJ#(s'sFDDE#K+s'tFDDE&#/s'uFDDEs'hs'g#l#%#s'Ys'Sl#&s'ys'x#l#'s'~s'}#j#(C#j#)C#j#*C##Hs)T##s*E$#G#%s*K$I#&%#k##s'T#k#(C#k#)C#k#*C#l#+-#s'M)CCs)[$#G*CCs)]$H#&%#m#(#%Cs#$s'}.Cs(##%Cs(0#%C#s'}'C#Js(+(s(6FDDE#K%C&s'|'Cs(6J#(s(9FDDE#K+s(:FDDE&#/s(;FDDEs(.s(-#l#%#s'{s'ul#&s(?s(>#l#'s(Ds(C#j#(C#j#)C#j#*C##Hs)p##s*g$#G#%s*m$I#&%#k##s'v#k#(C#k#)C#k#*C#l#+-#s'o)CCs)w$#G*CCs)y$H#&%#m#(#%Cs#$s(C.Cs(E#%Cs(R#%C#s(C'C#Js(M(s(XFDDE#K%C&s(B'Cs(XJ#(s([FDDE#K+s(\FDDE&#/s(]FDDEs(Ps(O#l#%#s(As(;l#&s(as(`#l#'s(fs(e#j#(C#j#)C#j#*C##Hs*0##s+-$#G#%s+3$I#&%#k##s(<#k#(C#k#)C#k#*C#l#+-#s(5)CCs*7$#G*CCs*9$H#&%#m#(#%Cs#$s(e.Cs(g#%Cs(t#%C#s(e'C#Js(o(s(zFDDE#K%C&s(d'Cs(zJ#(s(}FDDE#K+s(~FDDE&#/s)#FDDEs(rs(q#l#%#s(cs(]l#&s)'s)&#l#'s),s)+#j#(C#j#)C#j#*C##Hs*L##s+O$#G#%s+U$I#&%#k##s(^#k#(C#k#)C#k#*C#l#+-#s(W)CCs*S$#G*CCs*U$H#&%#m#(#%Cs#$s)+.Cs)-#%Cs):#%C#s)+'C#Js)5(s)@FDDE#K%C&s)*'Cs)@J#(s)CFDDE#K+s)DFDDE&#/s)EFDDEs)8s)7#l#%#s))s)#l#&s)Is)H#l#'s)Ns)M#j#(C#j#)C#j#*C##Hs*h##s+q$#G#%s+w$I#&%#k##s)$#k#(C#k#)C#k#*C#l#+-#s(y)CCs*o$#G*CCs*q$H#&%#m#(#%Cs#$s)M.Cs)O#%Cs)\#%C#s)M'C#Js)W(s)bFDDE#K%C&s)L'Cs)bJ#(s)eFDDE#K+s)fFDDE&#/s)gFDDEs)Zs)Y#l#%#s)Ks)El#&s)ks)j#l#'s)ps)o#j#(C#j#)C#j#*C##Hs+(##s,7$#G#%s,=$I#&%#k##s)F#k#(C#k#)C#k#*C#l#+-#s)?)CCs+/$#G*CCs+1$H#&%#m#(#%Cs#$s)o.Cs)q#%Cs)~#%C#s)o'C#Js)y(s*(FDDE#K%C&s)n'Cs*(J#(s*+FDDE#K+s*,FDDE&#/s*-FDDEs)|s){#l#%#s)ms)gl#&s*1s*0#l#'s*6s*5#j#(C#j#)C#j#*C##Hs+D##s,Y$#G#%s,_$I#&%#k##s)h#k#(C#k#)C#k#*C#l#+-#s)a)CCs+K$#G*CCs+M$H#&%#m#(#%Cs#$s*5.Cs*7#%Cs*D#%C#s*5'C#Js*?(s*JFDDE#K%C&s*4'Cs*JJ#(s*MFDDE#K+s*NFDDE&#/s*OFDDEs*Bs*A#l#%#s*3s*-l#&s*Ss*R#l#'s*Xs*W#j#(C#j#)C#j#*C##Hs+`##s,{$#G#%s-%$I#&%#k##s*.#k#(C#k#)C#k#*C#l#+-#s*')CCs+g$#G*CCs+i$H#&%#m#(#%Cs#$s*W.Cs*Y#%Cs*f#%C#s*W'C#Js*a(s*lFDDE#K%C&s*V'Cs*lJ#(s*oFDDE#K+s*pFDDE&#/s*qFDDEs*ds*c#l#%#s*Us*Ol#&s*us*t#l#'s*zs*y#j#(C#j#)C#j#*C##Hs+|##s-A$#G#%s-G$I#&%#k##s*P#k#(C#k#)C#k#*C#l#+-#s*I)CCs,'$#G*CCs,)$H#&%#m#(#%Cs#$s*y.Cs*{#%Cs+,#%C#s*y'C#Js+'(s+2FDDE#K%C&s*x'Cs+2J#(s+5FDDE#K+s+6FDDE&#/s+7FDDEs+*s+)#l#%#s*ws*ql#&s+;s+:#l#'s+@s+?#j#(C#j#)C#j#*C##Hs,<##s-c$#G#%s-i$I#&%#k##s*r#k#(C#k#)C#k#*C#l#+-#s*k)CCs,C$#G*CCs,E$H#&%#m#(#%Cs#$s+?.Cs+A#%Cs+N#%C#s+?'C#Js+I(s+TFDDE#K%C&s+>'Cs+TJ#(s+WFDDE#K+s+XFDDE&#/s+YFDDEs+Ls+K#l#%#s+=s+7l#&s+]s+\#l#'s+bs+a#j#(C#j#)C#j#*C##Hs,X##s.)$#G#%s./$I#&%#k##s+8#k#(C#k#)C#k#*C#l#+-#s+1)CCs,_$#G*CCs,a$H#&%#m#(#%Cs#$s+a.Cs+c#%Cs+p#%C#s+a'C#Js+k(s+vFDDE#K%C&s+`'Cs+vJ#(s+yFDDE#K+s+zFDDE&#/s+{FDDEs+ns+m#l#%#s+_s+Yl#&s,#s+~#l#'s,(s,'#j#(C#j#)C#j#*C##Hs,t##s.K$#G#%s.Q$I#&%#k##s+Z#k#(C#k#)C#k#*C#l#+-#s+S)CCs,{$#G*CCs,}$H#&%#m#(#%Cs#$s,'.Cs,)#%Cs,6#%C#s,''C#Js,1(s,<FDDE#K%C&s,&'Cs,<J#(s,?FDDE#K+s,@FDDE&#/s,AFDDEs,4s,3#l#%#s,%s+{l#&s,Es,D#l#'s,Js,I#j#(C#j#)C#j#*C##Hs-4##s.m$#G#%s.s$I#&%#k##s+|#k#(C#k#)C#k#*C#l#+-#s+u)CCs-;$#G*CCs-=$H#&%#m#(#%Cs#$s,I.Cs,K#%Cs,X#%C#s,I'C#Js,S(s,^FDDE#K%C&s,H'Cs,^J#(s,aFDDE#K+s,bFDDE&#/s,cFDDEs,Vs,U#l#%#s,Gs,Al#&s,gs,f#l#'s,ls,k#j#(C#j#)C#j#*C##Hs-P##s/3$#G#%s/9$I#&%#k##s,B#k#(C#k#)C#k#*C#l#+-#s,;)CCs-W$#G*CCs-Y$H#&%#m#(#%Cs#$s,k.Cs,m#%Cs,z#%C#s,k'C#Js,u(s-$FDDE#K%C&s,j'Cs-$J#(s-'FDDE#K+s-(FDDE&#/s-)FDDEs,xs,w#l#%#s,is,cl#&s--s-,#l#'s-2s-1#j#(C#j#)C#j#*C##Hs-l##s/U$#G#%s/[$I#&%#k##s,d#k#(C#k#)C#k#*C#l#+-#s,])CCs-s$#G*CCs-u$H#&%#m#(#%Cs#$s-1.Cs-3#%Cs-@#%C#s-1'C#Js-;(s-FFDDE#K%C&s-0'Cs-FJ#(s-IFDDE#K+s-JFDDE&#/s-KFDDEs->s-=#l#%#s-/s-)l#&s-Os-N#l#'s-Ts-S#j#(C#j#)C#j#*C##Hs.,##s/w$#G#%s/}$I#&%#k##s-*#k#(C#k#)C#k#*C#l#+-#s-#)CCs.3$#G*CCs.5$H#&%#m#(#%Cs#$s-S.Cs-U#%Cs-b#%C#s-S'C#Js-](s-hFDDE#K%C&s-R'Cs-hJ#(s-kFDDE#K+s-lFDDE&#/s-mFDDEs-`s-_#l#%#s-Qs-Kl#&s-qs-p#l#'s-vs-u#j#(C#j#)C#j#*C##Hs.H##s0=$#G#%s0C$I#&%#k##s-L#k#(C#k#)C#k#*C#l#+-#s-E)CCs.O$#G*CCs.Q$H#&%#m#(#%Cs#$s-u.Cs-w#%Cs.(#%C#s-u'C#Js.#(s..FDDE#K%C&s-t'Cs..J#(s.1FDDE#K+s.2FDDE&#/s.3FDDEs.&s.%#l#%#s-ss-ml#&s.7s.6#l#'s.<s.;#j#(C#j#)C#j#*C##Hs.d##s0_$#G#%s0e$I#&%#k##s-n#k#(C#k#)C#k#*C#l#+-#s-g)CCs.k$#G*CCs.m$H#&%#m#(#VS1s1%s0{0s1&s0|s.rs.q$#0s1's0}s.ys.qs#'#0s1(s0~s/$s.qs#J#0s1)s1#s/+s.qs#m#0s1*s1$s/2s.qs$4#0s1+s1%s/9s.qs$W#0s1,s1&s/@s.qs$z#0s1-s1's/Gs.qs%A#0s1.s1(s/Ns.qs%d#0s1/s1)s/Us.qs&+#0s10s1*s/\s.qs&N#0s11s1+s/cs.qs&q#0s12s1,s/js.qs'8#0s13s1-s/qs.qs'[#0s14s1.s/xs.qs'~#0s15s1/s0#s.qs(E#0s16s10s0*s.qs(h#0s17s11s01s.qs)/#0s18s12s08s.qs)R#0s19s13s0?s.qs)u#0s1:s14s0Fs.qs*<#0s1;s15s0Ms.qs*_#0s1<s16s0Ts.qs+&#0s1=s17s0[s.qs+I#0s1>s18s0bs.qs+l#0s1?s19s0is.qs,3#0s1@s1:s0ps.qs,V#0s1As1;s0ws.qs,y#0s1Bs1<s0~s.qs-@#0s1Cs1=s1)s.qs-c#0s1Ds1>s10s.qs.*#1S21#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#WS3Is1Y#WS4s1es1_#m#s#$#US5IWS6#GHm#%#j#,s1k#j#-C#j#.C#j#/C##"). Qed.
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_AllocBase.AENV Sort Prop.

(* [comment removed for export] *)
Lemma aenv_transport_pt : forall (Pr : Z -> Prop) tp TSD CTX TH sb SO T rest m m',
  AENV tp TSD CTX TH sb SO T rest m -> agree_on Pr m m' -> wmono bsegs m m' ->
  (forall a, AIMG_LO <= a < AIMG_TOP -> Pr a) -> (forall a, CTX <= a < CTX + 160 -> Pr a) -> (forall a, TH <= a < TH + 8 -> Pr a) ->   (* [comment removed for export] *)
  (forall a, SO <= a < SO + 16 + 8 * Z.of_nat (length T + length rest) -> Pr a) ->
  6354696 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP -> 6354608 <= TSD /\ TSD + 8 <= AIMG_TOP ->
  AENV tp TSD CTX TH sb SO T rest m'.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_AllocBase.AENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.agree_on); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_LO); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.AIMG_TOP); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Nat.add); constr:(@Corelib.Init.Datatypes.length); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@Corelib.Lists.ListDef.map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.AGOT_VALS); constr:(@Corelib.Lists.ListDef.repeat); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64arr); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AW_AllocBase.mkAENV); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.rw_cells_transport_pt); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocRep.u64arr_transport_pt); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.Lists.List.length_map); constr:(@Stdlib.Lists.List.length_app)|] [|@a; @v; @x; @y; @m; @n; @__ff; @__varmap; @__wit; @__x1; @__arith; @H0; @H; @__x2; @__x3; @__x4; @cstr0; @cstr; @Ha0; @Ha; @Etr; @Eso; @Einst2; @Einst1; @Ehooks; @Epart; @Efill; @Erms; @Ethresh; @Ehme; @Eshb; @Egot; @Ecan; @Eafl; @Einit; @Etid; @Ethr; @Egot2; @Elsan; @Ectx; @Etsd; @Etp; @Etsdi; @e_tr; @e_so; @e_inst2; @e_inst1; @e_hooks; @e_part; @e_fill; @e_rms; @e_thresh; @e_hme; @e_shb; @e_got; @e_can; @e_afl; @e_init; @e_tid; @e_thr; @e_got2; @e_lsan; @e_ctx; @e_tsd; @e_tp; @e_tsdi; @TSR; @TPR; @ZS; @ZT; @ZC; @ZI; @WM; @AG; @E; @m'; @rest; @T; @SO; @sb; @TH; @CTX; @TSD; @tp; @Pr|] "#AX#h$s#k$Q#$##$R$P$Y#{#y#u$*#d#h$W#[#W#Z#X$Z$##%#&$J#b#`#3#c#/#.#5#\#a#_#'#2#4#-#6$0#]#(#1#0#^#9$3$K#~#o#,#+#)#8#D#E#M#U#*#z#7#P#V$g#m#l$,$+$/#:$:#F$;#L#O#Q$G$H$_$`#f#e#g$m$n$j$r#q#s#t#x$-$4$7#;#<#=#>$8#?#@$9#A#B#C#G#H#I#J#K#N#R#S#T#Y$M$O$\$]$a$b$^$i$k$l$o$p$s$t$q$=$'#n#}#v$.#w$)$B$U$T#|$($V$[$S$5$F$N$D$@$?$>$c$%$C$A$I$&$E$e$$$6$f#r$1$L$X$h#p$2$<$dR$J$$K$#*%#+%$L%$M$$N%$O&$P%$Q'$R*$S$#6$$T'$U%#P$$V&$W*$X$$Y5$Z+$[/$\)$]'$^,$_$#4%$`%$a&$b&#R%$c/$d%$e$$f&$g%$h'$i%$j,$k$$l%$m%$n'$o$$p$$q&$r%k##CO#SC##########USR#USS#NCN$ISDSESLSFS;S4S(S'EWSjS/S'EWSkLS(S')SlF&FSM'$#US5Ek##$#k#$C#)S.F$6##########.#%S.#&F#',#US,Ek##$#k#$C#.A%S.#&F#'3#US6Ek##$#k#$C#)S/F.s#(%S/#>CS7>s#'SDF$#/#A0#%(#&F#',#US0Ek##$#k#$C#$SC##########$#$#$#$#$#######$#$#####$#######.#Cs#IS,$SC##########$#$#$#$###$#$#$#########$#######.##-$###$#$#########.##SC##$###$#$###$#############$###########.##4##########$###$#$#$###########.#$s######$#####$#####$#$#######.#$s#W##$#$#$#$#$###$#######$###########.##s#=$#$#$#####.##s#P$#$#$#$#$###$#$#####$#$###$#######.#$s#\$#$#$###$#$#$#######.#$s#C##########.#$s#B$#$#$#$#####$#$###$#$###########.##s#9####$#$#$#$###$###$#$#$#######.#$s$'##$#$###########$#######.##s$H$###$#$#$#$#$#$#$#####$#####.#$1################$#$###$#.##s#J$###############.##s#(####$###$#$#$#$#######.##s#1$#$#$#$#######.##s$;########################.##s$b####$#############################.##s$4$#####$#####$###$#$#######.#$s#Q##$#$#$#####.#$s$%##$#########.#$s$,$#$#######.##s$1######.#$s$h########.#$s$m######.##s$4$#$#$#######.#$s#1##$#######.##s#/########.#$s#F##########.#)s&Ps&g#s'T##########.#%s&o#)#SM',##s&|$#$#$#########.#)s&ZS,%S,s'L)#SM'%#IS0S6S,S5S<S=S.S/S7IS8S0S6S,S5S<S=S.S7j##$#$s'r##$#$###$#######$#$#$#$###########.#.SCUST#USU#(SV(#(#USRs(.USS#USTS9J$*%$#*&%#*'&#VSm*#2S9O#JM*M$#*M'#*M3#0LS7s&s#Cs(9S8$s(,######USn#%(#2S05#*M#00LS/&#0LS.S8$$s#6######.#%S8#0LS=#+Cs(LS?%#s(*0LS<#;#s#?########$#####$###############.#2s(=5#*M#s#00LS5s'1#2S?5#*M#s#40LS,SG#%SWs(M0LS6#s#6$s#X####$#$#####$###$#$#######.#*Ms#Us#G0LS0s'9#$s(J##$#$#$#$#$###$#$#$#$#$###########.#USUs#d*M#s#]*Ms#l#*M%#0LS8s'>##s#y$#$#$#####.#0LSNs'?s##$s)C$#$#$#$#$###############$#######.#2F5#j#%C#GCM#So0LSGs'C#$s$B####$###$#$#$#$#######.#$s)3$#$#$#$#$#$#$#$#$#$#$#$#$###############################.#2#5#*M#s$Q0LS?s'f#$s#r##########.#$>$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#.#2#5#5s$~*M#s$}*M$#*M&#0LSWs(1#$s$:$#$#$#$###$###$#####$###########.#$=$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#.#2#5#*M#s%K0LSps(G#$s%0##$#$#$#$###$###$#######.##s$P##$#############$#######$#####.#2s(V5#*M#s%n0LSqs(K##s&5$#$#######$#$###$#####$#####.#2s&[O#$s%|$#$###.#2#O#*M#s&-*Ms&/#*M,#0LSrs(X#$8####$#$###$#.#0LSss(Ss%P#s#l##$#############.#(s&O(#(#(#(#(#(#WStMs$-#0LSus(\##s#:####$#$#####$#$#$#######.#2SH5#*M#s&]0LSvs(a##s#G##$#$#$#######.#.s,D.s,.VSw$#2#5#USXs&A.s'K2#USX#*Ms&ts&q*Ms'$#*M%#*M)#*M+#0LSxs(p#%SIs,*2#5#>CSH/#2#5#*M#s&~*M(#0LSySI#%SYs,4GCs,WS@SIPs,X#SHXSZLSz%#0LSHs+:s'&Cs,\SJ%#s&}2S[5#*M#s'.0LSI&#0LSYSJ$%SJs&x0LS{#&Cs,eSO%#s,C0LS|#s'40LS}s+6s&d2SO5#*M#s'90LS~S\#%S]s,R0LT##s';0LS[s+.s&T0LSJs*xs&=0LT$s*rs&V0LS\s*`s%|0LSOs*Us%N0LS]s*Os$}0LT%s*>s$V0LT&s)|s$40LT's)ms#t0LSKs)`s&]0LSPs)Ws#Z2Q5#*M#s'J0LRs)N#0LS$s)Fs#5%S1s,\2#5#>CQ/#2#5#*M#s'T*M(#0LT(S1#%S:s,fGCs--S@S1Ps-.#QXSZLS#%#)s+lF/s#r%s+n#&F#'&#)s+qE&E&'$#%s+ts,z&E#''#j#&CFU#s,~%s+y#&E#+O,?O--m#$#@//#&EFD#j#'C#j#&C#+CE%EFXS^CCS_#+C#j#(C#j#)C#+Cs,-/F+C#j#&S)#+Cs-7BS)CCCS&S&99$s$7s-8#6CCCCCCJ:::J)s,3s,3(s#$9#8CCK;K0EE/s#$9#9BAB95#:A>#FJSANSAKCEUT)CUT*C1Cs,<LCSC,C$P#-&HDDG#I1Cs-F3C'#,C'S%#-*HDDG#I4+HDDG'#UT+D#s(m######.#1Cs*&,C#P1-4HDDG#I$s-=$#####$#############################.#1Cs**,Cs#(S%#-s#+HDDG#I4s#,HDDG:#7s#-HDDGs#$s###VT,s#.G+S`SaVT-FS'?S`#Sam$%#WT.CS9EXT/FS'$#l#**)#l#+s#8s#7#l#,s#;s#:#j#-C#&Fs#\'s#e#)s*OE&Es*='$#k##&#k#-C#VFS(El#.+$#l#/s#Gs#c#=E#j#0s#k#j#$C#<s(k/#%s-%#&F#'s#u#USbEk##$#k#$C#m#+#m##$;NQS#S$Rs--s(uS?#Cs.OS-%#s(p2S*5#*M#s(}Cs.TN%#s(u)#F%$s$'&F#'%#Cs.ZSc%#s({)#E%$s$-&E#'%#%'s.E&E#'(#%*s$(&E#D++C-6CCCCCCJs$-s$-s$-Js#x..#s$7s$,s#r8CCKs$.Ks$#EEs#~-'#9/-/'&#:-*#FHCs%SHCs)FHCSVEC$#EC&#Q#SQHCs)JHCs)MEC#(EC%#Q#SQ*SA#s#|*SA)#KCS'UT0CMC$E#LCs/%1Cs)@3C$#,C#Ps#~-s$%HDDG#I3C%s#},Cs$%S%#-s$(HDDG#I4s$)HDDG&#1Cs.&,C#P,-s$,HDDG#I1Cs*03C/#,C#Ps#d-s$0HDDG#I4s$1HDDG'#7s$2HDDG#s$(s#d7s$3HDDG,s$)#l#*#s#ds#^l#+7s$6#l#,;s$9#j#-C#j#1C#%Es)W)#F%$s.z&F#'%#)s.:S'%S's*B)#s+A'%#)s+VS'&S's+D'$#k##&#k##+#k#-C#k#1C#Cs/GSdXF#S(ESPl#.5%#l#/s#>s#F#=E#j#0s#Q#j#$C#2S-5#*M#s)z<#/#%s#\#&F#'s#]#k###s#kk#$C#m#-#m##$;NQS#S$Rs#hs#eSG#2S25#*M#s*+)S-F%S-s%/&F#'%#)NE%Ns%3&E#'%#%Ns/K&E#'(#%Ns%.&E#D++CN6CCCCCCJs%3s%3s%3Js$~NN#s%=s%2s$x8CCKs%4Ks%)EEs%(-'#9/-/'&#:-*#FMCs#VEs#WLCs/B,C#Ps$s-s$vHDDG#I3C%s$r,Cs$vS%#-s$yHDDG#I4s$zHDDG&#1Cs.m,C#P*-s$}HDDG#I,C)Ps$W-s%#HDDG#I4s%$HDDG%#7s%%HDDG#s$ws$W7s%&HDDG*s$x#l#*#s$Ws$Ql#+3s%)#l#,s#js%,#j#-C#j#1C#)EF%Es/l&F#'%#)s.~S'%S's/p)#s,3'%#k###s#Nk##(#k#-C#k#1C#XFSbS(ESKl#.0$#l#/s#&s#.#=E#j#0s#7#j#$C#<s$G/#%S-#&F#'s#@#k###s$Vk#$C#m#*#m##$;NQS#S$RS*s#FSN#%S2s*[2S+5#*M#s*s%S*s*_)#F%$s%x&F#'%#%S-s*d)#E%$s%}&E#'%#%'s09&E#'(#%*s%x&E#D++C-6CCCCCCJs%}s%}s%}Js%l..#s&+s%|s%f8CCKs%~Ks%sEEs%r-'#9/-/'&#:-*#F1Cs*t3Cs%`#,C#Ps$D-s%dHDDG#I3C%s%`,Cs$GS%#-s%gHDDG#I4s%hHDDG&#,Cs%gPs$J-s%jHDDG#I1Cs0U3Cs%j#,Cs$NS%#-s%nHDDG#I4s%oHDDG'#7s%pHDDG*s%f#l#*#s%Es%?l#+s$Ts%s#l#,s%ws%v#j#-C#j#1C#%Fs+-)#E%$s0[&E#'%#)ES'%Es0f&S'#'%#k##'#k#-C#k#1C#WFS(ScEl#.0$#l#/s#&s#.#VRE#j#0s#8#j#$C#<s$+/#%s#@#&F#'s#A#k###s%Dk#$C#m#*#m##$;NQS#S$Rs#Ks#HS8#%s%Cs0m%s%?s0n)#F/s'{%%#&F#'&#%s%?s0t)#E%$(&E#'%#.s1E%(#&E#')#Us&f&%,#&E#D-+C/+C+BS)CCCS&S&s&ls&ls&Ws(2,#6CCCCCCJs&ms&ms&mJs&\22%6)#8CCKs&nKs&cEEs&b1)#9313)(#:1-#F1Cs1,3Cs%3#,C#Ps&Q-s&THDDG#I1C53C&#,Cs&US%#-s&XHDDG#I4s&YHDDG'#7s&ZHDDG#s&Ps%*l#*#s&/s&)l#+s%>s&]#l#,s%Bs&`#j#-C#j#1C#%Es1;)#F%$B&F#'%#k###s$~k#-C#k#1C#l#.+#s$|l#/;s#&#=E#j#0s#1#j#$C#<s,8/#%s#:#&F#'s#;#k###s&)k#$C#m#*#m##$;NQS#S$Rs#Bs,AS0#)s0CF%s0Ds'F&F#'%#)s0GE&E&'$#%s0Js1a&E#''#%s0Ms'D&E#+O*?O++m#$#@--#+Cs0S6CCCCCCJs'Ls'Ls'LJs';s0Ts0T#s'Vs'Ks'58CCKs'MKs'BEEs'A3*#9101*&#:0-#F1Cs0X,C#Ps'/-s'2HDDG#I3C%s'.,Cs'2S%#-s'5HDDG#I4s'6HDDG&#7s'7HDDG#s'-s&il#*#s&hs&bl#+s';s':#l#,s'>s'=#j#-C#&F<'s#$#k###s&_k#-C#l#.'#s&^l#/4?#=E#j#0s#'#j#$C#<s,?/#%s0o#&F#'s#0#k###s&]k#$C#m#*#m##$;NQS#S$Rs0vs,HS6#)S2F%S2s'z&F#'%#)S*E%S*s'~&E#'%#%S*s2:&E#'(#%S*s'y&E#D++CS*6CCCCCCJs'~s'~s'~Js'mS*S*#s(,s'}s'g8CCKs(#Ks'tEEs's-'#9/-/'&#:-*#F3Cs'`s'],Cs&DS%#-s'dHDDG#I4s'eHDDGs$Y#7s'fHDDG#s'\#l#*#s';s'5l#+s&Js'i#l#,s'ms'l#j#-C#j#1C#)FE%Fs2P&E#'%#&S's%E's$T#k##%#k#-C#k#1C#WFS(NEl#.-$#l#/8@#VSPE#j#0s#)#j#$C#%S2s%>&F#'s#0#k###s'5k#$C#m#(#m##$;NQS#S$RS+s&%S,#%S2s2f)s#/F%s#0s$N&F#'%#%S-s2k)#E%$s$S&E#'%#%'s$M&E#'(#%*s$L&E#D++C-6CCCCCCJs(Xs(Xs(XJs(G..#s$]s$Ps$J8CCKs(YKs(NEEs(M-'#9/-/'&#:-*#F,Cs#8Ps&y-s(=HDDG#I3Cs#:s$G,Cs&|S%#-s(@HDDG#I4s(AHDDG&#7s(BHDDG#s(8s%1l#*#s'ss'ml#+s'&s(E#l#,s(Is(H#j#-C#j#1C#)s#9E%s#:s$e&E#'%#k###s%,k#-C#k#1C#l#.*#s%+l#/7?#VRE#j#0s#)#j#$C#%s#[s$D&F#'s#0#k###s'jk#$C#m#(#m##$;NQS#S$Rs#6s.&S5#)s1uF/s.6%s1w#&F#'&#)s1zE&E&'$#%s1}s.@&E#''#Us)+s.C%s2%#&E#+O+?O,,m#$#@..#+Cs2++Cs.KBS)CCCS&S&s)4s)4s({s.Is.L#6CCCCCCJs)5s)5s)5Js)$s2.s2.%6,#8CCKs)6Ks)+EEs)*6,#9434,(#:30#F1Cs22,C#Ps(t-s(wHDDG#I1Cs.T3C&#,Cs(xS%#-s({HDDG#I4s(|HDDG'#7s(}HDDG#s(ss(Sl#*#s(Rs(Ll#+s)%s)$#l#,s)(s)'#j#-C#&F@'s#)#k###s(Ik#-C#l#.'#s(Hl#/5s###=E#j#0s#+#j#$C#<s-n/#%s2J#&F#'s#5#k###s(Gk#$C#m#*#m##$;NQS#S$Rs2Qs-wS<#)s2?F/s.m%s2A#&F#'&#)s2DE&E&'$#.s3k%s2H#&E#'(#Us)e&%s2L#&E#+O,?O--m#$#@//#+Cs2R+C.BS)CCCS&S&s)ns)ns)Ys/%/#6CCCCCCJs)os)os)oJs)^s2Us2U%7,#8CCKs)pKs)eEEs)d7,#9545,(#:40#F1Cs2Y,C#Ps)R-s)UHDDG#I1C73C&#,Cs)VS%#-s)YHDDG#I4s)ZHDDG'#7s)[HDDG#s)Qs)1l#*#s)0s)*l#+s)_s)^#l#,s)bs)a#j#-C#&F@'s#*#k###s)'k#-C#l#.'#s)&l#/5s###=E#j#0s#,#j#$C#<s.4/#%s2q#&F#'s#6#k###s)%k#$C#m#*#m##$;NQS#S$Rs2xs.=S=#)s2rF%s2ss#u&F#'%#)s2vE&E&'$#%s2ys/V&E#''#%s2|s#t&E#+O*?O++m#$#@--#+Cs3&6CCCCCCJs*Hs*Hs*HJs*7s3's3'#s$)s#{s#r8CCKs*IKs*>EEs*=3*#9101*&#:0-#F1Cs3+,C#Ps*+-s*.HDDG#I3C%s#q,Cs*.S%#-s*1HDDG#I4s*2HDDG&#7s*3HDDG#s*)s)el#*#s)ds)^l#+s*7s*6#l#,s*:s*9#j#-C#&F<'s#$#k###s)[k#-C#l#.'#s)Zl#/4?#=E#j#0s#'#j#$C#%s3@s#o&F#'s#.#k###s)Wk#$C#m#(#m##$;NQS#S$Rs3Gs/+S.#)s35F(s,*(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#/#%s4I#&F#'s#t#)s4LE&E&'$##s/[####.#%s4S#&E#'+#Us,.&%s4W#&E#+O/?O00m#$#@22#+Cs4]+C.BS)CCCS&S&s,7s,7s+~:/#6CCCCCCJs,8s,8s,8Js,'s4`s4`%:,#8CCKs,9Ks,.EEs,-:,#9878,(#:70#F1Cs4d,C#Ps+w-s+zHDDG#I1C73C&#,Cs+{S%#-s+~HDDG#I4s,#HDDG'#7s,$HDDG#s+vs+Vl#*#s+Us+Ol#+s,(s,'#l#,s,+s,*#j#-C#&F@'s$?#k###s+Lk#-C#l#.'#s+Kl#/5s###=E#j#0s#/#j#$C##s/5$###$#########$###########.#$s.u$###########.#$s.9##$###$#######.#$s-y$#$#$#######.#$s00######.#$s06########.##s/:######.##s#+$#$#######.#$s#1########.##s#/$#$#$#####.##s#G$#$#######.#JC*Cs3x#*Cs3q#*Cs2d#*Cs3k#*Cs3e#*Cs3a#*Cs54#*Cs5f#*Cs3^#*Cs3Z#*Cs5p#*Cs3T#*Cs3N#*Cs3I#*Cs3C#GCMs1B#<#/#%s6(#&F#'s%S#k###s,Rk#$C#m#s#n#<s1J/#%s60#&F#'s%[#k###s,Zk#$C#m#*#;NQS#S$Rs66s1RS/#)s6+F%s6,s-v&F#'%#)s6/E&E&'$#%s62s85&E#''#%s65s-t&E#+O*?O++m#$#@--#+Cs6;6CCCCCCJs-|s-|s-|Js-ks6<s6<#s.*s-{s-e8CCKs-}Ks-rEEs-q3*#9101*&#:0-#F1Cs6@,C#Ps-_-s-bHDDG#I3C%s-^,Cs-bS%#-s-eHDDG#I4s-fHDDG&#7s-gHDDG#s-]s-=l#*#s-<s-6l#+s-ks-j#l#,s-ns-m#j#-C#&F<'s#$#k###s-3k#-C#l#.'#s-2l#/4?#=E#j#0s#'#j#$C#<s1N/#%s6W#&F#'s#0#k###s-1k#$C#m#*#m##$;NQS#S$Rs6^s1WS7#)s6XF/s&+%s6Z#&F#'&#)s6]E&E&'$#.s8R%s6a#&E#'(#Us.O&%s6e#&E#+O,?O--m#$#@//#+Cs6k+C.BS)CCCS&S&s.Xs.Xs.Cs&?/#6CCCCCCJs.Ys.Ys.YJs.Hs6ns6n%7,#8CCKs.ZKs.OEEs.N7,#9545,(#:40#F1Cs6r,C#Ps.<-s.?HDDG#I1C73C&#,Cs.@S%#-s.CHDDG#I4s.DHDDG'#7s.EHDDG#s.;s-wl#*#s-vs-pl#+s.Is.H#l#,s.Ls.K#j#-C#&F@'s#*#k###s-mk#-C#l#.'#s-ll#/5s###=E#j#0s#,#j#$C#<s1Z/#%s7.#&F#'s#6#k###s-kk#$C#m#*#m##$;NQS#S$Rs75s1cSD#)s7$F%s7%s/,&F#'%#)s7(E&E&'$#%s7+s9G&E#''#%s7.s/*&E#+O*?O++m#$#@--#+Cs746CCCCCCJs/2s/2s/2Js.}s75s75#s/<s/1s.w8CCKs/3Ks/(EEs/'3*#9101*&#:0-#F1Cs79,C#Ps.q-s.tHDDG#I3C%s.p,Cs.tS%#-s.wHDDG#I4s.xHDDG&#7s.yHDDG#s.os.Ol#*#s.Ns.Hl#+s.}s.|#l#,s/$s/##j#-C#&F<'s#$#k###s.Ek#-C#l#.'#s.Dl#/4?#=E#j#0s#'#j#$C#<s1f/#%s7P#&F#'s#0#k###s.Ck#$C#m#*#m##$;NQS#S$Rs7Ws1oSE#)s79F%s7:s/`&F#'%#)s7=E&E&'$#%s7@s9{&E#''#%s7Cs/^&E#+O*?O++m#$#@--#+Cs7I6CCCCCCJs/fs/fs/fJs/Us7Js7J#s/ps/es/O8CCKs/gKs/\EEs/[3*#9101*&#:0-#F1Cs7N,C#Ps/I-s/LHDDG#I3C%s/H,Cs/LS%#-s/OHDDG#I4s/PHDDG&#7s/QHDDG#s/Gs/'l#*#s/&s.|l#+s/Us/T#l#,s/Xs/W#j#-C#&F<'s#$#k###s.yk#-C#l#.'#s.xl#/4?#=E#j#0s#'#j#$C#<s1w/#%s7e#&F#'s#0#k###s.wk#$C#m#*#m##$;NQS#S$Rs7ls2$SL#)s7]F/s'}%s7_#&F#'&#)s7bE&E&'$#.s:=%s7f#&E#'(#Us09&%s7j#&E#+O,?O--m#$#@//#+Cs7p+C.BS)CCCS&S&s0Bs0Bs0-s(5/#6CCCCCCJs0Cs0Cs0CJs02s7ss7s%7,#8CCKs0DKs09EEs087,#9545,(#:40#F1Cs7w,C#Ps0&-s0)HDDG#I1C73C&#,Cs0*S%#-s0-HDDG#I4s0.HDDG'#7s0/HDDG#s0%s/al#*#s/`s/Zl#+s03s02#l#,s06s05#j#-C#&F@'s#*#k###s/Wk#-C#l#.'#s/Vl#/5s###=E#j#0s#,#j#$C#<s28/#%s83#&F#'s#6#k###s/Uk#$C#m#*#m##$;NQS#S$Rs8:s2ASF#)s8-F%s8.s*I&F#'%#)s81E&E&'$#%s84s6*&E#''#%s87s*H&E#+O*?O++m#$#@--#+Cs8=6CCCCCCJs0xs0xs0xJs0gs8>s8>#s*Ys*Os*F8CCKs0yKs0nEEs0m3*#9101*&#:0-#F1Cs8B,C#Ps0[-s0^HDDG#I3C%s*E,Cs0^S%#-s0aHDDG#I4s0bHDDG&#7s0cHDDG#s0Ys09l#*#s08s02l#+s0gs0f#l#,s0js0i#j#-C#&F<'s#$#k###s0/k#-C#l#.'#s0.l#/4?#=E#j#0s#'#j#$C#%s8Ws*C&F#'s#.#k###s0+k#$C#m#(#m##$;NQS#S$Rs8^s5[S;#)s8UF/s(I%s8W#&F#'&#)s8ZE&E&'$#.s;m%s8^#&E#'(#Us1I&%s8b#&E#+O,?O--m#$#@//#+Cs8h+C.BS)CCCS&S&s1Rs1Rs1=s(]/#6CCCCCCJs1Ss1Ss1SJs1Bs8ks8k%7,#8CCKs1TKs1IEEs1H7,#9545,(#:40#F1Cs8o,C#Ps16-s19HDDG#I1C73C&#,Cs1:S%#-s1=HDDG#I4s1>HDDG'#7s1?HDDG#s15s0ql#*#s0ps0jl#+s1Cs1B#l#,s1Fs1E#j#-C#&F@'s#*#k###s0gk#-C#l#.'#s0fl#/5s###=E#j#0s#,#j#$C#<s3,/#%s9+#&F#'s#6#k###s0ek#$C#m#*#m##$;NQS#S$Rs92s35S4#2S35#*M#s7%)s9)F%s9*s2)&F#'%#)s9-E&E&'$#%s90s<D&E#''#%s93s2'&E#+O*?O++m#$#@--#+Cs996CCCCCCJs2/s2/s2/Js1zs9:s9:#s29s2.s1t8CCKs20Ks2%EEs2$3*#9101*&#:0-#F1Cs9>,C#Ps1n-s1qHDDG#I3C%s1m,Cs1qS%#-s1tHDDG#I4s1uHDDG&#7s1vHDDG#s1ls1Ll#*#s1Ks1El#+s1zs1y#l#,s1}s1|#j#-C#&F<'s#$#k###s1Bk#-C#l#.'#s1Al#/4?#=E#j#0s#'#j#$C#<s/;/#%s9U#&F#'s#0#k###s1@k#$C#m#*#m##$;NQS#S$Rs9\s#6S(#)s9TF/s*B%s9V#&F#'&#)s9YE&E&'$#%s9\s<q&E#''#Us2]s<t%s9`#&E#+O+?O,,m#$#@..#+Cs9f+Cs<|BS)CCCS&S&s2fs2fs2Qs*Us<}#6CCCCCCJs2gs2gs2gJs2Vs9is9i%6,#8CCKs2hKs2]EEs2\6,#9434,(#:30#F1Cs9m,C#Ps2J-s2MHDDG#I3C%s.[,Cs2MS%#-s2PHDDG#I4s2QHDDG&#7s2RHDDG#s2Hs2(l#*#s2's1}l#+s2Vs2U#l#,s2Ys2X#j#-C#&F?'s#(#k###s1zk#-C#l#.'#s1yl#/4B#=E#j#0s#*#j#$C#<s3q/#%s:(#&F#'s#4#k###s1xk#$C#m#*#m##$;NQS#S$Rs:/s3zS'#%S>s=E2#5#>CS:/#2#5#*M#s8=*M(#)S3F%S3s#C&F#'%#)S+E%S+s=S>CS3>s=wS>F$#/#As=`#%(#&E#'+#/*/*%$#As=g#%/#&E#'2#D3+C3AEFXS^CCS_#+C#j#(C#j#)C#+C0+C06S)S)S)CCCT1S&S&S&JT2:2$91#BS)CCCS&S&s3Vs3Vs3A91#6CCCCCCSBs3Ws3Ws3WSB's=vs=vs3A92#6CCCCCCJs3Xs3Xs3XJs3G>>-92#8CCKs3YKs3NEEs3M92#9A9A20#%S+s#f&E#'s#$#&Es#$'s#&#%S+s#a&E#+CS+6CCCCCCJs3cs3cs3cJs3RS+S+#s#ns#ds#[8CCKs3dKs3YEEs3X+&#9s#,+s#,&;#:+)#F>CS+USe#/$)S9#>s>HS+USe#/$)S9#VT3Cs>2WSfC#s2AWSfC$s2<EC#s2;EC%#Q#SQ*SA#s3YKCS4MC#S's2:KCS(MC$E#1CS9LCs>^,C$P#-s3]HDDG#I,C&Ps1H-s3_HDDG#I3Cs3^s/m,Cs2BS%#-s3bHDDG#I4s3cHDDGs0W#3Cs1N+WT4Cs3`#3C(#,Cs2HS%#-s3hHDDG#I4s3iHDDGs0]#7s3jHDDG)s3`#7s3kHDDG.s3a#7s3lHDDG1s3b#l#*#s3As3;l#+7s3o#l#,<s3r#j#-C#j#1C#j#2C#j#3C#)S9S()S'S(%S's>Q&S(#'%#)S(S4%S(s>U%S;SFAs>_#%%#&S4#'(#k##*#k##/#k##0#k#-C#k#1C#k#2C#k#3C#>s?(S*/#>CS-/#[F%#S;NES'S(l#.;(#l#4s#Cs#A#l#5s#Hs#F#l#/s#Ks#R#XSgs#ns#gs#X#VSKE#j#0s#z#j#$C#%S3s>o2#5#>CS>/#2#5#*M#s9g*M(#<#/#%S3#&F#'s$0#k###s3Yk#$C#m#3#m##$;NQS#S$RS>s$6E#GCs?HS@S:Ps?I#S1>s?J$>s?KS1F$#)s$6F/EAs?5#%s$9#&F#''#USdEk##$#k#$C#j#)S)#FEs$>/#As??#%s$C#&F#'1#k###,k#$C#j#)S)#)s#-F>s?aS:Fs#,#/#As?J#%s#2#&F#')#)s$QE'#s$K'$s$EUs52s$IAs?R#%s$V#&E#D)6CCCCCCSBs57s57s57SBs$Cs?Vs?Vs4}s$U's$?6CCCCCCJs58s58s58Js5's$Zs$Zs$Is$U'#8CCKs59Ks5.EEs5-s$U'#9-s$U-'&#:-,#F,Cs#vPs3Y-s4yHDDG#I4s4zHDDG#s#p7s4{HDDG#s4qs#pl#*#s4Ps4Jl#+s$&s4~#l#,s5&s5%#j#-C#j#1C#j#2C#j#3C#%Fs?^)#E%S'S(As?i#%&#&E#''#%S(S4As?n#%s1.#&S'#'s1q#k##(#k#-C#k#1C#k#2C#k#3C#YFs#js#hS;NS(l#.5$#l#4s$Ls$J#l#5s$Qs$O#l#6s##s#-#XSgs$ws$ps$a#VSKE#j#7s#3#j#$C#XT5Cs@>S@S:ZShS)s%3s#>$s#S#>s@@s#UWT6s@As#WS1ZShS)s#Ts#J%$#]T7NQS#S$Rs%:s#XF#i#CT8S-S*S2S+S3S>S:S1S#s4Us3Is2^s1ps1/s0Ws0#s/Js.ms.3s-]s*[s*'s)Is(qs(=s'_s'-s&Os%ts%<s#[#IS-S*S2S+S3S>S:S1S#m#$#j#8s5v#j#9s5{#j#:s6*#j#;s6,#j#<s61#j#=s63#j#>s65#j#?s67#j#@s69#j#As6;#j#Bs6=#j#Cs6?#j#Ds6A#j#Es6C#j#Fs6E#j#Gs6G#j#Hs6J#j#Is6O#j#Js6Q#j#Ks6U#j#Ls6X#j#Ms6Z#j#Ns6a#i#:#S?SGSNS8S0S6S,S5S<S=S.S/S7SDSESLSFS;S4S(S'EFj#Os6d#j#Ps6i#j#Qs6t#j#Rs71#j#Ss7D#j#Ts7X#j#Us7b#j#Vs8$#j#Ws8H#j#Xs8q#j#Ys9D#j#Zs9t#j#[s:0#j#\s:9#j#]s:R#j#^s:d#j#_s:g#j#`s:l#j#as;&#j#bs;*#j#cs;2#j#ds;4#j#es;@#`T9S0S6S,S5S<S=S.S/S7s;i#SEj#fs;m#j#gs;{#j#hs@K#j#is@Z#j#js@b#j#ks@q#j#ls@x#j#ms@z#j#ns@|#j#oSi#j#(Si#j#psA$#j#qsA&#j#rC#j#sC#j#tC#j#uC#j#vC#j#wsA-#j#xsA6##"). Qed.

(* [comment removed for export] *)
Lemma poisoned_visible : forall m m' A k v x,
  poisoned m A k v -> wmono bsegs m m' -> sh A <= bv_unsigned x < sh A + Z.of_nat k -> wview bsegs m' x <> None.
Proof.
  intros m m' A k v x (HA & HM & [HB HW]) WM Hx. apply WM. destruct HW as (W1 & W2 & W3).
  unfold poison_bytes in W3. rewrite repeat_length in W3.
  specialize (W3 (bv_unsigned x - sh A) ltac:(hci; lia)). replace (sh A + (bv_unsigned x - sh A)) with (bv_unsigned x) in W3 by lia.
  unfold wa in W3. rewrite Z_to_bv_bv_unsigned in W3. exact W3.
Qed.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma in_window1 : forall x lo n, 0 <= lo -> 0 <= n -> lo + n < 2^64 ->
  in_rangesb x [(wz lo, wz n)] = true -> lo <= bv_unsigned x < lo + n.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.orb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.zin_rangeb); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb_cons); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.Bool.Bool.orb_false_r); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.unsigned_lit); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.andb_prop); constr:(@kc__2); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@Corelib.Numbers.BinNums.xI)|] [|@b; @z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @__sat1; @__sat2; @m; @n; @__x3; @__sat3; @__sat4; @R2; @H; @R1; @R; @Hh; @Hn; @H0; @lo; @x|] "#&L#:$'#A#o#I###P#$#%#p#n#&#*#C#)#,#x#-#+#`#u#.#@#(#z#/#G#'#O#S#R#X#^#e#a#f#i#h#w#{#\#0#3#2#>#=#F#L#U#V#W#]#_#g#j#k#m#v#y#|#~$#$$#}$&#1$($)#5#4$*#9#7#8#H#E#T#B#D#[#Z#l#r#q$%#?#N#K#Q#Y#c#b#M#J#d#t#s$'<#k&#l%#m%#n%#o%#p%#q%#r+#s'#t*#u%#v$#w$#x&#y)#z%#{%#|&#}'#~%$#$$$%$%&#&($&(.S'.#.#.#.#.#US=#US>#&NH$LIUS+,US+(VS?$#'&#VS@))/S,/L5,,$#US-&0'$#6S(##E#G/S(522#*0,#(6O##EFGj#$E#%8OVS.#(6O.VS/$#WSAO+01E*(F$##E%G%?M/O5@@#1VS.%#VS/#SBUSC$1E$0F%##E&GVS0s#'M%s#(#%s#)P)F#$F%(%#2%##E#Gj#%C#VSDs#,s#+'Ns#-&Ns#-'Ns#-k##$#k##&#&Ns#2WSEs#3s#2Hj##S1#j#&%#&Ns#4k##S1#k#&(#7S27#7#3C#3C%3CS24C$#4C&#VS3#S4US-S$0S$$#USFS$VS5CIUSGCXS6C$H#USHCUSIC8CS'8Cs#U9C$#VS7Cs#MWSJC#s#R+C%S%#,)KDDJ#QUSKDVS7CN+C#S)*,-KDDJ#Q+C%S)-,/KDDJ#Q+C/S%+,1KDDJ#Q[S82KDDJ%#*3KDDJ&+#*4KDDJ),#*5KDDJ.-#VSL6JVSMEGVSNFI#E#Gm$%#WSOCNHXSPFI$#l#'*)#l#(@?#l#)s#%s#$#j#*C#j#+C#$FH'#s#h&NI&NL'Ls#k-$#k##&#k##'#k##)#k#*C#k#+C#:PROMS#l#,/$#l#-s#Cs#@#l#.s#Ms#H#VS9M#1Cs#Ws#PFM#%s#~S#)M#VS0s$$O%s$%#$M#('#2'##E#G%s$*R)P#$PF(%#2%##E#Gj#%C#3Cs#R4C#s#N4Cs#Q#VS3#S40S$#s#M9Cs#Es#F+C#S%s#C,s#IKDDJ#Q*s#JKDDJs#?s#Bs#:*s#KKDDJs#>s#C#*s#LKDDJ%s#D#l#'#s#9s#3l#(s#Ps#O#l#)+s#T#j#*C#j#+C#$HF'#s$<k##s#1s#/k##s$B#k##%#k#*C#k#+C#:S&RMS#Pl#,+$#l#-s#os#l#l#.s#ys#t#VS9M#1Cs$'?FM#)S#s$'$S#M(s$)#2%##E#G$PS#(s#,#WSQs#,#F#Es#-G#E%G-$#%s$YS&)R##E#G$RP(&##E#G-&#%s$`S*&S&#$S&R'%#-%#j##(#((&#E#G%s$hS:)S*##E#G%s$kSR$S:S*($##E#G)HF#E#G&IHk##$#&HF)IH#E#Gk##%#-'#&LIk##&#j##%#)LI#E#Gk##.#j###Hj##/#VSSHF;1-)$#j#/C#j#0C#k#/C4k#0C#%s%*S;WFS<#I&S<$(HF#E#G'IHk##$#'HF(IH#E#Gk##%#-'#'LIk##&#j##%#(LI#E#Gk##.#j###Hj##/#VSTHF;1-)$#j#/C#j#0C#k#/C4k#0C#%s%DSU$SVS;WF$#L'%$VS5CLXS6Cs$^H#USWS'8C#9Cs$\#+Cs$\S%#,s$_KDDJ#Q+Cs$_S)s$^,s$aKDDJ#Q[S8s$bKDDJ#%*s$cKDDJ$s$[#*s$dKDDJ's$\#l#'#s$Qs$Kl#(.s$g#l#)s$ns$l#j#*C#j#+C#j#1C#$FI'H#&HI&IL$IS,'L#-%#k##'#k##)#k#*C#k#+C#k#1C#%s%fSX:SY#SZLS(l#,1%#l#2s%2s%/#l#3s%<s%7#l#4s#'s#&#l#5s#-s#+#l#6s#Ds#C#l#5s#Is#G#j#4s#_#j#6s#d#V#HFj##s#i#j##s#v#;s#ws#ts#m#Fl#7s#~s#{#l#7s$+s$&#l#7s$Xs$P#l#7s%Us%T#l#7s%^s%]#j#7s%k#j#8s%t#j#9s%z#j#:s%{#j#0C#j#;C#j#<s&###"). Qed.

Lemma in_rangesb_if : forall x (b : bool) l, in_rangesb x (if b then l else []) = true -> in_rangesb x l = true.
Proof. intros x [|] l H; [exact H| discriminate H]. Qed.

Lemma land_lnot7' : forall x, Z.land x (Z.lnot 7) = x - x mod 8.
Proof.
  intros x. rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma amodelx_hit : forall s mo c cnt rest ch,
  AMODELX s mo ->
  AMODELX (mkAst (hit_state (a_st s) c cnt rest ch) (a_thr s) (a_ctx s) (a_fsb s) (a_L s) (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s)) mo.
Proof. intros s mo c cnt rest ch A. exact A. Qed.

End HCW.


(* [comment removed for export] *)
Ltac trp lem AG WM H Z B :=
  eapply (lem _ _ _ AG WM); [exact H|];
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
  let Ha := fresh in intros ? Ha; apply Z; clear - Ha B; try acb; lia.

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Section MallocColdGlue.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo size : Z) (CH : list (Z * Z)).

  (* [comment removed for export] *)
  Let st := a_st s.
  Let TH := a_thr s.
  Let sb := a_sb s.
  Let CTX := a_ctx s.
  Let rz := rz_size size.
  Let needed := round_up (Z.max size 8) 8 + rz.
  Let c := class_id needed.
  Let csz := class_size c.
  Let csz8 := csz / 8.
  Let CA := TH + 208.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  (* [comment removed for export] *)
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  (* [comment removed for export] *)
  Let st2 := refilled st c.
  Let chunks2 := firstn (Z.to_nat n) fl1.
  Let cp := hd 0 chunks2.
  Let AB := compact_to_addr st2 c cp.
  Let U := AB + rz.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x0747e8 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let id := d_putid d (depot_hash T).
  Let d' := d_put d (depot_hash T) nT.
  (* [comment removed for export] *)
  Definition COLD_COST : Z := 606208.
  Let L2 : list (word * word) :=
    if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
    else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s).
  Let S2 : list (word * word) :=
    (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
    ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Let sR := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) (a_AL s) (a_top s) (a_bot s).   (* [comment removed for export] *)
  Let ch := mkChunk AB U size rz c CAllocated.
  Let st3 := hit_state st2 c n (tl chunks2) ch.
  Let sF := mkAst st3 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) (a_AL s) (a_top s) (a_bot s).
  (* [comment removed for export] *)
  Let Wr : list ivl := (lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: rf_W lo (bv_unsigned sp) P RI (FA s c) (RB s c) TH CA nf mfa mu mfa' mu'.
  Let Wt : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                       :: (TH + 2800, TH + 3169) :: depot_W d.
  Definition mc_W : list ivl := Wr ++ Wt.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT bsegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2992 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis MISS : pc_count (get_pc st c) = 0.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 262144.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain bsegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz size.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.      (* [comment removed for export] *)
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis OK : lzok bsegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x074720) fc None m (seg_rom bsegs).

  (* [comment removed for export] *)
  Definition malloc_cold_gpost (msF' : machine_state) (mo' : Model) : Prop :=
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       lzok bsegs (a_L sF) (a_S sF) (a_Zr sF) (mkCfg msF' mo')
    /\ restrict (a_L sF) (a_S sF) msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz U) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ ARHEAP sF ((U, size) :: LB) m' /\ awin_vis sF m' /\ flagsx_rep m' /\ AMODELX sF mo' /\ nonvm_same mo mo'   (* [comment removed for export] *)
    /\ DEPOT bsegs d' m' /\ depot_placed sF d' /\ depot_cov d' mo'
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch mc_W m m' /\ wmono bsegs m m'
    /\ avmx s sF mo mo'                                                                   (* [comment removed for export] *)
    /\ (exists junk, rw_cells bsegs m' U [CB (Z.to_nat size) junk]) /\ addressable m' U size
    /\ (forall kaddr, exists st'' ev, am_malloc_k st size kaddr = Some (U, st'', ev) /\ same_but_shadow st'' st3).

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.

  (* [comment removed for export] *)
  Let RQ : rq_rz (compute_req size) = rz /\ rq_needed (compute_req size) = needed /\ rq_primary (compute_req size) = true
           /\ rq_size (compute_req size) = size /\ 16 <= rz <= 2048 /\ size + rz <= needed /\ needed < size + rz + 8 /\ 8 + rz <= needed.
  Proof.
    pose proof (rz_size_facts size) as (RZ & _). unfold compute_req. replace (size =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn -[Z.add Z.mul Z.max round_up rz_size Z.leb Z.ltb Z.eqb].
    replace (round_up (Z.max size 8) 8 + rz_size size <=? kMaxSize) with true by (symmetry; apply Z.leb_le; subst needed rz; lia).
    subst needed rz. unfold round_up. repeat split; try reflexivity; Z.div_mod_to_equations; lia.
  Qed.
  Let HC : 1 <= c <= 30.
  Proof. subst c. apply class_id_le30. destruct RQ as (_ & _ & _ & _ & A & B & _). unfold kMaxSize in SZ. lia. Qed.
  Let CSZ : 32 <= csz <= 65536 /\ needed <= csz /\ csz mod 32 = 0 /\ 8 * csz8 = csz.
  Proof.
    pose proof (class_size_table_facts c ltac:(hci; lia)) as (T1 & T2 & T3 & _). subst csz8 csz.
    pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; destruct RQ as (_ & _ & _ & _ & A & B & _); lia)). subst c.
    repeat split; try lia; Z.div_mod_to_equations; lia.
  Qed.
  Let RF := rf_facts st c WFs HC ROOM.
  Let PURE := refill_pure s m c R HC MISS.
  Let NR : 1 <= n <= 8 /\ n + n = max_count c.
  Proof.
    pose proof (max_count_facts c ltac:(hci; clear - HC; try acb; lia)) as MCF. clear - MCF; try acb. subst n; unfold rf_n; destruct MCF as [M1 M2].
    destruct (proj1 (Z.even_spec _) M2) as [k Hk]; rewrite Hk in *; rewrite (Z.mul_comm 2 k), Z.div_mul by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Tactic Notation "bands_as" simple_intropattern(p) :=
    (let X := fresh "BX" in
     lazymatch goal with B : hidden ((TH + 4096 <= 65536 \/ _) /\ _) |- _ => pose proof B as X; destruct X as [p] end).
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__4 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AllocWalkKit.hidden Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__6 := Elimination for Corelib.Init.Datatypes.list Sort Prop.

  Theorem malloc_arep_cold :
    (forall msF' mo', malloc_cold_gpost msF' mo' -> sreach bsegs Q (mkCfg msF' mo')) -> sreach bsegs Q (mkCfg msF mo).
  Proof.
    (* Repair for the current LPS revision: the recorded KReplay body of [malloc_arep_cold] no
       longer type-checks, because the first conjunct of [amaps_in_ledger] (Bo/AllocRep.v:867-873)
       now asks ledger membership only of an entry of non-zero size.  The body is replaced by the
       explicit text of the same theorem in the same Section of openssl/echconfiglist_parser's
       ASan+UBSan tree (projects/openssl/echconfiglist_parser/proofs/lib/Both/As/AG_MallocCold.v:229-613),
       whose Section variables, hypotheses and Lets have the same shape as this file's; that text
       binds the changed conjunct only as [_].  Nothing is decoded or re-encoded.
       Name substituted: asegs -> bsegs throughout (this tree names its segment list [bsegs],
       Bo/BSegs.v; the source tree keeps the name asegs).
       Literals substituted, source value -> this tree's value (where this tree states it):
         heap floor in BND (four places) and the top of ZR's first band:
           12599296 -> 6832128 = AIMG_TOP 0x684000 ([aapp_env], Bo/AllocRep.v:135; Bo/BSegs.v:40)
         TH band in BANDS: 12599296 -> 6832128 ([akobj_lit], Bo/AllocRep.v:147-148)
         depot frame window in BND and BANDS: 8 * 131072 -> 8 * 262144
           ([depot_placed], Bo/AG_Malloc2.v:36-43; [aapp_lit], Bo/AllocRep.v:150)
         GD, the two d_sb bounds: 1048576 -> 2097152 = 8 * 262144 (same source); the two d_nb
           bounds stay 1048576 = 16 * 65536
         return address passed to [refill_sreach]: wz 0x19b90c -> wz 0x54ac4 (the [malloc_head]
           post, Bo/AW_MallocHead.v:39; [malloc_from_refill] starts there, Bo/AW_MallocTail.v:191-193)
         [ret_pc_even] argument: 1685772 -> 346820 = 0x54ac4 (same address)
         FRC2 last cell: 1667228 -> 328540 = 0x5035c (Bo/AW_MallocHead.v:47, Bo/AW_MallocTail.v:178)
         AFR2 frame words: 1666508 -> 327820 = 0x5008c and 1831964 -> 477160 = 0x0747e8
           (Bo/AW_MallocHead.v:48, Bo/AW_MallocTail.v:72)
         FRA2 second cell: 1832072 -> 477268 = 0x074854 (Bo/AW_MallocHead.v:50, Bo/AW_MallocTail.v:180)
         ZT bands: 65536 <= a < 7849928 \/ 7849956 <= a < 7915480 \/ 12109808 <= a < 12599296
           -> 65536 <= a < 2094728 \/ 2094756 <= a < 2160280 \/ 6354608 <= a < 6832128.  The two gaps
           are the fixed windows of [depot_W] (Bo/AsDepotInv.v:113-114): SSB = 2094728 to SSB + 28,
           and DEP = 2160280 to DEP_MAP1 + 8 = 6354608 (Bo/AsDepotInv.v:24-27); the top is AIMG_TOP.
           The cells of [flagsx_rep] (Bo/AllocRepX.v:165-170) lie inside the bands: AGOT_SSP 0x1203f0
           and ACFLAGS + 219, + 244 (ACFLAGS 0x1bf2e8, Bo/AllocRep.v:33) in the first, ASSPGUARD
           0x681830 and ALIBCPGSZ 0x681ab0 (Bo/AllocRepX.v:33-35) in the third.
       Checked and unchanged: 0x10007fff8000 = AHI_LO (Bo/AsShadow.v:28); 0x2008fff7000 = sh AHI_LO
       (Bo/AsShadow.v:32, ASHADOW_BASE 0x7fff8000 at Bo/BSegs.v:46); 2147446784 and 17594333495296
       (Bo/AllocRep.v:148, 150); the stack offsets -2320, -2144, -2128, -81, -72, -64
       (Bo/AW_MallocHead.v:39-52); the allocator constants (As/AsanAllocModel.v, the same text as
       the source's).  The VISE pc 0x074720, the utrace pc 0x0747e8, DCAP's 262144 and AINST enter
       this text only by name.
       Changed name use: the RESF premise of [refill_sreach] (Bo/AS_Refill4.v:241-242) takes a
       [map_contains] premise that the source's does not, and so does this tree's [ak_resf_hi]
       (Bo/AllocRepX.v:397-398), so that bullet binds it too ([intros a k Ha Hmc], passed as the
       last argument) where the source has [intros a k Ha].  No akernel hypothesis is destructed:
       AK and AK1 go whole to [AMODELX_mat] and the ak_* lemmas, so the akernel split of
       Bo/AllocRepX.v:305 needs no change here. *)
    intros K.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).
    pose proof DPL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct AX as [AWV FXR]. destruct AMX as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0). destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    pose proof (ienv_of_arep s m R) as IEN. rewrite <- TP in IEN.
    assert (UNW : rw_cells bsegs m (TH + 3168) [C1 (b8 0)]).
    { pose proof (proj1 HR) as RR. destruct RR as (_ & _ & _ & THR & _). destruct THR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U0). exact U0. }
    destruct (refill_cells_of_arep s m c R HC MISS) as (q0 & q1 & q2 & q3 & PC1 & PCJ & FAM & QST & TST & RIC & RIJ & EXH & RST & FARR & FAJ & USJ & REN).
    pose proof PURE as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & PCS).
    fold st in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ. fold r in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ.
    fold nf mfa au mu fl in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, RIC, FARR, FAJ, USJ.
    assert (BND : 4096 <= TH /\ TH + 4096 <= aceil /\ TH mod 4096 = 0 /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ sb mod 65536 = 0 /\ 6832128 <= CTX /\ CTX + 160 <= aceil /\ 6832128 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 6832128 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 6832128 <= d_sb d /\ d_sb d + 8 * 262144 <= aceil
            /\ 4096 <= a_top s <= 2^47 /\ 0 <= a_bot s < a_top s /\ aceil <= lo /\ 1 <= c <= 30
            /\ P = TH + 208 + 80 * c /\ CA = TH + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384).
    { assert (E1 : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
      assert (E2 : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
      pose proof (akobj_env _ _ T2 ltac:(unfold kPageSize; clear; lia)) as T2e. pose proof (aapp_env _ _ P2 ltac:(unfold kPtrArrayReserve; clear; lia)) as P2e.
      pose proof (aapp_env _ _ X2 ltac:(clear; lia)) as X2e. pose proof (aapp_env _ _ G10 ltac:(clear; lia)) as G10e. pose proof (aapp_env _ _ G12 ltac:(clear; lia)) as G12e.
      clear - Y1 Y2 Y3 P1 P2e P3 T1 T2e T3 X1 X2e X3 TCX G10e G11 G12e G13 LO HC E1 E2; try acb. unfold TH, sb, CTX, P, CA, RI, a_ri. unfold a_sb in *.
      acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. repeat split; (first [clear - T2e T1 Y2 Y3 Y1 X2e P2e G10e G12e TCX LO HC E1; lia | lia]). }
    (* [comment removed for export] *)
    assert (BANDS : hidden ((TH + 4096 <= 65536 \/ (6832128 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 262144 <= 2147446784 \/ 17594333495296 <= d_sb d))).
    { split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
      split; [pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L|].
      split; [exact (aapp_lit _ _ G10)| exact (aapp_lit _ _ G12)]. }
    assert (BDJ : (TH + 4096 <= sb \/ sb + 137438953472 + 4096 <= TH) /\ (TH + 4096 <= CTX \/ CTX + 160 <= TH) /\ (CTX + 160 <= sb \/ sb + 137438953472 + 4096 <= CTX)).
    { clear - D2 D3 TCX; try acb. unfold TH, sb, CTX. unfold disj, a_sb, kSpaceSize, kPageSize in *. repeat split; lia. }
    pose proof BDJ as (BDJ1 & BDJ2 & BDJ3).
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at bsegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VISE).
    { eapply (@malloc_head _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size d
                ATSD CTX TH (a_top s) (a_bot s) CH sb (wz (if as_cache_inited st then max_count c else 0)) rz needed c CA P).
      - constructor. repeat split; reflexivity.
      - exact LO.
      - clear - HI; try acb; lia.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - exact SZ.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.   (* [comment removed for export] *)
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia].
      - constructor. unfold kSpaceSize. clear - BDJ; try acb. lia.
      - constructor. unfold kSpaceSize. unfold disj, kSpaceSize, kPageSize in G1, G2, G3, G4, G5, G6. clear - G1 G2 G3 G4 G5 G6 G10 G12 BND; try acb. unfold TH, sb, CTX in *. unfold a_sb in *.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      - constructor. unfold AHI_LO, kSpaceSize. acb. clear - BND; try acb. lia.
      - constructor. clear - BND; try acb. lia.
      - clear - BND; try acb. lia.
      - exact FCH.
      - exact Ha0.
      - exact IEN.
      - exact MI.
      - exact ST.
      - exact PC1.
      - exact UNW.
      - exact DEP. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ PO1.
    destruct PO1 as (t0_1 & t1_1 & t2_1 & a4_1 & a5_1 & a6_1 & a7_1 & t3_1 & t4_1 & t5_1 & t6_1 & jk & j8 & rest & m1 & VIS1 & MU1 & WM1 & MI1 & AEN1 & LR & TRNG & NRT
                     & ST1 & FRC1 & AFR1 & FRA1 & FRB1 & FRM1 & PC1' & UNW1 & DEP1).
    (* [comment removed for export] *)
    pose proof (munch_agree _ _ _ MU1) as AG1.
    assert (Z1 : forall a, a < lo /\ a <> TH + 3168 -> outside [(lo, bv_unsigned sp); (TH + 3168, TH + 3169)] a).
    { intros a Ha. cbn [outside]. clear - Ha; try acb. repeat split; try exact I; lia. }
    pose proof CSZ as (CS1 & CS2 & CS3 & CS4).
    assert (BR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384 /\ Z.of_nat (length (wlist (rev fl))) = nf /\ 32 <= csz <= 65536)
      by (clear - U1 U2 U4 U5 U8 CS1; try acb; unfold kFreeArraySize, kUserMapSize, kFreeArrayOffset in *; repeat split; lia).
    name_bands.
    pose proof (conj BND (conj BR BDJ1)) as BB. pose proof (conj BND BDJ1) as BD1.
    assert (PCJ1 : stk bsegs m1 (a_cache s + PCLASS_SIZE * c + 16) (a_cache s + PCLASS_SIZE * c + 80)) by (unfold a_cache, OT_CACHE, PCLASS_SIZE in *; trp stk_transport_pt AG1 WM1 PCJ Z1 BND).
    assert (FAM1 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells bsegs m1 (a_cache s + 80 * c' + 4) [C4 mc] /\ rw_cells bsegs m1 (a_cache s + 80 * c' + 8) [C8 cs]
                                              /\ (as_cache_inited st = true -> mc = wz (max_count c') /\ cs = wz (class_size c'))).
    { intros c' Hc'. destruct (FAM c' Hc') as (mc & cs & V1 & V2 & V3). exists mc, cs. unfold a_cache, OT_CACHE in *. pose proof (conj BND Hc') as B2.
      split; [trp rw_cells_transport_pt AG1 WM1 V1 Z1 B2|]. split; [trp rw_cells_transport_pt AG1 WM1 V2 Z1 B2| exact V3]. }
    assert (QST1 : rw_cells bsegs m1 (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3]) by (trp rw_cells_transport_pt AG1 WM1 QST Z1 BND).
    assert (TST1 : stk bsegs m1 (TH + 2800) (TH + 3168)) by (trp stk_transport_pt AG1 WM1 TST Z1 BND).
    assert (RIC1 : rw_cells bsegs m1 RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]) by (trp rw_cells_transport_pt AG1 WM1 RIC Z1 BD1).
    assert (RIJ1 : stk bsegs m1 (RI + 64) (RI + 68)) by (trp stk_transport_pt AG1 WM1 RIJ Z1 BD1).
    assert (EXH1 : rw_cells bsegs m1 (RI + 68) [C1 (b8 0)]) by (trp rw_cells_transport_pt AG1 WM1 EXH Z1 BD1).
    assert (RST1 : stk bsegs m1 (RI + 69) (RI + 128)) by (trp stk_transport_pt AG1 WM1 RST Z1 BD1).
    assert (FARR1 : u32arr bsegs m1 (FA s c) (wlist (rev fl))) by (trp u32arr_transport_pt AG1 WM1 FARR Z1 BB).
    assert (FAJ1 : stk bsegs m1 (FA s c + 4 * nf) (FA s c + mfa)) by (trp stk_transport_pt AG1 WM1 FAJ Z1 BB).
    assert (USJ1 : stk bsegs m1 (RB s c + au) (RB s c + mu)) by (trp stk_transport_pt AG1 WM1 USJ Z1 BB).
    assert (REN1 : RENV (wz ATP) ATSD (a_ctx s) TH sb (a_ri s) m1).
    { apply (renv_transport (wz ATP) ATSD (a_ctx s) TH sb (a_ri s) m m1 _ REN MU1 WM1); cbn [disjoint_from]; unfold wz, ATP, ATSD; rewrite ?unsigned_lit by (clear; lia); clear - BND BDJ2; try acb; unfold CTX in *; lia. }
    (* [comment removed for export] *)
    pose proof (AMODELX_mat s mo mo1 (conj AM AK) SBM1) as AMX1. pose proof AMX1 as AMX1'. destruct AMX1' as [AM1 AK1].
    pose proof AM1 as AM1'. destruct AM1' as (AIL1 & ASV1 & AB1). destruct AIL1 as (_ & _ & _ & NOV1 & NW1 & NWA1). destruct AB1 as [AB1a AB1b].
    (* [comment removed for export] *)
    eapply (refill_sreach (a_L s) (a_S s) (a_Zr s) msF1 mo1 Q (wz 0x54ac4) (Z_to_bv 64 (bv_unsigned sp + -2320)) gp tp t0_1 t1_1 t2_1
              (Z_to_bv 64 c) (wz P) a4_1 a5_1 a6_1 a7_1 (wz 8) (wz CA) (wz AINST) (wz size) (wz AINST) (wz (bv_unsigned sp + -2128))
              (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) t3_1 t4_1 t5_1 t6_1 F fc m1 lo sb c CA TH CTX ATSD nf mfa au mu fl (as_cache_inited st)).
    all: pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    { exact LO. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - HI; try acb; lia. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - SPT; try acb; lia. }
    { constructor. rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). clear - SPA; try acb. Z.div_mod_to_equations. lia. }
    { exact HC. }
    { reflexivity. }
    { unfold AHI_LO, kSpaceSize, kPageSize. acb. clear - BND; try acb. lia. }
    { constructor. clear - BND; try acb. lia. }
    { rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia. }
    { unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb. repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
    { constructor. clear - BND; try acb. Z.div_mod_to_equations. lia. }
    { constructor. unfold kSpaceSize. clear - BDJ; try acb. lia. }
    { unfold kFreeArraySize. clear - BR; try acb. lia. }
    { constructor. exact U3. }
    { unfold kUserMapSize, kFreeArrayOffset. clear - BR; try acb. lia. }
    { constructor. exact U6. }
    { exact U7. }
    { exact OK1. }
    { exact VIS1. }
    { exact MI1. }
    { rewrite unsigned_lit by (clear - SPR HI BND; try acb; lia). exact ST1. }
    { rewrite TP. exact REN1. }
    { exact U8. }
    { exact PC1'. }
    { exact PCJ1. }
    { exact FAM1. }
    { exact QST1. }
    { exact TST1. }
    { exact RIC1. }
    { exact RIJ1. }
    { exact EXH1. }
    { exact RST1. }
    all: try replace (sb + c * 2 ^ 32) with (RB s c) by (clear - BND; try acb; lia).
    all: try replace (RB s c + kFreeArrayOffset) with (FA s c) by (unfold kFreeArrayOffset; clear - BND; try acb; lia).
    { exact FARR1. }
    { exact FAJ1. }
    { exact USJ1. }
    { intros a k Ha Hmc. exact (ak_resf_hi s mo1 AK1 a k Ha Hmc). }
    { intros a k Ha Hk. apply (ak_prim s mo1 AK1 a k c); [unfold kNumClasses; clear - HC; try acb; lia| exact Ha| unfold kRegionSize; exact Hk]. }
    { exact NW1. }
    { exact NWA1. }
    { exact NOV1. }
    { intros x Hx. apply (ak_zr_sb s mo1 AK1). unfold kSpaceSize, kPageSize. clear - Hx BND; try acb. unfold sb in *. lia. }
    { exact (ak_zrsh s mo1 AK1). }
    { exact (ak_lsh s mo1 AK1). }
    { intros x Hx. apply WM1. exact (AWV x Hx). }
    { unfold ABUDGET, aPhi in AB1b. change (a_st s) with st in AB1b. unfold COLD_COST in PROOM. unfold page_size in AB1b. clear - AB1a AB1b PROOM; try acb. lia. }
    { exact U9. }
    { exact U10. }
    { exact (ak_atop s mo1 AK1). }   (* [comment removed for export] *)
    cbv beta. intros msF2 mo2 RD.
    destruct RD as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & q0' & q1' & q2' & q3' & m2 & L' & S' & RD).
    lazy zeta in RD.
    destruct RD as (OK2 & VIS2 & EL & ES & NVS & VMM & VMR & VML & VMB & VBRK & VMN & EAG & MU2 & WM2 & MI2 & ST2 & PCN & FAM2 & CHA & CHJ
                    & RI2 & RIJ2 & EXH2 & RST2 & FARR2 & FAJ2 & USJ2 & POIu & POIf & QST2 & TST2).
    fold mu' nnew nf1 mfa' au' fl1 n in VIS2, EL, ES, VMN, EAG, MU2, PCN, CHA, CHJ, RI2, FARR2, FAJ2, USJ2, POIu, POIf.
    rewrite unsigned_lit in MU2, ST2 by (clear - SPR HI BND; try acb; lia).
    subst L' S'. fold L2 in OK2, VIS2. fold S2 in OK2, VIS2.
    (* [comment removed for export] *)
    pose proof RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    fold st r in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13. fold nf mfa au mu fl n in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
    pose proof (rf_mfa_delta st c WFs HC ROOM) as FD. fold r in FD. fold nf mfa au mu in FD. fold mfa' in FD.
    assert (BR2 : mu <= mu' <= mu + 262144 /\ mfa <= mfa' <= mfa + 262144 /\ mfa' <= 536870912 /\ 1 <= n <= 8 /\ n <= nf1 /\ 4 * nf1 <= mfa' /\ au <= au' <= mu').
    { unfold kUserMapSize, kFreeArraySize, kFreeArrayMapSize in Q7, Q12, FD. clear - Q1 Q6 Q7 Q11 Q12 FD NR; try acb. repeat split; lia. }
    assert (SHB : 0x2008fff7000 <= sh (RB s c + mu) /\ sh (RB s c + mu) + (mu' - mu) / 8 <= (sh aceil)
                /\ 0x2008fff7000 <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= (sh aceil)).
    { clear - BND BR BR2; try acb. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    pose proof (conj BND (conj BR BR2)) as BB2.
    (* [comment removed for export] *)
    assert (UNW2 : rw_cells bsegs m2 (TH + 3168) [C1 (b8 0)]).
    { eapply rw_cells_transport; [exact UNW1| exact MU2| exact WM2|]. unfold rf_W. cbn [disjoint_from cells_size csize Z.of_nat Nat.add Pos.of_succ_nat].
      unfold PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize.
      bands_as (BT & _).
      repeat lazymatch goal with
        | |- disjoint_from (icW _) _ _ => apply icW_disjoint; clear - BND; try acb; lia
        | |- _ /\ _ => split; [clear - BB2 SHB BDJ1 BT; try acb; (first [clear - BB2 BDJ1 ACEILB BT SHB; lia | lia])|]
        end. }
    (* [comment removed for export] *)
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM02.
    assert (AG02 : agree_on (outside Wr) m m2).
    { intros x Hx Hr. transitivity (m1 (wa x)).
      - apply MU2. rewrite wa_unsigned by exact Hr. revert Hx. unfold Wr, rf_W. cbn [outside app]. clear - HI; try acb. intros (X1 & X2 & X3 & REST).
        split; [clear - X1 HI; try acb; lia| exact REST].
      - apply MU1. rewrite wa_unsigned by exact Hr. revert Hx. unfold Wr. cbn [outside]. clear. intros (X1 & X2 & _). repeat split; try exact I; assumption. }
    pose proof (arep_after_refill s m m2 c L2 S2 (a_AL s) lo (bv_unsigned sp) q0' q1' q2' q3' R HC MISS ROOM LO AG02 WM02
                  PCN FAM2 CHA CHJ RI2 RIJ2 EXH2 RST2 FARR2 FAJ2 USJ2 POIu POIf QST2 TST2 UNW2) as R2.
    pose proof (flagsx_after_refill s m m2 c lo (bv_unsigned sp) R HC MISS ROOM LO AG02 WM02 FXR) as FX2.
    assert (HAL : 0 <= a_AL s <= a_AL s) by (clear - AB1a; lia).   (* [comment removed for export] *)
    pose proof (amodelx_after_refill s mo1 mo2 c L2 S2 (a_AL s) AMX1 OKs HC ROOM (lazy_ranges_okb_nowrap bsegs _ (lzok_ranges OK))
                  eq_refl eq_refl VMM VMR VML (nonvm_same_atop _ _ NVS) VMN EAG HAL) as AMX2.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (rfd_pc_c st c WFs HC ROOM) as PCc.
    assert (HIT2 : pc_count (get_pc st2 c) <> 0) by (unfold st2; rewrite PCc; cbn [pc_count refill_pc]; fold n; clear - NR; try acb; lia).
    pose proof (hit_cells_of_arep sR m2 R2 c ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) HIT2) as HCL. cbv zeta in HCL.
    cbn [a_st a_cache a_sb a_thr] in HCL. fold st TH in HCL. unfold st2 in HIT2. fold st2 in HCL, HIT2.
    rewrite PCc in HCL. cbn [pc_count pc_chunks refill_pc] in HCL. fold n in HCL. fold fl1 in HCL. fold chunks2 in HCL. fold cp in HCL.
    destruct HCL as (j0 & j1 & j2 & j3 & QC1 & QC2 & QC3 & QC4 & QSTb & CHUNK & SHK & TSTb & UNWb & CC & CR & CPS & ABlo & ABhi & INI).
    assert (ABE : AB = sb + c * 2^32 + cp * 16) by (unfold AB; rewrite compact_to_addr_eq, region_beg_eq; reflexivity).
    rewrite <- ABE in CHUNK, SHK, ABlo, ABhi. change (a_sb sR) with sb in ABlo, ABhi. unfold kSpaceSize in ABhi.
    (* [comment removed for export] *)
    assert (GD : (TH + 4096 <= d_nb d \/ d_nb d + 1048576 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 2097152 <= TH)
                 /\ (sb + 137438953472 + 4096 <= d_nb d \/ d_nb d + 1048576 <= sb) /\ (sb + 137438953472 + 4096 <= d_sb d \/ d_sb d + 2097152 <= sb)).
    { unfold disj, kPageSize, kSpaceSize in G1, G2, G3, G4. clear - G1 G2 G3 G4; try acb. unfold TH, sb. lia. }
    assert (DAV : depot_avoid (rf_W lo (bv_unsigned sp + -2320) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') d).
    { pose proof GD as (GD1 & GD2 & GD3 & GD4). unfold depot_avoid, avoids, rf_W, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize.
      bands_as (BT & _ & _ & BN & BS).
      split; [| split; [| split]].
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB BT; try acb; (first [clear - BB2 BT SHB; lia | lia])|]). apply icW_avoids. clear - BND BT; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB BT; try acb; lia|]). apply icW_avoids. clear - BND BT; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB GD1 GD3 BN; try acb; (first [clear - BB2 ACEILB GD1 GD3 SHB BN; lia | lia])|]). apply icW_avoids. clear - BND GD1; try acb; lia.
      - do 13 (apply Forall_cons; [cbn [fst snd]; clear - BB2 SHB GD2 GD4 BS; try acb; (first [clear - BB2 ACEILB GD2 GD4 SHB BS; lia | lia])|]). apply icW_avoids. clear - BND GD2; try acb; lia. }
    pose proof (DEPOT_transport bsegs d m1 m2 _ DEP1 MU2 WM2 DAV) as DEP2.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (ZR : forall a, (65536 <= a < 6832128 \/ TH <= a < TH + 288 \/ CTX <= a < CTX + 160 \/ bv_unsigned sp + -2320 <= a) ->
                 outside (rf_W lo (bv_unsigned sp + -2320) (CA + PCLASS_SIZE * c) (sb + kSpaceSize + REGIONINFO_SIZE * c) (FA s c) (RB s c) TH CA nf mfa mu mfa' mu') a).
    { intros a Ha. unfold rf_W, PCLASS_SIZE, REGIONINFO_SIZE, kSpaceSize. cbn [outside]. bands_as (BT & BC & _).
      (* [comment removed for export] *)
      destruct BDJ as (BDJa & BDJb & BDJc). destruct Ha as [Ha|[Ha|[Ha|Ha]]].
      - clear BDJa BDJb BDJc BDJ2 BC. destruct BT as [BT|[BT|BT]]; repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BT; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BT; try acb; (first [clear - Ha BB2 BT SHB; lia | lia])|]
        end.
      - clear BDJb BDJc BDJ2 BC. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BT; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BT BDJa; try acb; (first [clear - Ha BB2 BDJa ACEILB BT SHB; lia | lia])|]
        end.
      - clear BDJa BDJ2 BT. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI BDJb; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI BC BDJb BDJc; try acb; (first [clear - BB2 Ha ACEILB BDJb BDJc SHB BC; lia | lia])|]
        end.
      - clear BDJa BDJb BDJc BDJ2 BT BC. repeat lazymatch goal with
        | |- outside (icW _) _ => apply outside_icW_far; clear - Ha BND HI; try acb; lia
        | |- _ /\ _ => split; [clear - Ha BB2 SHB HI; try acb; lia|]
        end. }
    pose proof (munch_agree _ _ _ MU2) as AG2.
    assert (AEN2 : AENV tp ATSD CTX TH sb (bv_unsigned sp + -2128) T rest m2).
    { eapply (aenv_transport_pt _ tp ATSD CTX TH sb _ T rest m1 m2 AEN1 AG2 WM2).
      - intros a Ha. apply ZR. left. unfold AIMG_LO, AIMG_TOP in Ha. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - intros a Ha. apply ZR. clear - Ha; try acb. lia.
      - rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - unfold ATSD, AIMG_TOP. clear; lia. }
    assert (FRC2 : rw_cells bsegs m2 (bv_unsigned sp + -2320) [C8 (wz rz); C8 (wz needed); C8 (wz 8); C8 (wz size); C8 (wz 1); C8 (wz 328540)]) by (trp rw_cells_transport_pt AG2 WM2 FRC1 ZR BND).
    assert (AFR2 : aframe (Z_to_bv 64 (bv_unsigned sp + -2144)) (wz 327820) sp (wz size) (wz 477160) (wz 1) (Z_to_bv 64 (bv_unsigned sp + -2128))
                          (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 m2 j8).
    { unfold aframe in AFR1 |- *. rewrite unsigned_lit in AFR1 |- * by (clear - SPR HI BND; try acb; lia). trp rw_cells_transport_pt AG2 WM2 AFR1 ZR BND. }
    assert (FRA2 : rw_cells bsegs m2 (bv_unsigned sp + -2144) [C8 sp; C8 (wz 477268)]) by (trp rw_cells_transport_pt AG2 WM2 FRA1 ZR BND).
    assert (FRB2 : rw_cells bsegs m2 (bv_unsigned sp + -72) [C8 sp]) by (trp rw_cells_transport_pt AG2 WM2 FRB1 ZR BND).
    assert (FRM2 : rw_cells bsegs m2 (bv_unsigned sp + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (trp rw_cells_transport_pt AG2 WM2 FRM1 ZR BND).
    (* [comment removed for export] *)
    unfold wz in VIS2. rewrite (ret_pc_even 346820) in VIS2 by (clear; lia).
    eapply (evt_sreach_lazy_at bsegs L2 S2 (a_Zr s) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (malloc_from_refill ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 lo size d ATSD CTX TH (a_top s) (a_bot s) T rest
                sb n (max_count c) chunks2 j0 j1 j2 j3 rz needed c csz csz8 (Z.min size 4096) CA P cp AB U nT id).
      - constructor. repeat split; try reflexivity. exact ABE.
      - exact LO.
      - clear - HI; try acb; lia.
      - constructor. exact SPA.
      - constructor. exact SPT.
      - exact SZ.
      - constructor. rewrite TP. unfold wz, ATP, AIMG_TOP. rewrite unsigned_lit by (clear; lia). clear; lia.
      - constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T2. clear - BND T2 X2; try acb.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia | Z.div_mod_to_equations; lia].
      - constructor. unfold kSpaceSize. clear - BDJ; try acb. lia.
      - constructor. unfold kSpaceSize. clear - GD G5 G6 G10 G12 BND; try acb. unfold disj in *. unfold CTX in *.
        repeat match goal with |- _ /\ _ => split end; first [assumption | (first [clear - GD; lia | lia])].
      - constructor. unfold AHI_LO, kSpaceSize. acb. clear - BND; try acb. lia.
      - exact CC.
      - exact CR.
      - exact CPS.
      - constructor. split; [exact ABlo| exact ABhi].
      - constructor. clear - BND; try acb. lia.
      - exact DCAP.
      - clear - BND; try acb. lia.
      - exact NRT.
      - exact LR.
      - exact TRNG.
      - exact AEN2.
      - exact MI2.
      - exact ST2.
      - exact FRC2.
      - exact AFR2.
      - exact FRA2.
      - exact FRB2.
      - exact FRM2.
      - exact QC1.
      - exact QC2.
      - exact QC3.
      - exact QC4.
      - exact QSTb.
      - exact CHUNK.
      - exact SHK.
      - exact TSTb.
      - exact UNWb.
      - exact DEP2. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ PO3.
    destruct PO3 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j0' & j1' & j2' & j3' & b1 & m3 & VIS3 & MU3 & WM3 & MI3 & ST3 &
                    QC1' & QC3' & QC4' & QST' & HDR & B1 & LEFT & FILL & SLACK & SHA & TST' & UNW' & DEP').
    (* [comment removed for export] *)
    assert (HR2 : ARHEAP sR LB m2) by (destruct HR as (_ & ND & EQ); split; [exact R2| split; [exact ND| exact EQ]]).
    assert (DPL2 : depot_placed sR d) by exact DPL.
    pose proof (arheap_after ra sp s0 m2 sR LB d lo size CH HR2 DPL2 LO ltac:(hci; clear - HI; try acb; lia) SZ HIT2 m3 j0' j1' j2' j3' b1) as AH.
    pose proof (new_block ra sp s0 m2 sR LB d lo size CH HR2 DPL2 LO ltac:(hci; clear - HI; try acb; lia) SZ HIT2 DCAP m3) as NB.
    cbn [a_st a_thr a_ctx a_fsb a_L a_S a_Zr a_AL a_top a_bot] in AH, NB. fold st TH rz needed in AH, NB. fold c in AH, NB. fold st2 csz in AH, NB. fold csz8 in AH.
    rewrite PCc in AH, NB. cbn [pc_count pc_chunks refill_pc] in AH, NB. fold n fl1 in AH, NB. fold chunks2 in AH, NB. fold cp in AH, NB. fold AB in AH, NB. fold U in AH, NB.
    specialize (AH MU3 WM3 QC1' QC3' QC4' QST' HDR B1 LEFT FILL SLACK SHA TST' UNW').
    specialize (NB FILL SLACK SHA).
    pose proof RQ as (RQ1 & RQ2 & RQ3 & RQ4 & RQ5 & RQ6 & RQ7 & RQ8). rewrite RQ4 in AH. fold ch in AH. fold st3 in AH.
    apply K. unfold malloc_cold_gpost.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m3.
    split; [exact OK3|]. split; [exact VIS3|]. split; [exact AH|].
    split.
    { (* [comment removed for export] *)
      intros x Hx. cbn [a_S] in Hx. unfold S2 in Hx. rewrite !in_rangesb_app in Hx.
      apply Bool.orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [| apply Bool.orb_true_iff in Hx; destruct Hx as [Hx|Hx]].
      - apply in_rangesb_if in Hx.
        apply in_window1 in Hx; [| clear - SHB; try acb; lia| clear - BR2; try acb; Z.div_mod_to_equations; lia| clear - SHB; try acb; lia].
        apply (poisoned_visible m2 m3 _ _ _ x POIf WM3). rewrite Z2Nat.id by (clear - BR2; try acb; Z.div_mod_to_equations; lia). exact Hx.
      - apply in_rangesb_if in Hx.
        apply in_window1 in Hx; [| clear - SHB; try acb; lia| clear - BR2; try acb; Z.div_mod_to_equations; lia| clear - SHB; try acb; lia].
        apply (poisoned_visible m2 m3 _ _ _ x POIu WM3). rewrite Z2Nat.id by (clear - BR2; try acb; Z.div_mod_to_equations; lia). exact Hx.
      - apply WM3, WM02. exact (AWV x Hx). }
    split.
    { (* [comment removed for export] *)
      pose proof (munch_agree _ _ _ MU3) as AG3.
      assert (ZT : forall a, (65536 <= a < 2094728 \/ 2094756 <= a < 2160280 \/ 6354608 <= a < 6832128) -> outside Wt a).   (* [comment removed for export] *)
      { intros a Ha. unfold Wt, depot_W. cbn [outside app]. bands_as (BT & _). clear - Ha BND ABlo SHB CSZ BT; try acb. unfold sb in *.
        assert (0x2008fff7000 <= sh AB) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; (first [clear - H0 H ABlo BND; lia | lia])).
        destruct Ha as [Ha|[Ha|Ha]]; (repeat split; try exact I; (first [clear - Ha BND BT ABlo H; lia | lia])). }   (* [comment removed for export] *)
      destruct FX2 as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *.
      split; [trp rw_cells_transport_pt AG3 WM3 FXa ZT BND|]. split; [trp rw_cells_transport_pt AG3 WM3 FXb ZT BND|].
      split; [exists g; trp rw_cells_transport_pt AG3 WM3 FXc ZT BND|]. split; [trp rw_cells_transport_pt AG3 WM3 FXd ZT BND|].
      exists bb; trp rw_cells_transport_pt AG3 WM3 FXe ZT BND. }
    split; [exact (amodelx_hit sR mo3 c n (tl chunks2) ch (AMODELX_mat sR mo2 mo3 AMX2 SBM3))|].
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat _ _ SBM1) (nonvm_same_trans _ _ _ NVS (nonvm_same_mat _ _ SBM3)))|].
    split; [exact DEP'|].
    split; [unfold depot_placed; unfold d'; rewrite d_nb_put, d_sb_put; exact DPL|].
    split.
    { unfold depot_cov. unfold d'. rewrite d_nb_put, d_sb_put. intros x Hx.
      rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). exact (DCOV x Hx). }
    split; [exact MI3|]. split; [exact ST3|].
    split.
    { intros x Hx. unfold mc_W in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2]. rewrite (MU3 x Hx2).
      pose proof (AG02 (bv_unsigned x) Hx1 (bv_unsigned_in_range _ x)) as E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E. }
    split; [eapply wmono_trans; [exact WM02| exact WM3]|].
    split. { apply avmx_same; [| reflexivity]. rewrite (same_but_materialized_vmmaps mo2 mo3 SBM3), VMM, (same_but_materialized_vmmaps mo mo1 SBM1). reflexivity. }
    split; [exact (proj1 NB)|]. split; [exact (proj2 NB)|].
    (* [comment removed for export] *)
    intros kaddr.
    assert (WF2 : WF st2) by exact (WF_refill st c WFs HC MISS ROOM).
    assert (TK0 : forall l : list Z, n = zlen l -> l = hd 0 l :: tl l).
    { intros [|y l] H; [exfalso; unfold zlen in H; cbn in H; clear - H NR; try acb; lia| reflexivity]. }
    pose proof (TK0 chunks2 CC) as TK. clear TK0. change (hd 0 chunks2) with cp in TK.
    assert (CV2 : carved st2 c AB).
    { apply carved_cache; [exact WF2| unfold kNumClasses; clear - HC; try acb; lia|]. unfold st2. rewrite PCc. change (pc_chunks (refill_pc st c)) with chunks2. rewrite TK. left. reflexivity. }
    pose proof CV2 as (_ & _ & CVa & CVm & CVle). rewrite region_beg_eq in CVa, CVm, CVle. change (as_space_beg st2) with sb in CVa, CVm, CVle. fold csz in CVm, CVle.
    pose proof (rz_size_facts size) as (_ & RZ16 & RZC). fold rz in RZ16, RZC. pose proof SZ as SZ2. unfold kMaxSize in SZ2.
    assert (UM8 : U mod 8 = 0).
    { (* [comment removed for export] *)
      unfold U. destruct BND as (_ & _ & _ & _ & _ & SB64 & _). clear - CVm RZ16 SB64 CS3 CS1.
      assert (Zcsz : csz <> 0) by lia.
      destruct (proj1 (Z.mod_divide _ csz Zcsz) CVm) as [q Hq].
      destruct (proj1 (Z.mod_divide rz 16 ltac:(lia)) RZ16) as [u Hu].
      destruct (proj1 (Z.mod_divide sb 65536 ltac:(lia)) SB64) as [t Ht].
      destruct (proj1 (Z.mod_divide csz 32 ltac:(lia)) CS3) as [k Hk].
      apply Z.mod_divide; [lia|]. exists (4 * q * k + 8192 * t + 536870912 * c + 2 * u). (first [clear - Hk Ht Hu Hq; nia | nia]). }
    assert (IM : forall a, sb <= a -> a + 1 <= aceil -> addr_is_in_mem a = true).
    { intros a Ha Hb. apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. clear - Ha Hb BND; try acb. lia. }
    assert (HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0).
    { change (as_space_beg st) with sb. unfold kHighMemBeg, kHighMemEnd, kSpaceSize. clear - BND; try acb. Z.div_mod_to_equations. lia. }
    destruct (am_malloc_cold st c WFs HC MISS ROOM HM size kaddr cp (tl chunks2) ltac:(hci; clear - SZ; try acb; lia)) as (st'' & ev & EQ & SB).
    - unfold size_too_big, kMaxAllowedMalloc. rewrite RQ2, RQ4. change (rq_n (compute_req size)) with size. change (2^40) with 1099511627776.
      replace (1099511627776 <? size) with false by (symmetry; apply Z.ltb_ge; clear - SZ2 RQ6 RQ5; try acb; lia).
      replace (1099511627776 <? needed) with false by (symmetry; apply Z.ltb_ge; clear - SZ2; try acb; lia). reflexivity.
    - rewrite RQ2. exact (proj2 SZ).
    - rewrite RQ2. reflexivity.
    - exact TK.
    - rewrite RQ1. change (compact_to_addr st c cp + rz) with U. rewrite land7_mod8. exact UM8.
    - rewrite RQ1. change (compact_to_addr st c cp + rz) with U. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 SZ2; try acb; lia.
    - rewrite RQ1, RQ4. change (compact_to_addr st c cp + rz) with U. rewrite land_lnot7'. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 SZ2; try acb; Z.div_mod_to_equations; lia.
    - rewrite RQ1, RQ4. change (compact_to_addr st c cp + rz) with U. rewrite land_lnot7'. apply IM; unfold U; clear - BND ABlo ABhi RQ6 CS2 RQ5 RQ7 SZ2; try acb; Z.div_mod_to_equations; lia.
    - rewrite RQ1. clear - RZC; try acb. clearbody rz. lia.
    - exact RQ3.
    - rewrite RQ1, RQ2, RQ4. clear - RQ6; try acb. lia.
    - exists st'', ev. rewrite RQ1 in EQ. rewrite RQ1, RQ4 in SB. split; [exact EQ| exact SB].
  Qed.
End MallocColdGlue.

End HCW2.

