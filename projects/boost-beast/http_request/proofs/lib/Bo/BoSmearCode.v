(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan BothImages BothPlanImages.
Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma both_smear_x : 0 <= x_smear BOTH_H /\ x_smear BOTH_H + 112 < 2 ^ 64.
Proof. cbn [x_smear BOTH_H]. lia. Qed.

Lemma both_smear_fwa :
  fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H)) = Some (0x00155593%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 4)) = Some (0x55555637%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 8)) = Some (0x333336b7%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 12)) = Some (0x0f0f1737%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 16)) = Some (0x010107b7%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 20)) = Some (0x00b56533%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 24)) = Some (0x5556059b%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 28)) = Some (0x3336861b%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 32)) = Some (0xf0f7069b%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 36)) = Some (0x1017871b%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 40)) = Some (0x00255793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 44)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 48)) = Some (0x02059793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 52)) = Some (0x00f585b3%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 56)) = Some (0x02061793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 60)) = Some (0x00f60633%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 64)) = Some (0x02069793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 68)) = Some (0x00f686b3%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 72)) = Some (0x02071793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 76)) = Some (0x00f70733%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 80)) = Some (0x00455793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 84)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 88)) = Some (0x00855793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 92)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 96)) = Some (0x01055793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 100)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 104)) = Some (0x02055793%bv : bv 32)
    /\ fetch_word BSEGS2 (Z_to_bv 64 (x_smear BOTH_H + 108)) = Some (0x00f56533%bv : bv 32).
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothPlanImages.BSEGS2); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlan.AP.x_smear); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothImages.BOTH_H); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.decidable.bool_decide_eq_true_1); constr:(@stdpp.base.decide_rel); constr:(@stdpp.option.option_eq_dec); constr:(@stdpp.bitvector.definitions.bv_eq_dec); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@stdpp.decidable.bool_decide)|] Array.empty "#,j###>#>#?#.#6#,#*#'#)#(#0#1#<#;#=#5#+#4#/#-#:#@#9#8#&#7#3#21#1$#2$#)&#3$#4%#5%#6)#7%#8&#9%#:'#;%#<&#=%$G$#$#$#$#UH#UJ#UK#$&UH#ULM'$#(E##/$###$###$###$###$#####$#$###$#$#####&#/>#F0>#%>9#&s#%,=#'?#(E#$3##$###$###$#####$#$#$#####$#######&#/s#8#F0s#8#%s#88#&s#>,s#7#'s#9#(E##G$#$#####$#$#####$#$#####$#$#####$#####$###$#####$#######&#/s#]#F0s#]#%s#]s###&A,s#\#'s#^#(E##s#'##$#$#$#$#########$#$#$###$#######$#$#####$#######&#/s$##F0s$##%s$#@#&s$(,s#~#'s$$#(E#$s$'##$#$#$#$#$#########$#####$#######&#/s$=#F0s$=#%s$=8#$s$7&#,s$=#'s$?#(E##s$=$###$###$#####$#$###$###$#$#####$#$#####&#/s$[#F0s$[#%s$[;#$s#{&#,s$[#'s$]#(E#$s$N$#$#$###$#####$#$#####$#####&#/s$s#F0s$s#%s$s5#$s#p$#&#,s$t#'s$v#(E##s$6##$###$#$#$#$#####$#$#$#$#####$#####&#/s%4#F0s%4#%s%49#&s%8,s%3#'s%5#(E##s$+####$#$#$#$#$#####$###$#$#####$#####&#/s%O#F0s%O#%s%O9##s%V$#$#&#,s%Q#'s%S#(E##s$/######$#$#$#$#######$#$#$#####$#####&#/s%m#F0s%m#%s%m9#$s$2&#,s%m#'s%o#(E##s#$$###$###$#########$#$###$#$#####&#/s&+#F0s&+#%s&+7#$s$F&#,s&+#'s&-#(E##s%+$###$#####$#$###$###$#$#####$#$#####&#/s&G#F0s&G#%s&G9#$s$J&#,s&G#'s&I#(E##s&L$#####$#$###$#########$#$###$#$#####&#/s&c#F0s&c#%s&c9##s&($#$#&#,s&e#'s&g#(E##s#:$#$#$#$###$#####$#####$#$#####&#/s&~#F0s&~#%s&~6#$s$h&#,s&~#'s'$#(E##s#9$#$#$#$###$#########$#$###$#$#####&#/s'=#F0s'=#%s'=8#&s&7,s'<#'s'>#(E##s#o$#$#$#$#$#$#####$#$#$#####$#$#####&#/s'W#F0s'W#%s'W8#&s'W,s'V#'s'X#(E##s#5$#$###$#########$#$###$#$#####&#/s'o#F0s'o#%s'o6##s'u$#$#&#,s'q#'s's#(E##s#6$#$#$#$#####$###$#####$#$#####&#/s(.#F0s(.#%s(.6#$s%;&#,s(.#'s(0#(E##s#j$#$#$###$#########$#$###$#$#####&#/s(H#F0s(H#%s(H7##s%W$#$#&#,s(J#'s(L#(E##s#l$#$#$#$#$#######$#$#####$#$#####&#/s(d#F0s(d#%s(d7#$s%U&#,s(d#'s(f#(E##s#W$###$###$#########$#$###$#$#####&#/s(~#F0s(~#%s(~7#$s(v&#,s(~#'s)$#(E#%s)(#s%@$s%[&#,s)(#'s)*#(E##s)2$###$###$###$#########$#$###$#$#####&#/s)D#F0s)D#%s)D9##s'`$#$#&#,s)F#'s)H#(E#%s)L#s%d$s%c&#,s)L#'s)N#(E##s)U$###$###$###$#########$#$###$#$#####&#/s)h#F0s)h#%s)h9#$s)+$#&#,s)i#'s)k#(E#%s)o#s&+$s%h&#,s)o#'s)q#(E#$s&(##$###$#########$#$###$#$#####&#/s*,#F0s*,#%s*,6##s&'$#$#&#,s*.#'s*0#(E#%s*4#s&L.+#.s#%#.s#-#.s#J#.s#S#.s#p#.s#w#.s$6#.s$S#.s$n#.s%.#.s%G#.s%b#.s%~#.s&>#.s&[#.s&x#.s'7#.s'V#.s'r#.s(4#.s(M#.s(l#.s)+#.s)N#.s)t#UIs*OUNs*RVOs*R#)s*Rs*R%#s*Ms*7VPCD*s*8$%C#Dm$%#+s*;'#)s*Xs*X+)s*8s*#*s*##%C#Dm$*#+s*&&#)s*]s*]0.s*#s)_*s)_#%C#Dm$/#+s)b&#)s*bs*b53s)_s)B*s)B#%C#Dm$4#+s)E&#)s*gs*g:8s)Bs)-*s)-#%C#Dm$9#+s)0&#)s*ls*l?=s),s(p*s(p#%C#Dm$>#+s(s&#)s*qs*qs#$Bs(os(]*s(]#%C#Dm$s###+s(`&#)s*vs*vs#)s#'s([s(E*s(E#%C#Dm$s#(#+s(H&#)s*{s*{s#.s#,s(Es(/*s(/#%C#Dm$s#-#+s(2&#)s+$s+$s#3s#1s(,s'r*s'r#%C#Dm$s#2#+s'u&#)s+)s+)s#8s#6s'qs']*s']#%C#Dm$s#7#+s'`&#)s+.s+.s#=s#;s'\s'F*s'F#%C#Dm$s#<#+s'I&#)s+3s+3s#Bs#@s'Es'/*s'/#%C#Dm$s#A#+s'2&#)s+8s+8s#Gs#Es',s&u*s&u#%C#Dm$s#F#+s&x&#)s+=s+=s#Ls#Js&ts&_*s&_#%C#Dm$s#K#+s&b&#)s+Bs+Bs#Qs#Os&_s&J*s&J#%C#Dm$s#P#+s&M&#)s+Gs+Gs#Vs#Ts&Js&7*s&7#%C#Dm$s#U#+s&:&#)s+Ls+Ls#[s#Ys&4s%}*s%}#%C#Dm$s#Z#+s&$&#)s+Qs+Qs#`s#^s%|s%h*s%h#%C#Dm$s#_#+s%k&#)s+Vs+Vs#es#cs%es%Q*s%Q#%C#Dm$s#d#+s%T&#)s+[s+[s#js#hs%Ps%<*s%<#%C#Dm$s#i#+s%?&#)s+`s+`s#os#ms%;s'x*s%;#%C#Dm$s#n#+s%>&#)s+es+es#ts#rs%:s%$*s%$#%C#Dm$s#s#+s%'&#)s+js+js#ys#ws$}s(&*s$}#%C#Dm$s#x#+s%$&#)s+os+os#~s#|s$|s$f*s$f#%C#Dm$s#}#+s$i&#)s+ts+ts$'s$%s$ds(0*s$d#%C#Dm$s$&#+s$g&#)s+ys+ys$,s$*s$cs$P*s$P#%C#Dm$s$+#+s$S&#)s+~s+~s$1s$/s$Ms(:*s$M#%C#Dm$s$0#+s$P&#-s$Ys$Q(#-s$ss$Q.#-s${s$Q4#-s%<s$Q:#-s%Es$Q@#-s%bs$Qs#&#-s%is$Qs#,#-s&(s$Qs#2#-s&Es$Qs#8#-s&`s$Qs#>#-s&|s$Qs#D#-s'9s$Qs#J#-s'Ts$Qs#P#-s'ps$Qs#V#-s(0s$Qs#\#-s(Ms$Qs#b#-s(js$Qs#h#-s))s$Qs#n#-s)Hs$Qs#t#-s)ds$Qs#z#-s*&s$Qs$$#-s*?s$Qs$*#-s*^s$Qs$0#-s*ys$Qs$6#-s+@s$Qs$<#-s+fs$Qs$B#-s,%s$Qs$H##"). Qed.
