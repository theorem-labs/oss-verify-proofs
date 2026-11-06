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
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsIface5 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2 AXRep_fields.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit X8SRKit AXImgKit X8_P_verb_stmt X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record hdrv := mkHV { hv_mp : Z ; hv_ml : Z ; hv_tp : Z ; hv_tl : Z ; hv_ver : Z ; hv_vb : Z }.

Definition HdrCells (h : hdrv) : list cell :=
  [C8 (wz (hv_mp h)); C8 (wz (hv_ml h)); C8 (wz (hv_tp h)); C8 (wz (hv_tl h)); C4 (wz (hv_ver h)); C4 (wz (hv_vb h))].

(* [comment removed for export] *)
Definition hdr_empty (h : hdrv) : Prop :=
  hv_mp h = 0 /\ hv_ml h = 0 /\ hv_tp h = 0 /\ hv_tl h = 0 /\ 0 <= hv_ver h < 2^32 /\ 0 <= hv_vb h < 2^32.

Definition O_PR_HDR  : Z := 128.   (* [comment removed for export] *)
Definition O_PR_USED : Z := 241.   (* [comment removed for export] *)
Definition O_PR_MERGE : Z := 242.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FLD_CONNECTION := 25. Definition FLD_CONTENT_LENGTH := 31. Definition FLD_PROXY_CONNECTION := 73.
Definition FLD_TRANSFER_ENCODING := 108. Definition FLD_UPGRADE := 109.

Definition dof_core (c c' : pcore) : Prop :=
  pc_state c' = pc_state c /\ pc_hlim c' = pc_hlim c /\ pc_blim_has c' = pc_blim_has c /\ pc_blim c' = pc_blim c
  /\ pc_skip c' = pc_skip c /\ 0 <= pc_f c' < 2^14 /\ 0 <= pc_len c' < 2^64 /\ 0 <= pc_len0 c' < 2^64.

Definition dof_out (E' : ecv) : Prop :=
  E' = EC_clear
  \/ (ec_cat E' = AG_HTTP_CAT /\ ec_failed E' = true /\ ec_ok E' /\ 2 <= ec_flags E'
      /\ In (ec_val E') [HE_BAD_VALUE; HE_BAD_CONTENT_LENGTH; HE_BAD_TRANSFER_ENCODING; HE_MULTIPLE_CONTENT_LENGTH]).
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma dof_core_ok : forall c c', pcore_ok c -> dof_core c c' -> pcore_ok c'.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pcore); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pcore_ok); constr:(@kc__1); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_blim_has); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_blim); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_len); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_len0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_skip); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_hlim); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_state); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_state2_stmt.dof_core); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.or_ind)|] [|@z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat14; @__sat12; @__sat10; @__sat9; @__sat11; @__sat13; @__p1; @H17; @H16; @H15; @H14; @H13; @H12; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H2; @H1; @H0; @H; @D8; @D7; @D6; @D5; @D4; @D3; @D2; @D1; @Ff; @Stt; @Hl; @Sk; @Ln0; @Ln; @Bl; @Bh; @c'; @c|] "#3|#q$`#{#y$K###$$L$J#%#&#q#*#-#.#2#A#B#]#)#D#F#J#^#(#,#E#H$S#0#1#4#I#L#M#N#T#_$6#h#}#5#6#C#O#P#Q#R#8#9#:#G#S#U$;#g#<#=#>#K#V$\$0#'#3#@#X#Y#Z$8$B$A$Q$W$X#c$`#`#b#d#f#j#k#l#n#p#t#+#/#7#;#?#W#[#\$:$9$@$?$C$>$=$<$D$E$F$G$I$P$M$T$U$Y$Z$V$]#a#e#i#m$b#~$#$)#x$1$*$+$.$($-$,$$#z#u$&#v#|$4$/$a$2$O$N#w$'$H$[$3$R$%$5$7$_$^F$>%$?%$@%$A&$B$$C$$D$$E$$F$$G&$H$$I$$J$$K$$L$$M($N$$O'$P&#&&$Q($R%$S'$T*$U%$V$$W+$X*$Y)$Z%$[%$\%$]&$^$$_&0G/J&D#C3S9&D%#;%#.J$C#1S93#<$1#1#3#A'#$+##+#+J$C#1-1#1#1#1#3#A2#%+##+#(J$C#%$'#$#)J$C#%$+#$#-J$C#111#1#1#1#<#1#3#$,##,#*J<S93#3B<%3#3s#$<s#&3#3s#0<s#23#USOD5D$#5D'#5D)#5D,#5D.#5D1#5D3#5Ds#=#5Ds#D#5DC#,D9#'J$C#183#As#E#%'##'##*##s####s#0##s#5##s#:##s#F##s#R#8KJ0Kk##$#j##&#.K$C#$$s#P#$#+K$C#%$s#I#$#(K$C#%$s#M#$#)K$C#%$s#Q#$#-K$C#$$s#A#$#*K,D#s#+'K$C#%$s#(#$##'##*##/##4##9##>#/SP&D#C&D$s#{;$#.S)$C#$$s#t#$#+S)$C#%$s#m#$#(S)$C#%$s#q#$#)S)$C#%$s#u#$#-S)$C#$$s#e#$#*S),D#s#O'S)$C#%$s#L#$##'##*##/##4##9##>#.S$$C#$$s$8#$#+S$$C#%$s$1#$#(S$$C#%$s$5#$#)S$$C#%$s$9#$#-S$$C#$$s$)#$#*S$,D#s#o'S$$C#%$s#l#$##'##*##/##4##9##>#8MS$0Mk##$#j##&#+M$C#%$s$Q#$#(M$C#%$s$U#$#)M$C#%$s$Y#$#-M$C#$$s$I#$#*M,D#s$3'M$C#%$s$0#$##'##*##/##4##9#.Sh$C#$$s$w#$#+S*$C#%$s$p#$#(S*$C#%$s$t#$#)S*$C#%$s$x#$#-S*$C#$$s$h#$#*S*,D#s$R'S*$C#%$s$O#$##'##*##/##4##9#+N$C#%$s%/#$#(N$C#%$s%3#$#)N$C#%$s%7#$#-N$C#$$s%'#$#*N,D#s$m'N$C#%$s$j#$##'##*##/##4##9#8ON0Ok##$#j##&#(O$C#%$s%N#$#)O$C#%$s%R#$#-O$C#$$s%B#$#*O,D#s%,'O$C#%$s%)#$##'##*##/##4#+Si$C#%$s%d#$#(S.$C#%$s%h#$#)S.$C#%$s%l#$#-S.$C#$$s%\#$#*S.,D#s%F'S.$C#%$s%C#$##'##*##/##4#(S/$C#%$s%~#$#)S/$C#%$s&&#$#-S/$C#$$s%r#$#*S/,D#s%\'S/$C#%$s%Y#$##'##*##/##4#8PS/0Pk##$#j##&#)P$C#%$s&<#$#-P$C#$$s&,#$#*P,D#s%r'P$C#%$s%o#$##'##*##/#(SQ$C#%$s&M#$#)S0$C#%$s&Q#$#-S0$C#$$s&A#$#*S0,D#s&+'S0$C#%$s&(#$##'##*##/#)S:$C#%$s&b#$#-S:$C#$$s&R#$#*S:,D#s&<'S:$C#%$s&9#$##'##*##/#8S;S:0S;k##$#j##&#-S;$C#$$s&c#$#*S;,D#s&M'S;$C#%$s&J#$##'##*#)Sj$C#%$s''#$#-SA$C#$$s&s#$#*SA,D#s&]'SA$C#%$s&Z#$##'##*#-SB$C#$$s'##$#*SB,D#s&i'SB$C#%$s&f#$##'##*#8SCSB0SCk##$#j##&#*SC,D#s&u'SC$C#%$s&r#$##'#-Sk$C#$$s':#$#*SI,D#s'$'SI$C#%$s&}#$##'#*SJ,D#s'+'SJ$C#%$s'(#$##'#8SKSJ0SKk##$#j##&#'SK$C#%$s'1#$#*Sl,D#s':'SR$C#%$s'7#$#8QSR*Q*R&D$#-Q-R&D$#/Q/R&D$#.Q.R&D$#)Q)R&D$#'Q$C#%$s'K#$#+Q$C#%$s(&#$#(Q$C#%$s(*#$##'##,##1##5##9##=##A#0Rj##$#-S<&Ds###/S<&DB#.S<&DA#)S<&D@#'R$C#%$s'h#$#+R$C#%$s(C#$#(R$C#%$s(G#$##'##,##1##4##7##:#*S<*S%&D$#-S%-S+&D$#/S%/S+&D$#.S%.S+&D$#)S%)S+&D$#'S%$C#%$s(-#$#+S%$C#%$s(d#$#(S%$C#%$s(h#$##'##,##1##5##9##=#-S&&D@#/S&&D?#.S&&D>#)S&&D=#'S+$C#%$s(G#$#+S+$C#%$s(~#$#(S+$C#%$s)&#$##'##,##1##4##7##:#0S&j##$#/SD&D=#.SD&D=#)SD&D=#'S&$C#%$s(a#$#+S&$C#%$s)<#$#(S&$C#%$s)@#$##'##,##1##4##7#-SD-S,&D$#/S,/S1&D$#.S,.S1&D$#)S,)S1&D$#'S,$C#%$s(~#$#+S,$C#%$s)Y#$#(S,$C#%$s)]#$##'##,##1##5##9#/S'&D<#.S'&D;#)S'&D:#'S1$C#%$s)9#$#+S1$C#%$s)p#$#(S1$C#%$s)t#$##'##,##1##4##7#0S'j##$#.SL&D:#)SL&D:#'S'$C#%$s)P#$#+S'$C#%$s*+#$#(S'$C#%$s*/#$##'##,##1##4#/SL/S2&D$#.S2.S3&D$#)S2)S3&D$#'S2$C#%$s)i#$#+S2$C#%$s*D#$#(S2$C#%$s*H#$##'##,##1##5#.S4&D8#)S4&D7#'S3$C#%$s)}#$#+S3$C#%$s*X#$#(S3$C#%$s*\#$##'##,##1##4#0S4j##$#)S=&D7#'S4$C#%$s*5#$#+S4$C#%$s*l#$#(S4$C#%$s*p#$##'##,##1#.S=.S>&D$#)S>)S?&D$#'S>$C#%$s*J#$#+S>$C#%$s+%#$#(S>$C#%$s+)#$##'##,##1#)S@&D4#'S?$C#%$s*[#$#+S?$C#%$s+6#$#(S?$C#%$s+:#$##'##,##1#0S@j##$#'S@$C#%$s*l#$#+S@$C#%$s+G#$#(S@$C#%$s+K#$##'##,#)SE)S5&D$#'S5$C#%$s*}#$#+S5$C#%$s+X#$#(S5$C#%$s+\#$##'##,#'SF$C#%$s+/#$#+SF$C#%$s+f#$#(SF$C#%$s+j#$##'##,#0SMj##$#+SM$C#%$s+r#$#(SM$C#%$s+v#$##'#'Sm$C#%$s+H#$#+SS$C#%$s,##$#(SS$C#%$s,'#$##'#+ST$C#%$s,,#$#(ST$C#%$s,0#$##'#0SUj##$#(SU$C#%$s,7#$#+Sn$C#%$s,;#$#(So$C#%$s,?#$#*S(/S(&D#C&D$s,Z;$#.S($C#$$s,S#$#+S($C#%$s,L#$#(S($C#%$s,P#$#)S($C#%$s,T#$#-S($C#$$s,D#$#,DFs,-'S($C#%$s,*#$##'##)##.##3##8##=##B#j#$D#$CF$Fs,T#$#*S6,D#s,>##0#&##;##@##s#%##s#*##s#/#j#$D#&DFC&DFs-/;$#-S6$C#$$s,e#$###1#s#)##s#.##s#3##s#8##,#j#$D#/S6&D#C&D$s->;$#$Fs-5#B###,#&#j#$D#.S6$C#$$s-<#$#%Fs-3#s#+###8#s#C##s#H##(##2#j#$D#+S#$C#%$s-=#$#(S#$C#%$s-A#$#,Ds#`s,r'S#$C#%$s,o#$##'##s#N##s#S##+##0##s#b#Bs-^s,x%Cs-_$Cs,z%Cs,zk##$#k##&#$Cs-dCs-es-#Gj##S7#j#%%#$Cs-%k##S7#k#%(#Bs-ks-g$Cs-h%Cs-hk##$#k##2#Cs-ps-lGj##S7#j#%0#$Cs-nk##S7#k#%3#Bs-vs-g$Cs-h%Cs-hk##$#k##=#Cs-{s-lGj##S7#j#%;#$Cs-nk##S7#k#%>#VSpCs.%VSVSq#m##s#&UG#USP$UM%USrS9VSsD#USWStUSW#VSXD#WSuD&#VSXD&WSvD$#VSw#SxUSOSG5SG$#5SG%#USySGVSzDGUS{DUS|DVS}DS9@DC9D$SY#:&IEEH#S-@Ds.E9D'SY#:)IEEH#S-[S~*IEEH&#UT#E=,IEEH$#$VT$-HVSVSZS[VT%FJ&SZ#S[m$%#WT&DCGXT'FJ$#l#&*)#l#'76#l#(:9#j#)D#&DGC&DGs.W;$#k##s$+#k#)D#/S8VF#S\l#**%#l#+s#0s#T#l#,s#2s#I#l#-s#4s#?#l#.s#<s#9#l#-s#Ds#@#l#/s#Is#F#l#,s#Qs#M#l#0s#Vs#S#l#+s#`s#[#m##s$j9Ds#(SNs#):s#+IEEH#S-ZT(s#,IEEHK>s#-IEEH$#=s#.IEEH#s#%%l#&#s#$>l#'s#2s#1#l#(s#7s#4#j#)D#j#1L##s$SG$CGk##$#k#)D#k#1L#.S8$#s.m6#$S6l#*+&#l#+s#Ms#q#l#,s#Os#f#l#-s#Qs#\#l#.s#Ys#V#l#-s#as#]#l#/s#fs#c#l#,s#ns#j#l#0s#ss#p#l#+s#}s#x#m##s%)@Ds/#Ds.}ED$#9Ds#ISN#:s#KIEEH#S->s#LIEEHB#=s#MIEEH#s#D$l#&#s#Cs#=l#'s#Qs#P#l#(s#Vs#S#j#)D#j#1L##Gs$S$Gs/+k##$#k#)D#k#1L#$CA6#BS6l#**%#l#+s#ks$3#l#,s#ms$(#l#-s#os#z#l#.s#ws#t#l#-s$#s#{#l#/s$(s$%#l#,s$0s$,#l#0s$5s$2#l#+s$?s$:#m##s%F4s%Hs%GA#+SH%#s/36#$Ol#*s#8s#3#l#+s#zs$B#l#,s#|s$7#l#-s#~s$-#l#.s$*s$'#l#-s$2s$.#l#/s$7s$4#l#,s$?s$;#l#0s$Ds$A#l#+s$Ns$I#m##s$aDs/BEDs#0#9Ds#uS]#:s#wIEEH#S->s#xIEEHs#N#=s#yIEEH#s#p$l#&#s#os#il#'s#}s#|#l#(s$&s$##j#)D#j#1L##Gs$v%Gs/Lk##$#k#)D#k#1L#$C@6#AOl#**%#l#+s$;s$_#l#,s$=s$T#l#-s$?s$J#l#.s$Gs$D#l#-s$Os$K#l#/s$Ts$Q#l#,s$\s$X#l#0s$as$^#l#+s$ks$f#m##s$}4s%#s$~@#(SH%#s/_6#$Nl#*s#ds#_#l#+s$Js$n#l#,s$Ls$c#l#-s$Ns$Y#l#.s$Vs$S#l#-s$^s$Z#l#/s$cs$`#l#,s$ks$g#l#0s$ps$m#l#+s$zs$u#m##s%-$C06#1Nl#*s#&A#l#+s$Ws${#l#,s$Ys$p#l#-s$[s$f#l#.s$cs$`#l#-s$ks$g#l#/s$ps$m#l#,s$xs$t#l#0s$}s$z#l#+s%+s%&#m##s%94s%;s%:0#)S8%#s/{6#$SEl#*s$$s#{#l#+s$fs%.#l#,s$hs%##l#-s$js$u#l#.s$rs$o#l#-s$zs$v#l#/s%#s$|#l#,s%+s%'#l#0s%0s%-#l#+s%:s%5#m##s&6$C06#1SEl#*s#Bs#=#l#+s$ss%;#l#,s$us%0#l#-s$ws%&#l#.s%#s$|#l#-s%+s%'#l#/s%0s%-#l#,s%8s%4#l#0s%=s%:#l#+s%Gs%B#m##s&B4s&Ds&C0#-S8$#s0'6#$S=l#*s$@s$;#l#+s%&s%J#l#,s%(s%?#l#-s%*s%5#l#.s%2s%/#l#-s%:s%6#l#/s%?s%<#l#,s%Gs%C#l#0s%Ls%I#l#+s%Vs%Q#m##s&N@Ds049Ds$|SN#:s$~IEEH#S->s%#IEEHs$U#=s%$IEEH#s$w$l#&#s$vs$pl#'s%(s%'#l#(s%-s%*#j#)D#j#1L##Gs&H$Gs0?k##$#k#)D#k#1L#$C?6#@S=l#**%#l#+s%Bs%f#l#,s%Ds%[#l#-s%Fs%Q#l#.s%Ns%K#l#-s%Vs%R#l#/s%[s%X#l#,s%cs%_#l#0s%hs%e#l#+s%rs%m#m##s&i4s&ks&j?#+S^$C#%$s0g*S^,D#s0<+T)%#s0k(S_$C#%$s0n*S_,D#s0C(S\%#s0r)S`$C#%$s0u*S`,D#s0J)T*%#s0y-Sa$C#$$s0h*Sa,D#s0Q-SH$#s0l'S8$C#%$s0P*S8,D#s0X'T+%#s0T$C$*Sb,D#s0]'Sb%#s0Y+Sc$C#%$s13*Sd,D#s0d+Sd%#s17(T,$C#%$s1:*Se,D#s0k(Se%#s1>/Sf&D#C&D$s1W*Sf,D#s0rj#2&S5j#2&S5ZT-('%$#Scj#3+#j#41#721/#SQj#55#j#6;#7<;9#Pj#7?#j#8s#$#7s#%s#&s###S0j#9s#'#j#:s#-#7s#.s#-s#+#S'j#;s#1#j#<s#7#7s#8s#7s#5#S3j#=s#;#j#>s#A#7s#Bs#As#?#S=j#?s#E#j#@s#K#7s#Ls#Ks#I#S?j#As#O#j#Bs#U#7s#Vs#Us#S#SEj#Cs'0#j#Ds'w#7s'xs'ws&|#SF'SH%#s106#$Pl#*s%hs%c#l#+s&Ns&r#l#,s&Ps&g#l#-s&Rs&]#l#.s&Zs&W#l#-s&bs&^#l#/s&gs&d#l#,s&os&k#l#0s&ts&q#l#+s&~s&y#m##s',Ds1?EDs%`#9Ds&IS]#:s&KIEEH#S->s&LIEEHs%~#=s&MIEEH#s&D$l#&#s&Cs&=l#'s&Qs&P#l#(s&Vs&S#j#)D#j#1L#%Fs1H#G#%Gs1Jk##$#k#)D#k#1L#$CA6#BPl#*+%#l#+s&ls'4#l#,s&ns')#l#-s&ps&{#l#.s&xs&u#l#-s'$s&|#l#/s')s'&#l#,s'1s'-#l#0s'6s'3#l#+s'@s';#m##s'I4s'Ks'JA#4s'Ns'Js#0#4s(9s'Js$.#4s(>s'Js$Z#4s'Rs'Js$w#4s'Ws'Js%8#4s(Ms'Js%e#4s(Rs'Js&F#)S#?Ds(Gs'_$#S*.S#?Ds(Us'm$#S./S#?Ds([s'x$#S0-S#?Ds(Is(,$#SA*S#?Ds(`s(;$#SI0S#m#$#j#Es(d#j#Fs(i#V#GFj##s(o#j##s({#2s(|s(xs(u#Fj#Ds)%#j#Gs)/#V#GFj##s)5#j##s)K#2s)Ls)Cs)@#Fj#Ds)Q#j#Hs)`#V#GFj##s)e#j##s*)#2s**s)xs)u#Fj#Ds*-#j#Is*@#V#GFj##s*E#j##s*k#2s*ls*[s*X#Fj#Ds*o#j#Js+*#V#GFj##s+/#j##s+[#2s+\s+Hs+E#Fj#Ds+_#j#Ks+z#V#GFj##s,##j##s,U#2s,Vs,?s,<#Fj#Ds,Y#j#Ls,x#V#GFj##s,}#j##s-]#2s-^s-@s-=#Fj#Ds-b#j#Ms-d#j#Ns-i#V#GFj##s-m#j##s-{#2s-|s-xs-s#Fj#Ds.##j#Os.+#V#GFj##s.1#j##s.E#2s.Fs.?s.:#Fj#Ds.K#j#Ps.X#V#GFj##s.^#j##s.|#2s.}s.qs.l#Fj#Ds/&#j#Qs/8#V#GFj##s/>#j##s/f#2s/gs/Vs/Q#Fj#Ds/l#j#Rs0'#V#GFj##s0-#j##s0_#2s0`s0Js0E#Fj#Ds0e#j#Ss1%#V#GFj##s1+#j##s1g#2s1hs1Ms1H#Fj#Ds1m#j#Ts22#V#GFj##s28#j##s3Q#2s3Rs2_s2Z#Fj#Ds3X#j#USg#j#VSg##"). Qed.

Definition http_fail (E' : ecv) : Prop :=
  ec_cat E' = AG_HTTP_CAT /\ ec_failed E' = true /\ ec_ok E' /\ 2 <= ec_flags E' /\ 1 <= ec_val E' <= 28.

(* [comment removed for export] *)
Definition lsub (L0 L1 : list Z) : Prop := forall e, e ∈ L0 -> e ∈ L1.
Definition lbn_own (L1 : list Z) (LBn : list block) : Prop := forall b, In b LBn -> blk_addr b ∈ L1 /\ 1 <= blk_size b.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AREALLOC_STACK : Z := 112 + AOPNEW_STACK.
Definition AHDRMETHOD_STACK : Z := 80 + AREALLOC_STACK.
Definition ONREQ_STACK : Z := 80 + AHDRMETHOD_STACK.
(* [comment removed for export] *)
Definition ISL_STACK : Z := 160 + ONREQ_STACK.
(* [comment removed for export] *)
Definition DOF_STACK : Z := 336 + (176 + AASSIGN_STACK + AFS_STACK).
(* [comment removed for export] *)
Definition IPF_STACK : Z := 304 + 8560.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition req_res (LB : list block) (mbs tbs : list byte) (verb ver : Z) (h' : hdrv) (LB' : list block) (m' : mem) : Prop :=
  exists (pt : bptr) (At : Z),
    hv_tp h' = At /\ hv_tl h' = Z.of_nat (length tbs) + 1 /\ hv_ver h' = ver /\ 0 <= hv_vb h' < 2^32
    /\ rblock_range At (Z.of_nat (length tbs) + 1)
    /\ rw_cells bsegs m' At [CB (S (length tbs)) (b8 32 :: tbs)]
    /\ addressable m' At (Z.of_nat (length tbs) + 1)                                  (* [comment removed for export] *)
    /\ ( (verb <> 0 /\ hv_mp h' = 0 /\ hv_ml h' = 0 /\ hv_vb h' = verb
          /\ LB' = (pt, At, Z.of_nat (length tbs) + 1) :: LB)
       \/ (verb = 0 /\ exists (pm : bptr) (Am : Z),
             hv_mp h' = Am /\ hv_ml h' = Z.of_nat (length mbs) /\ rblock_range Am (Z.of_nat (length mbs))
             /\ rw_cells bsegs m' Am [CB (length mbs) mbs]
             /\ addressable m' Am (Z.of_nat (length mbs))                                 (* [comment removed for export] *)
             /\ LB' = (pm, Am, Z.of_nat (length mbs)) :: (pt, At, Z.of_nat (length tbs) + 1) :: LB) ).

(* [comment removed for export] *)
Definition onreq_cost (mbs tbs : list byte) (verb : Z) : Z :=
  as_Cm H (Z.of_nat (length tbs) + 1) + (if verb =? 0 then as_Cm H (Z.of_nat (length mbs)) else 0).

(* [comment removed for export] *)
Definition onreq_X (P : Z) : list (Z * Z) := [(P + O_PR_HDR, P + O_PR_HDR + 40); (P + O_PR_USED, P + O_PR_USED + 1)]%Z.

Definition onreq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (P MP TP verb ver lo B shi : Z) (mbs tbs : list byte)
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (h' : hdrv)
                  (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' LB' m'
    /\ rw_cells bsegs m' (P + O_PR_USED) [C1 (b8 1)]
    /\ rw_cells bsegs m' (P + O_PR_HDR) (HdrCells h')
    /\ req_res LB mbs tbs verb ver h' LB' m'
    /\ bytes_at bsegs m' MP mbs /\ bytes_at bsegs m' TP tbs
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (onreq_X P ++ XS) m m'
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ AXStatics2 m'
    /\ as_AL H s' >= as_AL H s - onreq_cost mbs tbs verb.

Definition onreq_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (P verb MP TP ver lo B shi : Z) (mbs tbs : list byte) (h : hdrv) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_ON_REQUEST_IMPL) fc None m (seg_rom bsegs) ->
    a0 = wz P -> a1 = wz verb -> a2 = wz MP -> a3 = wz (Z.of_nat (length mbs)) -> a4 = wz TP -> a5 = wz (Z.of_nat (length tbs)) ->
    a6 = wz ver ->
    rw_cells bsegs m (P + O_PR_USED) [C1 (b8 0)] ->
    rw_cells bsegs m (P + O_PR_HDR) (HdrCells h) -> hdr_empty h ->
    bytes_at bsegs m MP mbs -> bytes_at bsegs m TP tbs ->
    1 <= Z.of_nat (length mbs) < 2^26 -> 1 <= Z.of_nat (length tbs) < 2^26 ->
    0 <= verb < 2^32 -> verb = verb_of (zbytes mbs) -> (ver = 10 \/ ver = 11) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + (Z.of_nat (length tbs) + 1) + Z.of_nat (length mbs) <= as_LIVE_MAX H ->
    Z.of_nat (length LB) + 2 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ONREQ_STACK ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
    AXStatics2 m ->
    (* [comment removed for export] *)
    0 <= P -> aobj LB LF P 256 -> P mod 8 = 0 -> accessible m P 256 ->
    aobj LB LF MP (Z.of_nat (length mbs)) -> accessible m MP (Z.of_nat (length mbs)) -> shvis m MP (MP + Z.of_nat (length mbs)) ->
    aobj LB LF TP (Z.of_nat (length tbs)) -> accessible m TP (Z.of_nat (length tbs)) -> shvis m TP (TP + Z.of_nat (length tbs)) ->
    (MP + Z.of_nat (length mbs) <= P \/ P + 256 <= MP) -> (TP + Z.of_nat (length tbs) <= P \/ P + 256 <= TP) ->
    as_RFS H LF m -> (length LF + 1 < AFS_MAXLIVE)%nat -> athr_cells m -> ACONST m ->
    stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
    onreq_cost mbs tbs verb <= as_AL H s ->
    as_SR H (onreq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF P MP TP verb ver lo B shi mbs tbs m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition isl_pure (sp : word) (P IN E lo shi : Z) (c : pcore) (p0 : Z) (bs : list byte) : Prop :=
  pcore_ok c /\ Z.of_nat (length bs) < 2^26
  /\ lo + ISL_STACK <= bv_unsigned sp /\ aceil <= lo
  /\ P mod 8 = 0 /\ E mod 8 = 0
  /\ bv_unsigned sp <= IN /\ IN + 8 <= shi /\ IN mod 8 = 0
  /\ (P + 256 <= E \/ E + 24 <= P)
  /\ (p0 + Z.of_nat (length bs) <= P \/ P + 256 <= p0) /\ (p0 + Z.of_nat (length bs) <= E \/ E + 24 <= p0)
  /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp + 64 <= shi.

(* [comment removed for export] *)
Definition isl_X (P IN E : Z) : list (Z * Z) :=
  [(P, P + 80); (P + O_PR_HDR, P + O_PR_HDR + 40); (P + O_PR_USED, P + O_PR_USED + 1); (IN, IN + 8); (E, E + 24);
   (AG_HTTP_CAT, AG_HTTP_CAT + 64)]%Z.

Definition isl_cost (bs : list byte) : Z := as_Cm H (Z.of_nat (length bs)) + as_Cm H (Z.of_nat (length bs)).

(* [comment removed for export] *)
Definition isl_outcome (c : pcore) (p0 : Z) (bs : list byte) (h : hdrv) (LB : list block) (g : bool) (m' : mem)
    (c' : pcore) (in' : Z) (E' : ecv) (u' : Z) (h' : hdrv) (LB' : list block) (g' : bool) : Prop :=
  (exists e loc, c' = c /\ in' = p0 /\ E' = EC_http_loc e loc
      /\ In e [HE_NEED_MORE; HE_BAD_METHOD; HE_BAD_TARGET; HE_BAD_VERSION] /\ Z.even loc = true /\ 4 <= loc /\ loc + 1 < 2^64
      /\ u' = 0 /\ h' = h /\ LB' = LB /\ g' = true)
  \/ (exists (k j ver f1 : Z) (mbs tbs : list byte),
      c' = mkPC (pc_blim_has c) (pc_blim c) (pc_len c) (pc_len0 c) (pc_skip c) (pc_hlim c) 2 f1
      /\ (f1 = pc_f c \/ f1 = Z.lor (pc_f c) 16) /\ 0 <= f1 < 2^14
      /\ in' = p0 + k + j + 12 /\ 1 <= k /\ 1 <= j /\ p0 + k + j + 12 <= p0 + Z.of_nat (length bs)
      /\ E' = EC_clear /\ u' = 1 /\ (ver = 10 \/ ver = 11) /\ g' = g
      /\ bytes_at bsegs m' p0 mbs /\ bytes_at bsegs m' (p0 + k + 1) tbs /\ Z.of_nat (length mbs) = k /\ Z.of_nat (length tbs) = j
      /\ req_res LB mbs tbs (verb_of (zbytes mbs)) ver h' LB' m').

Definition isl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (P IN E lo B shi : Z) (c : pcore) (pad7 pad2 : list byte) (p0 : Z) (bs : list byte)
    (h : hdrv) (g : bool) (m : mem) (mo : Model) : config -> Prop :=
  fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H)
                   (c' : pcore) (in' : Z) (E' : ecv) (u' : Z) (h' : hdrv) (LB' : list block) (g' : bool) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' LB' m'
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (isl_X P IN E ++ XS) m m'
    /\ rw_cells bsegs m' P (ParserCoreCells c' pad7 pad2)
    /\ rw_cells bsegs m' IN [C8 (wz in')]
    /\ rw_cells bsegs m' E (ErrCodeCells E')
    /\ rw_cells bsegs m' (P + O_PR_USED) [C1 (b8 u')]
    /\ rw_cells bsegs m' (P + O_PR_HDR) (HdrCells h')
    /\ bytes_at bsegs m' p0 bs
    /\ AHttpCat m' g' /\ AXStatics2 m'
    /\ isl_outcome c p0 bs h LB g m' c' in' E' u' h' LB' g'
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - as_Cm H (in' - p0).      (* [comment removed for export] *)

Definition isl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (P IN E lo B shi : Z) (c : pcore) (pad7 pad2 : list byte)
         (p0 : Z) (bs : list byte) (h : hdrv) (g : bool) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_BP_INNER_PARSE_START_LINE) fc None m (seg_rom bsegs) ->
    a0 = wz P -> a1 = wz IN -> a2 = wz (p0 + Z.of_nat (length bs)) -> a3 = wz E ->
    rw_cells bsegs m P (ParserCoreCells c pad7 pad2) ->
    rw_cells bsegs m IN [C8 (wz p0)] ->
    rw_cells bsegs m E (ErrCodeCells EC_clear) ->
    rw_cells bsegs m (P + O_PR_USED) [C1 (b8 0)] ->
    rw_cells bsegs m (P + O_PR_HDR) (HdrCells h) -> hdr_empty h ->
    bytes_at bsegs m p0 bs ->
    AHttpCat m g -> AXStatics2 m ->
    isl_pure sp P IN E lo shi c p0 bs ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + Z.of_nat (length bs) <= as_LIVE_MAX H -> Z.of_nat (length LB) + 2 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    0 <= P -> aobj LB LF P 256 -> accessible m P 256 ->
    aobj LB LF E 24 -> accessible m E 24 -> shvis m E (E + 24) ->
    aobj LB LF p0 (Z.of_nat (length bs)) -> accessible m p0 (Z.of_nat (length bs)) -> shvis m p0 (p0 + Z.of_nat (length bs)) ->
    as_RFS H LF m -> (length LF + 1 < AFS_MAXLIVE)%nat -> athr_cells m -> ACONST m ->
    stack0 m lo shi ->
    isl_cost bs <= as_AL H s ->
    as_SR H (isl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF P IN E lo B shi c pad7 pad2 p0 bs h g m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dof_W (lo : Z) (sp : word) (P E : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (P, P + 80); (E, E + 24); (AG_HTTP_CAT, AG_HTTP_CAT + 64)]%Z.

Definition dof_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LF : list fframe) (P E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (vp : Z) (vbs : list byte) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' c' E' g' (XS : list (Z * Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ Forall (fs_scratch H LF) XS
    /\ munch (dof_W lo sp P E ++ (as_FSB H, as_FSB H + AFS_FLAGS) :: XS) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' P (ParserCoreCells c' pad7 pad2) /\ dof_core c c'
    /\ rw_cells bsegs m' E (ErrCodeCells E') /\ dof_out E'
    /\ bytes_at bsegs m' vp vbs
    /\ AHttpCat m' g' /\ AXStatics2 m'
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

(* [comment removed for export] *)
Definition dof_pure (sp : word) (P E lo shi : Z) (c : pcore) (fld vp : Z) (vbs : list byte) : Prop :=
  pcore_ok c /\ 0 <= fld < 2^31 /\ lo + DOF_STACK <= bv_unsigned sp /\ aceil <= lo
  /\ aapp P 80 /\ P mod 8 = 0 /\ aapp E 24 /\ E mod 8 = 0 /\ (P + 80 <= E \/ E + 24 <= P)
  /\ aapp vp (Z.of_nat (length vbs)) /\ (vp + Z.of_nat (length vbs) <= P \/ P + 80 <= vp)
  /\ (vp + Z.of_nat (length vbs) <= E \/ E + 24 <= vp)
  /\ 0 <= vp /\ vp + Z.of_nat (length vbs) < 2^47
  /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp + 64 <= shi
  /\ Z.of_nat (length vbs) < 2^32.

Definition dof_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (LF : list fframe) (P E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (fld vp : Z) (vbs : list byte)
    (E0 : ecv) (g : bool),
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) ->
  rw_cells bsegs m E (ErrCodeCells E0) -> ec_ok E0 ->
  bytes_at bsegs m vp vbs ->
  AHttpCat m g -> AXStatics2 m ->
  stk bsegs m lo (bv_unsigned sp) ->
  dof_pure sp P E lo shi c fld vp vbs ->
  mem_inv bsegs m -> bv_unsigned ra mod 2 = 0 ->
  (* [comment removed for export] *)
  tp = Z_to_bv 64 ATP -> athr_cells m -> ACONST m -> stack0 m lo shi ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  accessible m P 80 -> accessible m E 24 -> shvis m E (E + 24) ->
  accessible m vp (Z.of_nat (length vbs)) ->
  fsobj H LF P 80 -> fsobj H LF E 24 -> fsobj H LF vp (Z.of_nat (length vbs)) ->
  evt bsegs (dof_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF P E lo shi c pad7 pad2 vp vbs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz fld) (wz vp) (wz (Z.of_nat (length vbs))) (wz E) a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_BP_DO_FIELD) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ipf_pure (sp : word) (P IN E lo shi : Z) (c : pcore) (p0 : Z) (bs : list byte) : Prop :=
  pcore_ok c /\ Z.of_nat (length bs) <= 8194
  /\ lo + IPF_STACK <= bv_unsigned sp /\ aceil <= lo
  /\ P mod 8 = 0 /\ E mod 8 = 0
  /\ bv_unsigned sp <= IN /\ IN + 8 <= shi /\ IN mod 8 = 0
  /\ (P + 256 <= E \/ E + 24 <= P)
  /\ (p0 + Z.of_nat (length bs) <= P \/ P + 256 <= p0) /\ (p0 + Z.of_nat (length bs) <= E \/ E + 24 <= p0)
  /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp + 64 <= shi.

(* [comment removed for export] *)
Definition ipf_X (P IN E : Z) (L0 : list Z) : list (Z * Z) :=
  (P, P + 128) :: (IN, IN + 8) :: (E, E + 24) :: (AG_HTTP_CAT, AG_HTTP_CAT + 64) :: (AG_FIELD_TABLE, AG_FIELD_TABLE + 3456)
  :: elemsW L0.

(* [comment removed for export] *)
Definition new_elems_off (LB0 : list block) (SP : Z) (L0 L1 : list Z) : Prop :=
  forall e, e ∈ L1 -> e ∈ L0 \/ (forall a k, aclient_range H LB0 SP a k -> 0 < k -> a + k <= e \/ e + 48 <= a).

(* [comment removed for export] *)
Definition ipf_cost (n : Z) : Z := as_Cm H (17 * n).

Definition ipf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (P IN E lo B shi : Z) (c : pcore) (pad7 pad2 : list byte) (p0 : Z) (bs : list byte)
    (L0 : list Z) (mb : byte) (m : mem) (mo : Model) : config -> Prop :=
  fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H)
                   (c' : pcore) (q' : Z) (E' : ecv) (LBn : list block) S' L' ns' ls' em' (g' : bool) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' (LBn ++ LB) m'
    /\ AFieldsC m' (P + 80) S' L' ns' ls' em' /\ AFieldsOwn (LBn ++ LB) em' /\ new_elems_off LB (bv_unsigned sp) L0 L'
    /\ lsub L0 L' /\ lbn_own L' LBn
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (ipf_X P IN E L0 ++ XS) m m'
    /\ rw_cells bsegs m' P (ParserCoreCells c' pad7 pad2) /\ dof_core c c'
    /\ rw_cells bsegs m' IN [C8 (wz q')] /\ p0 <= q' <= p0 + Z.of_nat (length bs)
    /\ rw_cells bsegs m' E (ErrCodeCells E') /\ (E' = EC_clear \/ http_fail E') /\ (E' = EC_clear -> p0 + 2 <= q')
    /\ rw_cells bsegs m' (P + O_PR_MERGE) [C1 mb]
    /\ bytes_at bsegs m' p0 bs /\ APfTab m' /\ (AFieldTabZero m' \/ FT m') /\ FTInit m' /\ AHttpCat m' g' /\ AXStatics2 m'
    /\ lb_bytes LBn <= 17 * (q' - p0) /\ 4 * Z.of_nat (length LBn) <= q' - p0
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - ipf_cost (q' - p0).

Definition ipf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (P IN E lo B shi : Z) (c : pcore) (pad7 pad2 : list byte)
         (p0 : Z) (bs : list byte) (g : bool) (errv : word) (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt) (mb : byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_BP_INNER_PARSE_FIELDS) fc None m (seg_rom bsegs) ->
    a0 = wz P -> a1 = wz IN -> a2 = wz (p0 + Z.of_nat (length bs)) -> a3 = wz E ->
    rw_cells bsegs m P (ParserCoreCells c pad7 pad2) ->
    rw_cells bsegs m IN [C8 (wz p0)] ->
    rw_cells bsegs m E (ErrCodeCells EC_clear) ->
    rw_cells bsegs m (P + O_PR_MERGE) [C1 mb] ->
    AFieldsC m (P + 80) S L ns ls em -> AFieldsOwn LB em ->
    (forall e, e ∈ L -> e + 48 <= p0 \/ p0 + Z.of_nat (length bs) <= e) ->
    bytes_at bsegs m p0 bs ->
    APfTab m -> (AFieldTabZero m \/ FT m) -> FTInit m -> AHttpCat m g -> AXStatics2 m ->
    ipf_pure sp P IN E lo shi c p0 bs ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + 17 * Z.of_nat (length bs) <= as_LIVE_MAX H -> Z.of_nat (length LB) + Z.of_nat (length bs) / 4 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk bsegs m lo (bv_unsigned sp) ->
    rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    0 <= P -> aobj LB LF P 256 -> accessible m P 256 ->
    aobj LB LF E 24 -> accessible m E 24 -> shvis m E (E + 24) ->
    (forall e d, em !! e = Some d -> E + 24 <= e \/ e + esize d <= E) ->
    aobj LB LF p0 (Z.of_nat (length bs)) -> accessible m p0 (Z.of_nat (length bs)) -> shvis m p0 (p0 + Z.of_nat (length bs)) ->
    as_RFS H LF m -> (length LF + 2 < AFS_MAXLIVE)%nat -> (length LF < AFS7_MAXLIVE)%nat ->     (* [comment removed for export] *)
    athr_cells m -> ACONST m ->
    stack0 m lo shi ->
    ipf_cost (Z.of_nat (length bs)) <= as_AL H s ->
    bv_unsigned mb <= 1 ->     (* [comment removed for export] *)
    as_SR H (ipf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF P IN E lo B shi c pad7 pad2 p0 bs L mb m mo)
      (mkCfg msF mo).

End HCW.
