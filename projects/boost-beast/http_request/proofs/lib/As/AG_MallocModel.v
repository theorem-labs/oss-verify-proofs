(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition same_but_shadow (a b : astate) : Prop :=
  as_space_beg a = as_space_beg b /\ as_ptr_array a = as_ptr_array b /\ as_regions a = as_regions b /\ as_cache_inited a = as_cache_inited b
  /\ as_cache a = as_cache b /\ as_n_reserved a = as_n_reserved b /\ as_sec a = as_sec b /\ as_chunks a = as_chunks b /\ as_tq a = as_tq b
  /\ as_gq a = as_gq b /\ as_internal_init a = as_internal_init b /\ as_maps a = as_maps b /\ as_env a = as_env b
  /\ as_qmax a = as_qmax b /\ as_qmin a = as_qmin b /\ as_qcache a = as_qcache b.

Lemma sbs_refl : forall a, same_but_shadow a a. Proof. intros; repeat split; reflexivity. Qed.
Lemma sbs_trans : forall a b c, same_but_shadow a b -> same_but_shadow b c -> same_but_shadow a c.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.astate); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AG_MallocModel.same_but_shadow); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_space_beg); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_ptr_array); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.region); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_regions); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_cache_inited); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.pclass); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_cache); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_n_reserved); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.schunk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_sec); constr:(@Stdlib.FSets.FMapPositive.PositiveMap.t); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.chunk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_chunks); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.qcache); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_tq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_gq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_internal_init); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.mapping); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_maps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_env); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qmax); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qmin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qcache); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_trans)|] [|@H31; @H28; @H30; @H27; @H29; @H26; @H25; @H24; @H23; @H22; @H21; @H20; @H19; @H18; @H17; @H16; @H15; @H14; @H13; @H12; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H0; @H2; @H1; @H; @c; @b; @a|] "#?I#d$)#k#|#r#%#'#&#(#)#+#*#,#-#/#1#3#5#7#9#;#=#?#A#C#E#G#I#K#M#O#Q#S#U#W#Y#[#]#_#a#c#b#.#0#2#4#6#8#:#<#>#@#B#D#F#H#J#L#N#P#R#T#V#X#Z#\#$#^#g#h#`#p#t#w#y#z$$###j#m$($)$'$&$%$##~#}#{#x#v#u#s#q#n#l#i$+$*#o9#o&#p%#q$#r$#s$#t$#u$#v$#w$#x$#y$#z$#{$#|$#}$#~$$#$$$$$%($&)$''$($VSVFSS4G4H#C$#3G3H#C$#8SX2G2H#%$#1G1H#E$#8SY0G0H#%$#/G/H#C$#8SZ.G.H#%$#US[S\-G-H#%$#,G,H#D$#+G+H#D$#*G*H#E$#8S])G)H#%$#8C(G(H#%$#'G'H#C$#%G%H#C$#&G&H#C$#$&#$*#$.#$3#$8#$<#$@#$s#$#$s#)#$s#.#$s#2#$s#7#$s#;#$s#@#4F#Cs#G#3F#Cs#F#2F#s#Es#D#1F#Es#C#0F#s#Bs#A#/F#Cs#@#.F#s#?s#>#-F#s#=s#<#,F#Ds#;#+F#Ds#:#*F#Es#9#)F#s#8s#7#(F#s#6s#5#'F#Cs#4#%F#Cs#3#&F#Cs#2#$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/#3I#C#s#s2I#s#r#s#q1I#E#s#p0I#s#o#s#n/I#C#s#m.I#s#l#s#k-I#s#j#s#i,I#D#s#h+I#D#s#g*I#E#s#f)I#s#e#s#d(I#s#c#s#b'I#C#s#a%I#C#s#`&I#C#s#_$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#4I#C#s$F4J#C#s$H3J#C#s$G2J#s$F#s$E1J#E#s$D0J#s$C#s$B/J#C#s$A.J#s$@#s$?-J#s$>#s$=,J#D#s$<+J#D#s$;*J#E#s$:)J#s$9#s$8(J#s$7#s$6'J#C#s$5%J#C#s$4&J#C#s$3$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##Cs#/s#_#s$qs#.s#^#Es#-s#]#s$ls#,s#\#Cs#+s#[#s$gs#*s#Z#s$ds#)s#Y#Ds#(s#X#Ds#'s#W#Es#&s#V#s$[s#%s#U#s$Xs#$s#T#Cs##s#S#CBs#R#CAs#Q$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#$>#3K3L#C$#2K2L#s%6$#1K1L#E$#0K0L#s%5$#/K/L#C$#.K.L#s%4$#-K-L#s%3$#,K,L#D$#+K+L#D$#*K*L#E$#)K)L#s%2$#(K(L#s%1$#'K'L#C$#%K%L#C$#&K&L#C$#$&#$*#$.#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#$s#2#$s#6#4K#C#s$-#Cs#>s$,#s%ns#<s$+#Es#:s$*#s%is#8s$)#Cs#6s$(#s%ds#4s$'#s%as#2s$&#Ds#0s$%#Ds#.s$$#Es#,s$##s%Xs#*s#~#s%Us#(s#}#Cs#&s#|#Cs#$s#{#CBs#z$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#$>#$@#2M#s&0#s#Z1M#E#s#Y0M#s&-#s#X/M#C#s#W.M#s&*#s#V-M#s&(#s#U,M#D#s#T+M#D#s#S*M#E#s#R)M#s&##s#Q(M#s%}#s#P'M#C#s#O%M#C#s#N&M#C#s#M$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#3M#C#s$*4N#C#s#N3N#C#s$.2N#s&_#s$-1N#E#s$,0N#s&\#s$+/N#C#s$*.N#s&Y#s$)-N#s&W#s$(,N#D#s$'+N#D#s$&*N#E#s$%)N#s&R#s$$(N#s&P#s$#'N#C#s#~%N#C#s#}&N#C#s#|$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##s'-s#-s#\#Es#,s#[#s'(s#+s#Z#Cs#*s#Y#s'#s#)s#X#s&|s#(s#W#Ds#'s#V#Ds#&s#U#Es#%s#T#s&ss#$s#S#s&ps##s#R#CBs#Q#CAs#P#C@s#O$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#2O2S;#s'J$#1O1S;#E$#0O0S;#s'I$#/O/S;#C$#.O.S;#s'H$#-O-S;#s'G$#,O,S;#D$#+O+S;#D$#*O*S;#E$#)O)S;#s'F$#(O(S;#s'E$#'O'S;#C$#%O%S;#C$#&O&S;#C$#$&#$*#$.#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#$s#2#4O#C#s$'3O#C#s$'#s(&s#<s$&#Es#:s$%#s'}s#8s$$#Cs#6s$##s'xs#4s#~#s'us#2s#}#Ds#0s#|#Ds#.s#{#Es#,s#z#s'ls#*s#y#s'is#(s#x#Cs#&s#w#Cs#$s#v#CBs#u$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#$>#$A#1S<#E#s#W0S<#s(?#s#V/S<#C#s#U.S<#s(<#s#T-S<#s(:#s#S,S<#D#s#R+S<#D#s#Q*S<#E#s#P)S<#s(5#s#O(S<#s(3#s#N'S<#C#s#M%S<#C#s#L&S<#C#s#K$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#2S<#s(j#s$$4P#C#s#L3P#C#s#L2P#s(p#s$*1P#E#s$)0P#s(m#s$(/P#C#s$'.P#s(j#s$&-P#s(h#s$%,P#D#s$$+P#D#s$#*P#E#s#~)P#s(c#s#}(P#s(a#s#|'P#C#s#{%P#C#s#z&P#C#s#y$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##Es#+s#Y#s)8s#*s#X#Cs#)s#W#s)3s#(s#V#s)0s#'s#U#Ds#&s#T#Ds#%s#S#Es#$s#R#s)'s##s#Q#s)$Bs#P#CAs#O#C@s#N#C?s#M$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#1Q1S=#E$#0Q0S=#s)U$#/Q/S=#C$#.Q.S=#s)T$#-Q-S=#s)S$#,Q,S=#D$#+Q+S=#D$#*Q*S=#E$#)Q)S=#s)R$#(Q(S=#s)Q$#'Q'S=#C$#%Q%S=#C$#&Q&S=#C$#$&#$*#$.#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#4Q#C#s#}3Q#C#s#}2Q#s*2#s#}#Es#:s#|#s*-s#8s#{#Cs#6s#z#s*(s#4s#y#s*%s#2s#x#Ds#0s#w#Ds#.s#v#Es#,s#u#s)xs#*s#t#s)us#(s#s#Cs#&s#r#Cs#$s#q#CBs#p$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#$?#$B#0S>#s*I#s#T/S>#C#s#S.S>#s*F#s#R-S>#s*D#s#Q,S>#D#s#P+S>#D#s#O*S>#E#s#N)S>#s*?#s#M(S>#s*=#s#L'S>#C#s#K%S>#C#s#J&S>#C#s#I$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###1S>#E#s#z4R#C#s#J3R#C#s#J2R#s*y#s#J1R#E#s$&0R#s*v#s$%/R#C#s$$.R#s*s#s$#-R#s*q#s#~,R#D#s#}+R#D#s#|*R#E#s#{)R#s*l#s#z(R#s*j#s#y'R#C#s#x%R#C#s#w&R#C#s#v$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##s+@s#)s#V#Cs#(s#U#s+;s#'s#T#s+8s#&s#S#Ds#%s#R#Ds#$s#Q#Es##s#P#s+/Bs#O#s+,As#N#C@s#M#C?s#L#C>s#K$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#0S#0S?#s+Y$#/S#/S?#C$#.S#.S?#s+X$#-S#-S?#s+W$#,S#,S?#D$#+S#+S?#D$#*S#*S?#E$#)S#)S?#s+V$#(S#(S?#s+U$#'S#'S?#C$#%S#%S?#C$#&S#&S?#C$#$&#$*#$.#$2#$6#$:#$>#$B#$s#&#$s#*#4S##C#s#w3S##C#s#w2S##s,5#s#w1S##E#s#w#s,1s#8s#v#Cs#6s#u#s,,s#4s#t#s,)s#2s#s#Ds#0s#r#Ds#.s#q#Es#,s#p#s+|s#*s#o#s+ys#(s#n#Cs#&s#m#Cs#$s#l#CBs#k$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$=#$@#$s###/S@#C#s#Q.S@#s,H#s#P-S@#s,F#s#O,S@#D#s#N+S@#D#s#M*S@#E#s#L)S@#s,A#s#K(S@#s,?#s#J'S@#C#s#I%S@#C#s#H&S@#C#s#G$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#0S@#s,m#s#t4S$#C#s#H3S$#C#s#H2S$#s,z#s#H1S$#E#s#H0S$#s,w#s#~/S$#C#s#}.S$#s,t#s#|-S$#s,r#s#{,S$#D#s#z+S$#D#s#y*S$#E#s#x)S$#s,m#s#w(S$#s,k#s#v'S$#C#s#u%S$#C#s#t&S$#C#s#s$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##Cs#'s#S#s-;s#&s#R#s-8s#%s#Q#Ds#$s#P#Ds##s#O#EBs#N#s-/As#M#s-,@s#L#C?s#K#C>s#J#C=s#I$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#/S%/SA#C$#.S%.SA#s-T$#-S%-SA#s-S$#,S%,SA#D$#+S%+SA#D$#*S%*SA#E$#)S%)SA#s-R$#(S%(SA#s-Q$#'S%'SA#C$#%S%%SA#C$#&S%&SA#C$#$&#$*#$.#$2#$6#$:#$>#$B#$s#&#4S%#C#s#q3S%#C#s#q2S%#s.0#s#q1S%#E#s#q0S%#s.-#s#q#Cs#6s#p#s.(s#4s#o#s.%s#2s#n#Ds#0s#m#Ds#.s#l#Es#,s#k#s-xs#*s#j#s-us#(s#i#Cs#&s#h#Cs#$s#g#CBs#f$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$;#$>#$A#$s#$#.SB#s.B#s#N-SB#s.@#s#M,SB#D#s#L+SB#D#s#K*SB#E#s#J)SB#s.;#s#I(SB#s.9#s#H'SB#C#s#G%SB#C#s#F&SB#C#s#E$%#$(#$+#$.#$1#$4#$7#$:#$=#/SB#C#s#n4S&#C#s#F3S&#C#s#F2S&#s.s#s#F1S&#E#s#F0S&#s.p#s#F/S&#C#s#z.S&#s.m#s#y-S&#s.k#s#x,S&#D#s#w+S&#D#s#v*S&#E#s#u)S&#s.f#s#t(S&#s.d#s#s'S&#C#s#r%S&#C#s#q&S&#C#s#p$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##s/3s#%s#P#s/0s#$s#O#Ds##s#N#DBs#M#EAs#L#s/'@s#K#s/$?s#J#C>s#I#C=s#H#C<s#G$$#$&#$(#$*#$,#$.#$0#$2#$4#.S'.SC#s/H$#-S'-SC#s/G$#,S',SC#D$#+S'+SC#D$#*S'*SC#E$#)S')SC#s/F$#(S'(SC#s/E$#'S''SC#C$#%S'%SC#C$#&S'&SC#C$#$&#$*#$.#$2#$6#$:#$>#$B#4S'#C#s#k3S'#C#s#k2S'#s0##s#k1S'#E#s#k0S'#s/|#s#k/S'#C#s#k#s/xs#4s#j#s/us#2s#i#Ds#0s#h#Ds#.s#g#Es#,s#f#s/ls#*s#e#s/is#(s#d#Cs#&s#c#Cs#$s#b#CBs#a$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$9#$<#$?#$B#$s#%#-SD#s02#s#K,SD#D#s#J+SD#D#s#I*SD#E#s#H)SD#s0-#s#G(SD#s0+#s#F'SD#C#s#E%SD#C#s#D&SD#C#s#C$%#$(#$+#$.#$1#$4#$7#$:#.SD#s0P#s#h4S(#C#s#D3S(#C#s#D2S(#s0d#s#D1S(#E#s#D0S(#s0a#s#D/S(#C#s#D.S(#s0^#s#v-S(#s0\#s#u,S(#D#s#t+S(#D#s#s*S(#E#s#r)S(#s0W#s#q(S(#s0U#s#p'S(#C#s#o%S(#C#s#n&S(#C#s#m$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##s0|s##s#M#DBs#L#DAs#K#E@s#J#s0s?s#I#s0p>s#H#C=s#G#C<s#F#C;s#E$$#$&#$(#$*#$,#$.#$0#$2#-S)-SE#s13$#,S),SE#D$#+S)+SE#D$#*S)*SE#E$#)S))SE#s12$#(S)(SE#s11$#'S)'SE#C$#%S)%SE#C$#&S)&SE#C$#$&#$*#$.#$2#$6#$:#$>#4S)#C#s#e3S)#C#s#e2S)#s1j#s#e1S)#E#s#e0S)#s1g#s#e/S)#C#s#e.S)#s1d#s#e#s1as#2s#d#Ds#0s#c#Ds#.s#b#Es#,s#a#s1Xs#*s#`#s1Us#(s#_#Cs#&s#^#Cs#$s#]#CBs#\$$#$&#$(#$*#$,#$.#$0#$2#$4#$7#$:#$=#$@#$s###$s#&#,SF#D#s#H+SF#D#s#G*SF#E#s#F)SF#s1s#s#E(SF#s1q#s#D'SF#C#s#C%SF#C#s#B&SF#C#s#A$%#$(#$+#$.#$1#$4#$7#-SF#s25#s#b4S*#C#s#B3S*#C#s#B2S*#s2M#s#B1S*#E#s#B0S*#s2J#s#B/S*#C#s#B.S*#s2G#s#B-S*#s2E#s#r,S*#D#s#q+S*#D#s#p*S*#E#s#o)S*#s2@#s#n(S*#s2>#s#m'S*#C#s#l%S*#C#s#k&S*#C#s#j$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##DAs#J#D@s#I#E?s#H#s2[>s#G#s2X=s#F#C<s#E#C;s#D#C:s#C$$#$&#$(#$*#$,#$.#$0#,S+,SG#D$#+S++SG#D$#*S+*SG#E$#)S+)SG#s2r$#(S+(SG#s2q$#'S+'SG#C$#%S+%SG#C$#&S+&SG#C$#$&#$*#$.#$2#$6#$:#4S+#C#s#_3S+#C#s#_2S+#s3M#s#_1S+#E#s#_0S+#s3J#s#_/S+#C#s#_.S+#s3G#s#_-S+#s3E#s#_#Ds#0s#^#Ds#.s#]#Es#,s#\#s3<s#*s#[#s39s#(s#Z#Cs#&s#Y#Cs#$s#X#CBs#W$$#$&#$(#$*#$,#$.#$0#$2#$5#$8#$;#$>#$A#$s#$#$s#'#+SH#D#s#E*SH#E#s#D)SH#s3U#s#C(SH#s3S#s#B'SH#C#s#A%SH#C#s#@&SH#C#s#?$%#$(#$+#$.#$1#$4#,SH#D#s#\4S,#C#s#@3S,#C#s#@2S,#s4.#s#@1S,#E#s#@0S,#s4+#s#@/S,#C#s#@.S,#s4(#s#@-S,#s4&#s#@,S,#D#s#n+S,#D#s#m*S,#E#s#l)S,#s3}#s#k(S,#s3{#s#j'S,#C#s#i%S,#C#s#h&S,#C#s#g$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##D?s#G#E>s#F#s4;=s#E#s48<s#D#C;s#C#C:s#B#C9s#A$$#$&#$(#$*#$,#$.#+S-+SI#D$#*S-*SI#E$#)S-)SI#s4N$#(S-(SI#s4M$#'S-'SI#C$#%S-%SI#C$#&S-&SI#C$#$&#$*#$.#$2#$6#4S-#C#s#Y3S-#C#s#Y2S-#s5(#s#Y1S-#E#s#Y0S-#s5%#s#Y/S-#C#s#Y.S-#s4~#s#Y-S-#s4|#s#Y,S-#D#s#Y#Ds#.s#X#Es#,s#W#s4ts#*s#V#s4qs#(s#U#Cs#&s#T#Cs#$s#S#CBs#R$$#$&#$(#$*#$,#$.#$0#$3#$6#$9#$<#$?#$B#$s#%#$s#(#*SJ#E#s#B)SJ#s5/#s#A(SJ#s5-#s#@'SJ#C#s#?%SJ#C#s#>&SJ#C#s#=$%#$(#$+#$.#$1#+SJ#D#s#V4S.#C#s#>3S.#C#s#>2S.#s5c#s#>1S.#E#s#>0S.#s5`#s#>/S.#C#s#>.S.#s5]#s#>-S.#s5[#s#>,S.#D#s#>+S.#D#s#j*S.#E#s#i)S.#s5V#s#h(S.#s5T#s#g'S.#C#s#f%S.#C#s#e&S.#C#s#d$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##E=s#D#s5o<s#C#s5l;s#B#C:s#A#C9s#@#C8s#?$$#$&#$(#$*#$,#*S/*SK#E$#)S/)SK#s5~$#(S/(SK#s5}$#'S/'SK#C$#%S/%SK#C$#&S/&SK#C$#$&#$*#$.#$2#4S/#C#s#S3S/#C#s#S2S/#s6W#s#S1S/#E#s#S0S/#s6T#s#S/S/#C#s#S.S/#s6Q#s#S-S/#s6O#s#S,S/#D#s#S+S/#D#s#S#Es#,s#R#s6Hs#*s#Q#s6Es#(s#P#Cs#&s#O#Cs#$s#N#CBs#M$$#$&#$(#$*#$,#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#)SL#s6]#s#?(SL#s6[#s#>'SL#C#s#=%SL#C#s#<&SL#C#s#;$%#$(#$+#$.#*SL#E#s#P4S0#C#s#<3S0#C#s#<2S0#s74#s#<1S0#E#s#<0S0#s71#s#</S0#C#s#<.S0#s7.#s#<-S0#s7,#s#<,S0#D#s#<+S0#D#s#<*S0#E#s#f)S0#s7'#s#e(S0#s7%#s#d'S0#C#s#c%S0#C#s#b&S0#C#s#a$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##s7?;s#A#s7<:s#@#C9s#?#C8s#>#C7s#=$$#$&#$(#$*#)S1)SM#s7J$#(S1(SM#s7I$#'S1'SM#C$#%S1%SM#C$#&S1&SM#C$#$&#$*#$.#4S1#C#s#M3S1#C#s#M2S1#s7~#s#M1S1#E#s#M0S1#s7{#s#M/S1#C#s#M.S1#s7x#s#M-S1#s7v#s#M,S1#D#s#M+S1#D#s#M*S1#E#s#M#s7ps#*s#L#s7ms#(s#K#Cs#&s#J#Cs#$s#I#CBs#H$$#$&#$(#$*#$,#$/#$2#$5#$8#$;#$>#$A#$s#$#$s#'#$s#*#(SN#s8%#s#<'SN#C#s#;%SN#C#s#:&SN#C#s#9$%#$(#$+#)SN#s84#s#J4S2#C#s#:3S2#C#s#:2S2#s8Y#s#:1S2#E#s#:0S2#s8V#s#:/S2#C#s#:.S2#s8S#s#:-S2#s8Q#s#:,S2#D#s#:+S2#D#s#:*S2#E#s#:)S2#s8L#s#b(S2#s8J#s#a'S2#C#s#`%S2#C#s#_&S2#C#s#^$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##s8`9s#>#C8s#=#C7s#<#C6s#;$$#$&#$(#(S3(SO#s8i$#'S3'SO#C$#%S3%SO#C$#&S3&SO#C$#$&#$*#4S3#C#s#G3S3#C#s#G2S3#s9A#s#G1S3#E#s#G0S3#s9>#s#G/S3#C#s#G.S3#s9;#s#G-S3#s99#s#G,S3#D#s#G+S3#D#s#G*S3#E#s#G)S3#s94#s#G#s91s#(s#F#Cs#&s#E#Cs#$s#D#CBs#C$$#$&#$(#$*#$-#$0#$3#$6#$9#$<#$?#$B#$s#%#$s#(#$s#+#'SP#C#s#9%SP#C#s#8&SP#C#s#7$%#$(#(SP#s9M#s#D4S4#C#s#83S4#C#s#82S4#s9v#s#81S4#E#s#80S4#s9s#s#8/S4#C#s#8.S4#s9p#s#8-S4#s9n#s#8,S4#D#s#8+S4#D#s#8*S4#E#s#8)S4#s9i#s#8(S4#s9g#s#^'S4#C#s#]%S4#C#s#\&S4#C#s#[$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##C7s#;#C6s#:#C5s#9$$#$&#'S5'SQ#C$#%S5%SQ#C$#&S5&SQ#C$#$&#4S5#C#s#A3S5#C#s#A2S5#s:X#s#A1S5#E#s#A0S5#s:U#s#A/S5#C#s#A.S5#s:R#s#A-S5#s:P#s#A,S5#D#s#A+S5#D#s#A*S5#E#s#A)S5#s:K#s#A(S5#s:I#s#A#Cs#&s#@#Cs#$s#?#CBs#>$$#$&#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#%SR#C#s#6&SR#C#s#5$%#'SR#C#s#>4S6#C#s#63S6#C#s#62S6#s;/#s#61S6#E#s#60S6#s;,#s#6/S6#C#s#6.S6#s;)#s#6-S6#s;'#s#6,S6#D#s#6+S6#D#s#6*S6#E#s#6)S6#s:~#s#6(S6#s:|#s#6'S6#C#s#Z%S6#C#s#Y&S6#C#s#X$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##C5s#8#C4s#7$$#%S7%ST#C$#&S7&ST#C$#4S7#C#s#;3S7#C#s#;2S7#s;g#s#;1S7#E#s#;0S7#s;d#s#;/S7#C#s#;.S7#s;a#s#;-S7#s;_#s#;,S7#D#s#;+S7#D#s#;*S7#E#s#;)S7#s;Z#s#;(S7#s;X#s#;'S7#C#s#;#Cs#$s#:#CBs#9$$#$&#$)#$,#$/#$2#$5#$8#$;#$>#$A#$s#$#$s#'#$s#*#$s#-#&SW#C#s#3%SW#C#s#84S8#C#s#43S8#C#s#42S8#s<<#s#41S8#E#s#40S8#s<9#s#4/S8#C#s#4.S8#s<6#s#4-S8#s<4#s#4,S8#D#s#4+S8#D#s#4*S8#E#s#4)S8#s</#s#4(S8#s<-#s#4'S8#C#s#4%S8#C#s#V&S8#C#s#U$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#$s#/##C3s#54S9#C#s#33S9#C#s#32S9#s<l#s#31S9#E#s#30S9#s<i#s#3/S9#C#s#3.S9#s<f#s#3-S9#s<d#s#3,S9#D#s#3+S9#D#s#3*S9#E#s#3)S9#s<_#s#3(S9#s<]#s#3'S9#C#s#3%S9#C#s#3&S9#C#s#3$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#4S:6Cs#1#s#aSTSRm##s#13S:6Cs#2#s#bSQSPm##s#22S:6s=@s#3#s#cSOSNm##s#31S:6Es#4#s#dSMSLm##s#40S:6s=?s#5#s#eSKSJm##s#5/S:6Cs#6#s#fSISHm##s#6.S:6s=>s#7#s#gSGSFm##s#7-S:6s==s#8#s#hSESDm##s#8,S:6Ds#9#s#iSCSBm##s#9+S:6Ds#:#s#jSAS@m##s#:*S:6Es#;#s#kS?S>m##s#;)S:6s=<s#<#s#lS=S<m##s#<(S:6s=;s#=#s#mS;Mm##s#='S:6Cs#>#s#nLIm##s#>%S:6Cs#?#s#oHSSm##s#?&S:6Cs#@#s#pFS^m##s#@7s#Cs#A&#7s#Fs#A*#7s#Is#A.#7s#Ls#A2#7s#Os#A6#7s#Rs#A:#7s#Us#A>#7s#Xs#AB#7s#[s#As#&#7s#^s#As#*#7s#as#As#.#7s#ds#As#2#7s#gs#As#6#7s#js#As#:#7s#ms#As#>#j#$s#p#j#%s$E#5s$Fs$Hs#s#Fj#&s$I#j#'s$|#5s$}s$zs$M#Fj#(s%%#j#)s%X#5s%Ys%[s%*#Fj#%s%\#j#*s&9#5s&:s&3s%c#Fj#'s&>#j#+s&s#5s&ts&vs&E#Fj#)s&w#j#,s'Z#5s'[s'Ps'%#Fj#*s'_#j#-s(:#5s(;s(=s'h#Fj#+s(>#j#.s)'#5s)(s(us(K#Fj#,s),#j#/s)e#5s)fs)hs)7#Fj#-s)i#j#0s*X#5s*Ys*Fs)y#Fj#.s*]#j#1s+<#5s+=s+?s*j#Fj#/s+@#j#2s,5#5s,6s+{s+S#Fj#0s,:#j#3s,w#5s,xs,zs,I#Fj#1s,{#j#4s-v#5s-ws-\s-5#Fj#2s-{#j#5s.^#5s._s.as.0#Fj#3s.b#j#6s/c#5s/ds/Es.{#Fj#4s/h#j#7s0M#5s0Ns0Ps/{#Fj#5s0Q#j#8s1X#5s1Ys16s0m#Fj#6s1]#j#9s2D#5s2Es2Gs1r#Fj#7s2H#j#:s3U#5s3Vs3/s2g#Fj#8s3Z#j#;s4C#5s4Ds4Fs3q#Fj#9s4G#j#<s5Z#5s5[s50s4i#Fj#:s5_#j#=s6J#5s6Ks6Ms5x#Fj#;s6N#j#>s7g#5s7hs79s6s#Fj#<s7l#j#?s8Y#5s8Zs8\s8+#Fj#=s8]#j#@s9|#5s9}s9Js9)#Fj#>s:%#j#As:p#5s:qs:ss:B#Fj#?s:t#j#Bs<=#5s<>s;cs;C#Fj#@s<B#j#Cs=3#5s=4s=6s<a#Fj#As=7#j#Ds>x#5s>ys>8s=e#SSVSVGFm#$#j#Bs?##j#Cs?$#j#ESU#j#FSU#j#GSU##"). Qed.
Lemma sbs_paint : forall st lo hi v, same_but_shadow (paint st lo hi v) st.
Proof. intros. destruct st; repeat split; reflexivity. Qed.

Lemma poison_shadow_some : forall st a sz v,
  Z.land a 7 = 0 -> addr_is_in_mem a = true -> Z.land sz 7 = 0 -> addr_is_in_mem (a + sz - 8) = true ->
  exists st' ev, poison_shadow st a sz v = Some (st', ev) /\ same_but_shadow st' st.
Proof.
  intros st a sz v H1 H2 H3 H4. unfold poison_shadow. rewrite H1, H2, H3, H4. cbn [negb Z.eqb].
  set (st' := if 0 <? sz then paint st a (a + sz) v else st).
  assert (S : same_but_shadow st' st) by (subst st'; destruct (0 <? sz); [apply sbs_paint| apply sbs_refl]).
  repeat match goal with |- context [if ?b then _ else _] => destruct b; try (do 2 eexists; split; [reflexivity| exact S]) end.
  all: do 2 eexists; split; [reflexivity| exact S].
Qed.

(* [comment removed for export] *)
Definition hit_state (st : astate) (c cnt : Z) (rest : list Z) (ch : chunk) : astate :=
  upd_chunk (set_pc st c (mkPC (cnt - 1) rest)) ch.

(* [comment removed for export] *)
Lemma am_malloc_hit : forall st n kaddr c cp rest,
  0 <= n ->
  let r := compute_req n in
  let needed := rq_needed r in
  let U := compact_to_addr st c cp + rq_rz r in
  size_too_big r = false -> needed <= kMaxSize ->
  c = class_id needed -> 0 < c < kNumClasses ->
  pc_chunks (get_pc st c) = cp :: rest -> pc_count (get_pc st c) <> 0 ->
  (* [comment removed for export] *)
  Z.land U 7 = 0 -> addr_is_in_mem U = true -> addr_is_in_mem (U + Z.land (rq_size r) (Z.lnot 7) - 8) = true ->
  addr_is_in_mem (U + Z.land (rq_size r) (Z.lnot 7)) = true ->
  (rq_rz r = 16 \/ 32 <= rq_rz r) -> rq_primary r = true -> rq_rz r + rq_size r <= needed ->
  exists st' ev, am_malloc_k st n kaddr = Some (U, st', ev)
    /\ same_but_shadow st' (hit_state st c (pc_count (get_pc st c)) rest (mkChunk (compact_to_addr st c cp) U (rq_size r) (rq_rz r) c CAllocated)).
Proof.
  intros st n kaddr c cp rest Hn r needed U TB NK Hc HC PCS CNT AL8 IM1 IM2 IM3 RZ16 PRIM FIT.
  unfold am_malloc_k. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). fold r. rewrite TB.
  fold needed. replace (kMaxSize <? needed) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite <- Hc. unfold cache_alloc.
  replace ((c =? 0) || (kNumClasses <=? c)) with false by (symmetry; apply orb_false_intro; [apply Z.eqb_neq; lia| apply Z.leb_gt; lia]).
  replace (pc_count (get_pc st c) =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNT).
  rewrite PCS.
  assert (CA : forall st1, as_space_beg st1 = as_space_beg st -> compact_to_addr st1 c cp = compact_to_addr st c cp)
    by (intros st1 E; unfold compact_to_addr, region_beg; rewrite E; reflexivity).
  rewrite (CA (set_pc _ _ _)) by (destruct st; reflexivity). fold U.
  replace (compact_to_addr st c cp + needed <? U + rq_size r) with false by (symmetry; apply Z.ltb_ge; subst U; lia).
  rewrite PRIM. cbn [negb].
  set (st2 := upd_chunk _ _).
  set (rd := Z.land (rq_size r) (Z.lnot 7)).
  assert (RD8 : Z.land rd 7 = 0) by (subst rd; rewrite <- Z.land_assoc, (Z.land_comm (Z.lnot 7) 7), Z.land_lnot_diag, Z.land_0_r; reflexivity).
  assert (S14 : exists st4 ev4, (if 0 <? rd then poison_shadow st2 U rd 0 else Some (st2, [])) = Some (st4, ev4) /\ same_but_shadow st4 st2).
  { destruct (0 <? rd). 2:{ do 2 eexists. split; [reflexivity| apply sbs_refl]. }
    destruct (poison_shadow_some st2 U rd 0 AL8 IM1 RD8 IM2) as (st4 & ev4 & E & S). exists st4, ev4. split; [exact E| exact S]. }
  destruct S14 as (st4 & ev4 & E14 & S4). rewrite E14.
  fold rd in IM3. rewrite IM3. cbn [negb].
  assert (S15 : exists st5 ev5, (if negb (rq_size r =? rd) then Some (paint st4 (U + rd) (U + rd + 8) (Z.land (rq_size r) 7), [EShadow1 (U + rd) (Z.land (rq_size r) 7)]) else Some (st4, []))
                               = Some (st5, ev5) /\ same_but_shadow st5 st4).
  { destruct (negb (rq_size r =? rd)); do 2 eexists; (split; [reflexivity|]); [apply sbs_paint| apply sbs_refl]. }
  destruct S15 as (st5 & ev5 & E15 & S5). rewrite E15.
  replace (negb (U - kChunkHeaderSize =? compact_to_addr st c cp) && (U - kChunkHeaderSize <? compact_to_addr st c cp + 16)) with false.
  2:{ symmetry. unfold kChunkHeaderSize. subst U. destruct RZ16 as [E|GE].
      - rewrite E. replace (compact_to_addr st c cp + 16 - 16 =? compact_to_addr st c cp) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      - rewrite andb_false_iff. right. apply Z.ltb_ge. lia. }
  do 2 eexists. split; [reflexivity|].
  eapply sbs_trans; [exact S5|]. eapply sbs_trans; [exact S4|]. subst st2. unfold hit_state. apply sbs_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import FMapPositive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Lemma gadd_find : forall (mp : PositiveMap.t chunk) k k' v,
  PositiveMap.find k' (PositiveMap.add k v mp) = if PositiveMap.E.eq_dec k k' then Some v else PositiveMap.find k' mp.
Proof.
  intros mp k k' v. destruct (PositiveMap.E.eq_dec k k') as [E|NE].
  - apply PositiveMap.find_1. apply PositiveMap.add_1. exact E.
  - destruct (PositiveMap.find k' mp) as [w|] eqn:F.
    + apply PositiveMap.find_1. apply PositiveMap.add_2; [exact NE|]. apply PositiveMap.find_2. exact F.
    + destruct (PositiveMap.find k' (PositiveMap.add k v mp)) as [w|] eqn:G; [|reflexivity].
      exfalso. apply PositiveMap.find_2 in G. apply PositiveMap.add_3 in G; [|exact NE]. apply PositiveMap.find_1 in G. congruence.
Qed.

Lemma chunk_list_in_iff : forall st x, In x (chunk_list st) <-> exists k, PositiveMap.find k (as_chunks st) = Some x.
Proof.
  intros st x. unfold chunk_list. rewrite in_map_iff. split.
  - intros [[k v] [E Hin]]. cbn in E. subst v. exists k. apply PositiveMap.elements_complete. exact Hin.
  - intros [k F]. exists (k, x). split; [reflexivity|]. apply PositiveMap.elements_correct. exact F.
Qed.

Lemma chunk_list_upd_iff : forall st ch x,
  In x (chunk_list (upd_chunk st ch)) <-> x = ch \/ exists k, PositiveMap.find k (as_chunks st) = Some x /\ k <> ckey (ch_user_beg ch).
Proof.
  intros st ch x. rewrite chunk_list_in_iff. unfold upd_chunk, set_chunks. cbn [as_chunks]. split.
  - intros [k F]. rewrite gadd_find in F. destruct (PositiveMap.E.eq_dec (ckey (ch_user_beg ch)) k) as [E|NE].
    + left. congruence.
    + right. exists k. split; [exact F| congruence].
  - intros [->|[k [F NE]]].
    + exists (ckey (ch_user_beg ch)). rewrite gadd_find. destruct (PositiveMap.E.eq_dec _ _); [reflexivity| congruence].
    + exists k. rewrite gadd_find. destruct (PositiveMap.E.eq_dec _ _); [congruence| exact F].
Qed.
