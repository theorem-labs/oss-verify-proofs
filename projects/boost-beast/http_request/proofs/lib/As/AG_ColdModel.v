(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf AllocKit AllocRep AllocRepFacts AW_Efs AW_Populate AG_WFHit AG_MallocModel AS_Refill1 AG_RefillModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma upd_nth_upd_nth {A} : forall (l : list A) i x y, upd_nth (upd_nth l i x) i y = upd_nth l i y.
Proof. induction l as [|a l IH]; intros [|i] x y; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma firstn_length_ge {A} : forall k (l : list A), (k <= length l)%nat -> length (firstn k l) = k.
Proof. intros k l H. rewrite length_firstn. lia. Qed.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma in_mem_high : forall a, kHighMemBeg <= a <= kHighMemEnd -> addr_is_in_mem a = true.
Proof. intros a H. unfold addr_is_in_mem. apply Bool.orb_true_intro. right. apply andb_true_intro. split; apply Z.leb_le; lia. Qed.

Lemma upd_nth_znth {A} : forall (l : list A) i d, (i < length l)%nat -> upd_nth l i (znth l i d) = l.
Proof. induction l as [|a l IH]; intros [|i] d H; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sbs_set_pc : forall a b c p, same_but_shadow a b -> same_but_shadow (set_pc a c p) (set_pc b c p).
Proof. intros a b c p S. unfold same_but_shadow in *. cbn. intuition congruence. Qed.
Lemma sbs_upd_chunk : forall a b ch, same_but_shadow a b -> same_but_shadow (upd_chunk a ch) (upd_chunk b ch).
Proof. intros a b ch S. unfold same_but_shadow, upd_chunk in *. cbn. intuition congruence. Qed.
Lemma sbs_set_region : forall a b c r, same_but_shadow a b -> same_but_shadow (set_region a c r) (set_region b c r).
Proof. intros a b c r S. unfold same_but_shadow in *. cbn. intuition congruence. Qed.
Lemma sbs_add_map : forall a b mp, same_but_shadow a b -> same_but_shadow (add_map a mp) (add_map b mp).
Proof. intros a b mp S. unfold same_but_shadow in *. cbn. intuition congruence. Qed.
Lemma sbs_get_region : forall a b c, same_but_shadow a b -> get_region a c = get_region b c.
Proof. intros a b c S. unfold get_region. destruct S as (_ & _ & E & _). rewrite E. reflexivity. Qed.
Lemma sbs_region_beg : forall a b c, same_but_shadow a b -> region_beg a c = region_beg b c.
Proof. intros a b c S. unfold region_beg. destruct S as (E & _). rewrite E. reflexivity. Qed.
Lemma sbs_free_array_base : forall a b c, same_but_shadow a b -> free_array_base a c = free_array_base b c.
Proof. intros a b c S. unfold free_array_base. rewrite (sbs_region_beg a b c S). reflexivity. Qed.
Lemma sbs_compact_to_addr : forall a b c cp, same_but_shadow a b -> compact_to_addr a c cp = compact_to_addr b c cp.
Proof. intros a b c cp S. unfold compact_to_addr. rewrite (sbs_region_beg a b c S). reflexivity. Qed.
Lemma sbs_sym : forall a b, same_but_shadow a b -> same_but_shadow b a.
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.astate); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AG_MallocModel.same_but_shadow); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_space_beg); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_ptr_array); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.region); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_regions); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_cache_inited); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.pclass); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_cache); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_n_reserved); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.schunk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_sec); constr:(@Stdlib.FSets.FMapPositive.PositiveMap.t); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.chunk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_chunks); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.qcache); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_tq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_gq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_internal_init); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.mapping); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_maps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_env); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qmax); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qmin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qcache); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_sym)|] [|@H15; @H13; @H14; @H12; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H2; @H0; @H1; @H; @S; @b; @a|] "#4/#D#e#K#\#R#$###%#&#(#*#,#.#0#2#4#6#8#:#<#>#@#'#)#+#-#/#1#3#5#7#9#;#=#?#A#B#C#H#G#P#T#W#Y#Z#`#J#M#L#N#Q#S#U#V#X#[#]#^#_#a#b#c#d#e#g#f#I#O9#O&#P%#Q$#R$#S$#T$#U$#V$#W$#X$#Y$#Z$#[$#\$#]$#^$#_$#`$#a'#b'#c(#d$VS7FG%H%F#C$#&H&F#C$#8S9'H'F#%$#(H(F#E$#8S:)H)F#%$#*H*F#C$#8S;+H+F#%$#US<S=,H,F#%$#-H-F#D$#.H.F#D$#/H/F#E$#8S>0H0F#%$#8C1H1F#%$#2H2F#C$#3H3F#C$#4H4F#C$#$&#$*#$.#$3#$8#$<#$@#$s#$#$s#)#$s#.#$s#2#$s#7#$s#;#$s#@##Cs#Es#F#Cs#Cs#D#s#Bs#@s#A#Es#>s#?#s#=s#;s#<#Cs#9s#:#s#8s#6s#7#s#5s#3s#4#Ds#1s#2#Ds#/s#0#Es#-s#.#s#,s#*s#+#s#)s#'s#(#Cs#%s#&#Cs##s#$#CAB$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#$>#$@#&I#C#s#c'I#s#b#s#a(I#E#s#`)I#s#_#s#^*I#C#s#]+I#s#\#s#[,I#s#Z#s#Y-I#D#s#X.I#D#s#W/I#E#s#V0I#s#U#s#T1I#s#S#s#R2I#C#s#Q3I#C#s#P4I#C#s#O$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#$s#,#&S'#C#s#/'S'#s$2#s#/(S'#E#s#/)S'#s$/#s#/*S'#C#s#/+S'#s$,#s#/,S'#s$*#s#/-S'#D#s#/.S'#D#s#//S'#E#s#/0S'#s$%#s#/1S'#s$##s#/2S'#C#s#/3S'#C#s#/4S'#C#s#/$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#%I%S'#C$##Cs#\s#0#s$^s#[s#/#Es#Zs#.#s$Ys#Ys#-#Cs#Xs#,#s$Ts#Ws#+#s$Qs#Vs#*#Ds#Us#)#Ds#Ts#(#Es#Ss#'#s$Hs#Rs#&#s$Es#Qs#%#Cs#Ps#$#Cs#Os###Cs#NB$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#$>#$@#'J#s$|#s#M(J#E#s#M)J#s$y#s#M*J#C#s#M+J#s$v#s#M,J#s$t#s#M-J#D#s#M.J#D#s#M/J#E#s#M0J#s$o#s#M1J#s$m#s#M2J#C#s#M3J#C#s#M4J#C#s#M$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#$s#)#'S(#s%I#s#,(S(#E#s#,)S(#s%F#s#,*S(#C#s#,+S(#s%C#s#,,S(#s%A#s#,-S(#D#s#,.S(#D#s#,/S(#E#s#,0S(#s%<#s#,1S(#s%:#s#,2S(#C#s#,3S(#C#s#,4S(#C#s#,$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#%J%S(#C$#&J&S(#C$##s%vs#Ys#0#Es#Xs#/#s%qs#Ws#.#Cs#Vs#-#s%ls#Us#,#s%is#Ts#+#Ds#Ss#*#Ds#Rs#)#Es#Qs#(#s%`s#Ps#'#s%]s#Os#&#Cs#Ns#%#Cs#Ms#$#Cs#Ls##$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#$>#$B#(K#E#s#L)K#s&3#s#L*K#C#s#L+K#s&0#s#L,K#s&.#s#L-K#D#s#L.K#D#s#L/K#E#s#L0K#s&)#s#L1K#s&'#s#L2K#C#s#L3K#C#s#L4K#C#s#L$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#(S)#E#s#))S)#s&Y#s#)*S)#C#s#)+S)#s&V#s#),S)#s&T#s#)-S)#D#s#).S)#D#s#)/S)#E#s#)0S)#s&O#s#)1S)#s&M#s#)2S)#C#s#)3S)#C#s#)4S)#C#s#)$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###%K%S)#C$#&K&S)#C$#'K'S)#s'.$##Es#Vs#0#s')s#Us#/#Cs#Ts#.#s'$s#Ss#-#s&}s#Rs#,#Ds#Qs#+#Ds#Ps#*#Es#Os#)#s&ts#Ns#(#s&qs#Ms#'#Cs#Ls#&#Cs#Ks#%#Cs#Js#$$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$<#$@#$s#$#)L#s'E#s#K*L#C#s#K+L#s'B#s#K,L#s'@#s#K-L#D#s#K.L#D#s#K/L#E#s#K0L#s';#s#K1L#s'9#s#K2L#C#s#K3L#C#s#K4L#C#s#K$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#$s###)S*#s'h#s#&*S*#C#s#&+S*#s'e#s#&,S*#s'c#s#&-S*#D#s#&.S*#D#s#&/S*#E#s#&0S*#s'^#s#&1S*#s'\#s#&2S*#C#s#&3S*#C#s#&4S*#C#s#&$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#%L%S*#C$#&L&S*#C$#'L'S*#s(<$#(L(S*#E$##s(9s#Ss#0#Cs#Rs#/#s(4s#Qs#.#s(1s#Ps#-#Ds#Os#,#Ds#Ns#+#Es#Ms#*#s((s#Ls#)#s(%s#Ks#(#Cs#Js#'#Cs#Is#&#Cs#Hs#%$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$:#$>#$B#$s#&#*M#C#s#J+M#s(P#s#J,M#s(N#s#J-M#D#s#J.M#D#s#J/M#E#s#J0M#s(I#s#J1M#s(G#s#J2M#C#s#J3M#C#s#J4M#C#s#J$%#$(#$+#$.#$1#$4#$7#$:#$=#$@#*S+#C#s##+S+#s(p#s##,S+#s(n#s##-S+#D#s##.S+#D#s##/S+#E#s##0S+#s(i#s##1S+#s(g#s##2S+#C#s##3S+#C#s##4S+#C#s##$%#$(#$+#$.#$1#$4#$7#$:#$=#%M%S+#C$#&M&S+#C$#'M'S+#s)F$#(M(S+#E$#)M)S+#s)E$##Cs#Ps#0#s)@s#Os#/#s)=s#Ns#.#Ds#Ms#-#Ds#Ls#,#Es#Ks#+#s)4s#Js#*#s)1s#Is#)#Cs#Hs#(#Cs#Gs#'#Cs#Fs#&$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$8#$<#$@#$s#$#$s#(#+N#s)Z#s#I,N#s)X#s#I-N#D#s#I.N#D#s#I/N#E#s#I0N#s)S#s#I1N#s)Q#s#I2N#C#s#I3N#C#s#I4N#C#s#I$%#$(#$+#$.#$1#$4#$7#$:#$=#+S,#s)w#@,S,#s)u#@-S,#D#@.S,#D#@/S,#E#@0S,#s)p#@1S,#s)n#@2S,#C#@3S,#C#@4S,#C#@$%#$(#$+#$.#$1#$4#$7#$:#%N%S,#C$#&N&S,#C$#'N'S,#s*L$#(N(S,#E$#)N)S,#s*K$#*N*S,#C$##s*Hs#Ms#0#s*Es#Ls#/#Ds#Ks#.#Ds#Js#-#Es#Is#,#s*<s#Hs#+#s*9s#Gs#*#Cs#Fs#)#Cs#Es#(#Cs#Ds#'$$#$&#$(#$*#$,#$.#$0#$2#$4#$6#$:#$>#$B#$s#&#$s#*#,O#s*^#s#H-O#D#s#H.O#D#s#H/O#E#s#H0O#s*Y#s#H1O#s*W#s#H2O#C#s#H3O#C#s#H4O#C#s#H$%#$(#$+#$.#$1#$4#$7#$:#,S-#s*x#=-S-#D#=.S-#D#=/S-#E#=0S-#s*s#=1S-#s*q#=2S-#C#=3S-#C#=4S-#C#=$%#$(#$+#$.#$1#$4#$7#%O%S-#C$#&O&S-#C$#'O'S-#s+N$#(O(S-#E$#)O)S-#s+M$#*O*S-#C$#+O+S-#s+L$##s+Is#Js#0#Ds#Is#/#Ds#Hs#.#Es#Gs#-#s+@s#Fs#,#s+=s#Es#+#Cs#Ds#*#Cs#Cs#)#Cs#Bs#($$#$&#$(#$*#$,#$.#$0#$2#$4#$8#$<#$@#$s#$#$s#(#$s#,#-P#D#s#G.P#D#s#G/P#E#s#G0P#s+[#s#G1P#s+Y#s#G2P#C#s#G3P#C#s#G4P#C#s#G$%#$(#$+#$.#$1#$4#$7#-S.#D#:.S.#D#:/S.#E#:0S.#s+r#:1S.#s+p#:2S.#C#:3S.#C#:4S.#C#:$%#$(#$+#$.#$1#$4#%P%S.#C$#&P&S.#C$#'P'S.#s,L$#(P(S.#E$#)P)S.#s,K$#*P*S.#C$#+P+S.#s,J$#,P,S.#s,I$##Ds#Gs#0#Ds#Fs#/#Es#Es#.#s,@s#Ds#-#s,=s#Cs#,#Cs#Bs#+#Cs#As#*#Cs#@s#)$$#$&#$(#$*#$,#$.#$0#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#.Q#D#s#F/Q#E#s#F0Q#s,Y#s#F1Q#s,W#s#F2Q#C#s#F3Q#C#s#F4Q#C#s#F$%#$(#$+#$.#$1#$4#.S/#D#7/S/#E#70S/#s,m#71S/#s,k#72S/#C#73S/#C#74S/#C#7$%#$(#$+#$.#$1#%Q%S/#C$#&Q&S/#C$#'Q'S/#s-F$#(Q(S/#E$#)Q)S/#s-E$#*Q*S/#C$#+Q+S/#s-D$#,Q,S/#s-C$#-Q-S/#D$##Ds#Ds#0#Es#Cs#/#s-<s#Bs#.#s-9s#As#-#Cs#@s#,#Cs#?s#+#Cs#>s#*$$#$&#$(#$*#$,#$.#$0#$4#$8#$<#$@#$s#$#$s#(#$s#,#$s#0#/R#E#s#E0R#s-S#s#E1R#s-Q#s#E2R#C#s#E3R#C#s#E4R#C#s#E$%#$(#$+#$.#$1#/S0#E#40S0#s-d#41S0#s-b#42S0#C#43S0#C#44S0#C#4$%#$(#$+#$.#%R%S0#C$#&R&S0#C$#'R'S0#s.<$#(R(S0#E$#)R)S0#s.;$#*R*S0#C$#+R+S0#s.:$#,R,S0#s.9$#-R-S0#D$#.R.S0#D$##Es#As#0#s.4s#@s#/#s.1s#?s#.#Cs#>s#-#Cs#=s#,#Cs#<s#+$$#$&#$(#$*#$,#$.#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#$s#2#0S##s.I#s#D1S##s.G#s#D2S##C#s#D3S##C#s#D4S##C#s#D$%#$(#$+#$.#0S1#s.W#11S1#s.U#12S1#C#13S1#C#14S1#C#1$%#$(#$+#%S#%S1#C$#&S#&S1#C$#'S#'S1#s/.$#(S#(S1#E$#)S#)S1#s/-$#*S#*S1#C$#+S#+S1#s/,$#,S#,S1#s/+$#-S#-S1#D$#.S#.S1#D$#/S#/S1#E$##s/(s#>s#0#s/%s#=s#/#Cs#<s#.#Cs#;s#-#Cs#:s#,$$#$&#$(#$*#$,#$0#$4#$8#$<#$@#$s#$#$s#(#$s#,#$s#0#$s#4#1S$#s/9#s#C2S$#C#s#C3S$#C#s#C4S$#C#s#C$%#$(#$+#1S2#s/D#.2S2#C#.3S2#C#.4S2#C#.$%#$(#%S$%S2#C$#&S$&S2#C$#'S$'S2#s/x$#(S$(S2#E$#)S$)S2#s/w$#*S$*S2#C$#+S$+S2#s/v$#,S$,S2#s/u$#-S$-S2#D$#.S$.S2#D$#/S$/S2#E$#0S$0S2#s/t$##s/qs#;s#0#Cs#:s#/#Cs#9s#.#Cs#8s#-$$#$&#$(#$*#$.#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#$s#2#$s#6#2S%#C#s#B3S%#C#s#B4S%#C#s#B$%#$(#2S3#C#+3S3#C#+4S3#C#+$%#%S%%S3#C$#&S%&S3#C$#'S%'S3#s0b$#(S%(S3#E$#)S%)S3#s0a$#*S%*S3#C$#+S%+S3#s0`$#,S%,S3#s0_$#-S%-S3#D$#.S%.S3#D$#/S%/S3#E$#0S%0S3#s0^$#1S%1S3#s0]$##Cs#8s#0#Cs#7s#/#Cs#6s#.$$#$&#$(#$,#$0#$4#$8#$<#$@#$s#$#$s#(#$s#,#$s#0#$s#4#$s#8#3S&#C#s#A4S&#C#s#A$%#3S4#C#(4S4#C#(%S&%S4#C$#&S&&S4#C$#'S&'S4#s1H$#(S&(S4#E$#)S&)S4#s1G$#*S&*S4#C$#+S&+S4#s1F$#,S&,S4#s1E$#-S&-S4#D$#.S&.S4#D$#/S&/S4#E$#0S&0S4#s1D$#1S&1S4#s1C$#2S&2S4#C$##Cs#5s#0#Cs#4s#/$$#$&#$*#$.#$2#$6#$:#$>#$B#$s#&#$s#*#$s#.#$s#2#$s#6#$s#:#4S5#C#s#@%S5%S6#C$#&S5&S6#C$#'S5'S6#s2)$#(S5(S6#E$#)S5)S6#s2($#*S5*S6#C$#+S5+S6#s2'$#,S5,S6#s2&$#-S5-S6#D$#.S5.S6#D$#/S5/S6#E$#0S50S6#s2%$#1S51S6#s2$$#2S52S6#C$#3S53S6#C$#4S6#Cs#2#$%#$)#$-#$1#$5#$9#$=#$A#$s#%#$s#)#$s#-#$s#1#$s#5#$s#9#5Cs#>s#?S&m##s#>5Cs#=s#>S%m##s#=5s2bs#<s#=S$m##s#<5Es#;s#<S#m##s#;5s2_s#:s#;Rm##s#:5Cs#9s#:Qm##s#95s2\s#8s#9Pm##s#85s2Zs#7s#8Om##s#75Ds#6s#7Nm##s#65Ds#5s#6Mm##s#55Es#4s#5Lm##s#45s2Us#3s#4Km##s#35s2Ss#2s#3Jm##s#25Cs#1s#2Im##s#15Cs#0s#1Fm##s#05Cs#0s#_Gm##s#06s#3s#1%#6s#7s#1(#6s#;s#1+#6s#?s#1.#6s#Cs#11#6s#Gs#14#6s#Ks#17#6s#Os#1:#6s#Ss#1=#6s#Ws#1@#6s#[s#1s###6s#_s#1s#&#6s#cs#1s#)#6s#gs#1s#,#6s#ks#1s#/#j#$s#o#j#%s$S#7s$Ts$Rs#s#Gj#&s$W#j#'s%?#7s%@s%;s$^#Gj#%s%C#j#(s&/#7s&0s&(s%M#Gj#'s&3#j#)s'##7s'$s&us&@#Gj#(s''#j#*s'w#7s'xs'js'7#Gj#)s'{#j#+s(s#7s(ts(cs(2#Gj#*s(w#j#,s)s#7s)ts)`s)1#Gj#+s)w#j#-s*w#7s*xs*as*4#Gj#,s*{#j#.s,##7s,$s+fs+;#Gj#-s,'#j#/s-/#7s-0s,os,F#Gj#.s-3#j#0s.?#7s.@s-|s-U#Gj#/s.C#j#1s/S#7s/Ts/1s.h#Gj#0s/W#j#2s0k#7s0ls0Fs0##Gj#1s0o#j#3s2+#7s2,s1_s1>#Gj#2s2/#j#4s3`#7s3as2|s2]#GVS7FHm#$#j#5s3g#j#6S8#j#7S8##"). Qed.

Section ColdModel.
  Variables (st : astate) (c : Z).
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c. Let csz := class_size c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.

  Hypothesis W : WF st.
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis EMPTY : pc_count (get_pc st c) = 0.
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  Hypothesis HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0.

  (* [comment removed for export] *)
  Definition gfa_state : astate :=
    mkState (as_space_beg st) (as_ptr_array st) (upd_nth (as_regions st) (zidx c) (refill_region st c)) true
            (as_cache st) (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st)
            (as_internal_init st) (refill_newmaps st c ++ as_maps st) (as_shadow st) (as_env st) (as_track_shadow st)
            (as_qmax st) (as_qmin st) (as_qcache st).

  Let RO : region_ok st c. Proof. apply WF_region; [exact W| unfold kNumClasses; lia]. Qed.
  Let T : 32 <= csz <= 65536 /\ csz mod 32 = 0 /\ 2 <= max_count c <= 16 /\ max_count c mod 2 = 0.
  Proof. pose proof (class_size_table_facts c ltac:(lia)) as (T1 & T2 & T3 & T4 & T5 & T6). subst csz. repeat split; try lia. Qed.
  Let NR : 1 <= n <= 8 /\ n + n = max_count c.
  Proof. subst n. unfold rf_n. lia. Qed.
  Let LENR : length (as_regions st) = 32%nat.
  Proof. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
  Let FLL : zlen fl = nf. Proof. symmetry. exact (ro_numfreed _ _ RO). Qed.
  Let AUR : 0 <= au <= mu /\ mu mod kUserMapSize = 0 /\ au mod csz = 0 /\ mu - au < csz + (if au =? 0 then kUserMapSize else 0).
  Proof.
    pose proof (ro_alloc_nonneg _ _ RO). pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_mod _ _ RO). pose proof (ro_alloc_mod _ _ RO ltac:(destruct T; lia)).
    pose proof (ro_tail_small _ _ RO ltac:(destruct T; lia)) as TS. fold r au mu csz in TS |- *.
    repeat split; try assumption; try lia.
  Qed.
  Let NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize /\ mfa mod kFreeArrayMapSize = 0.
  Proof.
    pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_mod _ _ RO). pose proof (ro_fa_bound _ _ RO). fold r nf mfa in H, H0, H1 |- *.
    assert (0 <= nf) by (rewrite <- FLL; unfold zlen; lia). lia.
  Qed.

  Lemma get_region_set_region : forall x rg, length (as_regions x) = 32%nat -> get_region (set_region x c rg) c = rg.
  Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.astate); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.region); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_regions); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AG_WFHit.znth_upd_nth_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.zidx); constr:(c); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.region0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AS_Refill1.rf_au'); constr:(nf); constr:(au); constr:(mu); constr:(au'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AS_Refill1.rf_mfa'); constr:(mfa); constr:(mfa'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AS_Refill1.rf_nf1); constr:(nf1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AS_Refill1.rf_nnew); constr:(nnew); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AS_Refill1.rf_mu'); constr:(mu'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.class_size); constr:(csz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AS_Refill1.rf_n); constr:(n); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rg_mapped_user); constr:(r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rg_allocated_user); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rg_mapped_free_array); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rg_num_freed); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(st); constr:(LENR); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_space_beg); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.max_count); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kFreeArrayMapSize); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kUserMapSize); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(AUR); constr:(T); constr:(HC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.znth); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.mkState); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_ptr_array); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.upd_nth); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_cache_inited); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_cache); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_n_reserved); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_sec); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_chunks); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_tq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_gq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_internal_init); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_maps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_shadow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_env); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_track_shadow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qmax); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qmin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.as_qcache); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.get_region); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.set_region)|] [|@n; @x; @y; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__p1; @__p2; @__p3; @__p4; @__p5; @__p6; @__p7; @__p8; @__p9; @__arith; @__sat3; @__sat4; @__sat5; @__sat6; @__sat7; @__sat8; @z2; @H2; @cstr0; @cstr; @LENR0; @L0; @heq_nf; @heq_mfa; @heq_au; @heq_mu; @heq_n; @heq_csz; @heq_mu'; @heq_nnew; @heq_nf1; @heq_mfa'; @heq_au'; @L; @rg|] "#'S#4$\#F$.#b$/$-#%#A#4#:#I#$###8#J#V#($7#H#M#g#Z#e#z#'$:#0#9#.#y#|#+$?#>#_#a#D#`#k#n#2#p#s#v#~#*$6#,#/#1$@#B#@#G#K#L#N#O#P#Q#R#S#T#U#W#X#Y#[#\#]#i#j#h#m#l#o#r#x#}$$$%#{$&$(#&$*$,$0$9#-$<$=$A$B$>#)#3$C$E$D$F$G$H#^#C#?$K$L$M$N$O$P$Q$R$S$T$U$V$W$X$Y$Z$[$J$I$]$\#7#=#q#d#E#t$1$2#c$'$4$3#<#u#w#;$5$;$8$+#f$#$)=$F$#=&$G%$H$$I%$J%$K*$L)$M$$N'$O'$P*$Q$$R%$S%$T%#6$$U%$V$#G%$W%$X+#F%$Y/$Z%$[%/M2O##S3##############################################################$Ks###/HUSFI9#Nj#$K#XSGIS$LP'C#$CSH$m#$#YSIIS$S%LP'C#$CSJ$m#$#XSKIS$LP'C#$CSL$m#$#XSMIS$LP'C#$CSN$m#$#XSOIS$LP'C#$CSP$m#$#USQI'C#$CQ$m#$#USRI'C#$CSS$m#$#USTS''C#$CP$m#$#USUS''C#$CL$m#$#USVS''C#$CS%$m#$#USWS''C#$CS$$m#$#US4I9#s#5VS5EI&S(&#&#&#&#+#6)#j#%CNVS5ENj#%C#'CI`SXCKCCS4&S&$SYII#'C):KCS6S&S7SZ20$s#D*#/S,2O#$K#s#G3$$C#/US-KUS-C3M3N$C$#$KMNVS[MNWS\%$#j#&K#j#%K#'C.:KC-S&,$1/#s#U;4XS81/#S./S92O#$K#s#Y3$$C#A'C$:KC5S&4,'%#s#]s##<XS8'%#S]/S:2O#US;#3$%E#US;.%E-VS^EI6EI$Cs#4I($#%IE$Cs#7E($#VS<&#US=S9&s#6&#&#&#&#&#&#+#0+#%E,%E%1.&%E#k##%#k##'#US_I+s#J0$#%E%%E%1'&%E#k##%#k##'#0S%S/%ES%%ES/1S%S/%E#k##%#k##'#0PS)%EP%ES)1PS)%E#k##%#k##'#0LQ%EL%EQ1LQ%E#k##%#k##'#0Qs#b%Es#c1Qs#d%E#k##%#k##,#;Cs$a;Cs$f;CS3WS>C$#WS>C&#VS`#SaUSbS0WScS0$#USdS0USeC<CSf,C$R#<CS*,C&R#,C%H#<CR,C#R),C#R*,C+R#,C'M#USgCUShC*#GDDFS?4CS(4Cs$)-C$S@#.'GDDF#S#)(GDDF'#*)GDDFS17CE-C)S@#.,GDDF#S#)-GDDF&#[Si.GDDF(#USjD5s$35#4C#-C+S+#.4GDDF#S#*5GDDFSA)6GDDF$#*7GDDFSk)8GDDF$#7Cs$85S(&#&#4C#-C'S+#.?GDDF#S#*@GDDFS.)AGDDF$#*BGDDFSB7Cs#[5,&#4C#-C&S+#.s#(GDDF#S#*s#)GDDFS,)s#*GDDF$#*s#+GDDFSC)s#,GDDF$#)s#-GDDF-#)s#.GDDF/#*s#/GDDFS:5.&#+#7C#-Cs#1S+#.s#5GDDF#S#)s#6GDDF)#-Cs#5Sl@.s#8GDDF#S#8s#9GDDF%s#,#8s#:GDDF.s#-#8s#;GDDFs#%s#.#8s#<GDDFs#0s#/#VSms#=F'S2SDVSnNH$S2#SDm$%#WSoCEMXSpNH$#l#'*)#l#(s#Gs#F#l#)s#Ts#S#j#*C#j#+C#j#,C#j#-C#j#.C#j#/J#j#0J#j#1J#j#2J#j#3J#j#4J#j#5J#j#6J#j#7J#$CNM(R#$CNE(Sq#VS<%#%ER(#S1(#SA%s$|S*(#S.%s$;R(#S,(#SC(SB#('#%S*s#4(Sr#6S*s%)k##$#k##'#k##/#k##3#k#*C#k#+C#k#,C#k#-C#k#.C#k#/J#k#0J#k#1J#k#2J#k#3J#k#4J#k#5J#k#6J#k#7J#+S(%#I$Cs$SE+s%A%s$Z#$Cs$;E&s$e&#&#&#+#%Q#$Cs$OE$Cs$IEVSsPLVStLEnS2#$##C##%#S)#EVSuQ#6&#((#(*#%LPfN7643-$#s%$s%'Ls$lQIS?S1SvSwSxl#8s#>:#l#9s$Ps$K#l#:s$Xs$R#l#;s$`s$Z#l#<s$hs$b#l#=s$ps$j#l#>s$zs$t#l#?s%`C#l#@s%1s%*#l#As%4s%3#l#Bs%8s%6#l#Cs%<s%?#l#Ds%Es%R#XSys%gs%_s%X#l#Es%js%k#l#Fs%os%p#l#Gs%ts%u#l#Hs%ys%z#l#Is%~s&##l#Js&'s&(#l#Ks&,s&-#l#Ls&1s&2#l#Ms&6s&7#l#Ns&;s&<#l#Os&@s&A#9s&Gs&Jm#$#2Os&JZSzKs&Ms&H$#NZS{Os&Ls&KMSE#US=HUS|HXS}Os&Os&NMUS~HUT#HUT$HUT%HUT&HUT'HUT(HUT)HUT*HUT+HUT,HUT-HUT.HUT/HUT0HfT143210/.-,+*)('&%$#/#XT2O#s&`SE$O#Mm#9#WT3HIMVT4#I$O#Mm#&#j#Ps&i#j#QO#j#%T5##"). Qed.

  (* [comment removed for export] *)
  Lemma gfa_cold : exists stg ev,
    get_from_allocator (ensure_cache_inited st) c n = Some (stg, firstn (Z.to_nat n) fl1, ev) /\ same_but_shadow stg gfa_state.
  Proof.
    pose proof (rf_facts st c W HC ROOM) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    fold r in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15.
    fold nf mfa au mu fl n csz in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15.
    fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15.
    (* [comment removed for export] *)
    set (st0 := ensure_cache_inited st).
    assert (S0 : st0 = mkState (as_space_beg st) (as_ptr_array st) (as_regions st) true (as_cache st) (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st)
                              (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st)).
    { subst st0. unfold ensure_cache_inited. destruct st; cbn. destruct as_cache_inited; reflexivity. }
    assert (GR0 : get_region st0 c = r) by (rewrite S0; reflexivity).
    assert (RB0 : region_beg st0 c = region_beg st c) by (rewrite S0; reflexivity).
    assert (FB0 : free_array_base st0 c = free_array_base st c) by (rewrite S0; reflexivity).
    assert (L0 : length (as_regions st0) = 32%nat) by (rewrite S0; exact LENR).
    unfold get_from_allocator. rewrite GR0. fold nf.
    destruct (Z.lt_ge_cases nf n) as [NF|NF].
    2:{ (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_ge nf n) NF). destruct (Q15 NF) as (E1 & E2 & E3).
        assert (EFL : fl1 = fl) by (subst fl1; unfold rf_fl1; fold n; fold nnew; rewrite E2; reflexivity).
        rewrite !GR0. fold nf mfa au mu fl. rewrite <- EFL.
        do 2 eexists. split; [reflexivity|].
        unfold gfa_state, refill_region, refill_newmaps. fold r. fold nf mfa au mu fl. fold n mu' nnew nf1 mfa' au' fl1.
        rewrite E1, E3, Q5, Q4, E2, EFL, !Z.ltb_irrefl. cbn [app]. rewrite Z.mul_0_l, !Z.add_0_r. rewrite S0. apply sbs_refl. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_lt nf n) NF). destruct (Q14 NF) as [TOTLE ENN].
    pose proof (rf_batch_small c HC) as [BSM _]. fold n csz in BSM.
    pose proof AUR as (A1 & A2 & A3 & A4). pose proof NFR as (F1 & F2 & F3 & F4). pose proof T as (T1 & _). pose proof HM as (M1 & M2 & M3).
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kHighMemBeg, kHighMemEnd, kSpaceSize in *.
    assert (ERB : region_beg st c = as_space_beg st + c * 4294967296) by (rewrite region_beg_eq; reflexivity).
    assert (EFA : free_array_base st c = region_beg st c + 3758096384) by (rewrite free_array_base_eq; reflexivity).
    assert (TOTB : au + csz <= rf_total c nf au <= au + 65536) by (unfold rf_total, rf_k; fold n csz; clear - BSM NF NR T1 F1; nia).
    assert (ETOT : au + (n - nf) * csz = rf_total c nf au) by (unfold rf_total, rf_k; fold n csz; clear; lia).
    unfold populate_free_array. rewrite GR0. fold au mu nf fl mfa csz. rewrite ETOT.
    (* [comment removed for export] *)
    assert (PSu : forall stA, exists stB evB, poison_shadow stA (region_beg st c + mu) 262144 kAsanHeapLeftRedzoneMagic = Some (stB, evB) /\ same_but_shadow stB stA).
    { intros stA. apply poison_shadow_some.
      - rewrite land7_mod8, ERB. clear - M3 A2. Z.div_mod_to_equations. lia.
      - apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. rewrite ERB. clear - M1 M2 A1 ROOM HC; lia.
      - reflexivity.
      - apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. rewrite ERB. clear - M1 M2 A1 ROOM HC; lia. }
    assert (PSf : forall stA, mfa < mfa' -> exists stB evB, poison_shadow stA (free_array_base st c + mfa) (mfa' - mfa) kAsanHeapLeftRedzoneMagic = Some (stB, evB) /\ same_but_shadow stB stA).
    { intros stA LT. apply poison_shadow_some.
      - rewrite land7_mod8, EFA, ERB. clear - M3 F4. Z.div_mod_to_equations. lia.
      - apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. rewrite EFA, ERB. clear - M1 M2 F1 F2 F3 HC; lia.
      - rewrite land7_mod8. clear - F4 Q13. Z.div_mod_to_equations. lia.
      - apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. rewrite EFA, ERB. clear - M1 M2 F1 F2 F3 HC LT Q12 F4 Q13; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    set (R1 := mkRegion mu' au nf fl mfa).
    set (stU := if mu <? mu' then add_map st0 (mkMap (region_beg st c + mu) (mu' - mu) (MkUserMap c) PROT_RW false) else st0).
    assert (LU : length (as_regions stU) = 32%nat) by (subst stU; destruct (mu <? mu'); [cbn [as_regions add_map]; exact L0| exact L0]).
    assert (STEP1 : exists st1 ev1,
      (if rf_total c nf au <=? mu then Some (st0, r, [])
       else if kFreeArrayOffset <? mu + 0 + round_up (rf_total c nf au - mu) kUserMapSize then None
       else let (st1, ev1) := map_fixed st0 (region_beg st0 c + mu) (round_up (rf_total c nf au - mu) kUserMapSize) (MkUserMap c) in
            match poison_shadow st1 (region_beg st0 c + mu) (round_up (rf_total c nf au - mu) kUserMapSize) kAsanHeapLeftRedzoneMagic with
            | Some (st2, ev2) => Some (set_region st2 c (mkRegion (mu + round_up (rf_total c nf au - mu) kUserMapSize) au nf fl mfa),
                                       mkRegion (mu + round_up (rf_total c nf au - mu) kUserMapSize) au nf fl mfa, ev1 ++ ev2)
            | None => None end)
      = Some (st1, R1, ev1) /\ same_but_shadow st1 (set_region stU c R1)).
    { destruct (Z.leb_spec (rf_total c nf au) mu) as [TOT|TOT].
      - assert (E1 : mu' = mu) by (subst mu'; unfold rf_mu'; fold n; rewrite (proj2 (Z.ltb_lt nf n) NF), (proj2 (Z.ltb_ge _ _) TOT); reflexivity).
        assert (RREC : r = R1) by (subst R1; rewrite E1; subst mu au nf fl mfa; destruct r; reflexivity).
        do 2 eexists. split; [rewrite <- RREC; reflexivity|].
        subst stU. rewrite E1, Z.ltb_irrefl. rewrite <- RREC. rewrite S0. unfold same_but_shadow, set_region. cbn.
        repeat split; try reflexivity. unfold r, get_region. symmetry. apply upd_nth_znth. rewrite LENR. unfold zidx. clear - HC. lia.
      - assert (MS : round_up (rf_total c nf au - mu) kUserMapSize = 262144) by (unfold round_up, kUserMapSize; clear - TOT TOTB A1; Z.div_mod_to_equations; lia).
        assert (E1 : mu' = mu + 262144).
        { subst mu'. unfold rf_mu'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF), (proj2 (Z.ltb_lt _ _) TOT). unfold pop_ms. fold csz. rewrite MS. reflexivity. }
        rewrite MS. unfold kFreeArrayOffset. replace (3758096384 <? mu + 0 + 262144) with false by (symmetry; apply Z.ltb_ge; clear - ROOM; lia).
        unfold map_fixed. cbv iota beta. rewrite RB0.
        destruct (PSu (add_map st0 (mkMap (region_beg st c + mu) 262144 (MkUserMap c) PROT_RW false))) as (stB & evB & EP & SB). rewrite EP.
        replace (mu + 262144) with mu' by exact E1. do 2 eexists. split; [reflexivity|].
        apply sbs_set_region. subst stU. rewrite (proj2 (Z.ltb_lt mu mu')) by (clear - E1; lia). replace (mu' - mu) with 262144 by (clear - E1; lia). exact SB. }
    destruct STEP1 as (st1 & ev1 & ES1 & S1). rewrite ES1. clear ES1.
    assert (L1 : length (as_regions st1) = 32%nat) by (destruct S1 as (_ & _ & E & _); rewrite E; cbn [as_regions set_region]; rewrite length_upd_nth; exact LU).
    assert (GR1 : get_region st1 c = R1) by (rewrite (sbs_get_region _ _ c S1); apply get_region_set_region; exact LU).
    assert (FB1 : free_array_base st1 c = free_array_base st c).
    { rewrite (sbs_free_array_base _ _ c S1). subst stU. rewrite <- FB0. destruct (mu <? mu'); reflexivity. }
    subst R1. cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
    rewrite <- ENN, <- Q4.
    (* [comment removed for export] *)
    set (R2 := mkRegion mu' au nf fl mfa').
    set (mpF := mkMap (free_array_base st c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false).
    set (stF := if mfa <? mfa' then add_map stU mpF else stU).
    assert (LF : length (as_regions stF) = 32%nat) by (subst stF; destruct (mfa <? mfa'); [cbn [as_regions add_map]; exact LU| exact LU]).
    assert (SRSR : forall x A B, set_region (set_region x c A) c B = set_region x c B) by (intros x A B; unfold set_region; cbn; rewrite upd_nth_upd_nth; reflexivity).
    assert (EMFA : mfa' = (if 4 * nf1 <=? mfa then mfa else round_up (4 * nf1) 262144)).
    { subst mfa'. unfold rf_mfa'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF). fold nf1. unfold efs_new, kFreeArrayMapSize. reflexivity. }
    assert (STEP2 : exists st2 ev2, ensure_free_array_space st1 c nf1 = Some (st2, ev2) /\ same_but_shadow st2 (set_region stF c R2)).
    { unfold ensure_free_array_space. rewrite GR1. cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
      rewrite (Z.mul_comm nf1 4).
      destruct (Z.leb_spec (4 * nf1) mfa) as [FAST|SLOW].
      - do 2 eexists. split; [reflexivity|]. subst stF R2. rewrite EMFA, Z.ltb_irrefl. exact S1.
      - assert (LT : mfa < mfa') by (rewrite EMFA; unfold round_up; clear - SLOW; Z.div_mod_to_equations; lia).
        unfold kFreeArrayMapSize, kFreeArraySize in *. rewrite <- EMFA. replace (_ <? mfa') with false by (symmetry; apply Z.ltb_ge; clear - Q12; lia).
        unfold map_fixed. cbv iota beta. rewrite FB1. fold mpF.
        destruct (PSf (add_map st1 mpF) LT) as (stB & evB & EP & SB). rewrite EP.
        do 2 eexists. split; [reflexivity|]. subst R2.
        assert (SB' : same_but_shadow stB (set_region stF c (mkRegion mu' au nf fl mfa))).
        { eapply sbs_trans; [exact SB|]. subst stF. rewrite (proj2 (Z.ltb_lt _ _) LT).
          change (set_region (add_map stU mpF) c (mkRegion mu' au nf fl mfa)) with (add_map (set_region stU c (mkRegion mu' au nf fl mfa)) mpF). apply sbs_add_map. exact S1. }
        rewrite <- (SRSR stF (mkRegion mu' au nf fl mfa)). apply sbs_set_region. exact SB'. }
    destruct STEP2 as (st2 & ev2 & ES2 & S2). rewrite ES2. clear ES2.
    assert (L2 : length (as_regions st2) = 32%nat) by (destruct S2 as (_ & _ & E & _); rewrite E; cbn [as_regions set_region]; rewrite length_upd_nth; exact LF).
    assert (GR2 : get_region st2 c = R2) by (rewrite (sbs_get_region _ _ c S2); apply get_region_set_region; exact LF).
    rewrite GR2. subst R2. cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
    replace (mu' <? au + nnew * csz) with false by (symmetry; apply Z.ltb_ge; clear - Q5 Q6; lia).
    rewrite (get_region_set_region st2 _ L2). cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
    replace (nf1 <? n) with false by (symmetry; apply Z.ltb_ge; clear - Q1; lia). cbn iota.
    rewrite (get_region_set_region st2 _ L2). cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
    assert (EFL1 : carve_asc au csz 0 (Z.to_nat nnew) ++ fl = fl1) by (subst fl1; unfold rf_fl1; fold n csz; fold nnew; reflexivity).
    rewrite EFL1, <- Q5, SRSR.
    do 2 eexists. split; [reflexivity|].
    (* [comment removed for export] *)
    eapply sbs_trans; [apply sbs_set_region; exact S2|]. rewrite SRSR.
    unfold gfa_state, refill_region, refill_newmaps. fold r. fold nf mfa au mu fl. fold n csz. fold mu' nnew nf1 mfa' au' fl1. fold mpF.
    subst stF stU. rewrite S0. destruct (mfa <? mfa'); destruct (mu <? mu'); apply sbs_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma am_malloc_cold : forall sz kaddr cp rest,
    0 <= sz ->
    let rq := compute_req sz in
    let needed := rq_needed rq in
    let U := compact_to_addr st c cp + rq_rz rq in
    size_too_big rq = false -> needed <= kMaxSize ->
    c = class_id needed ->
    firstn (Z.to_nat n) fl1 = cp :: rest ->
    Z.land U 7 = 0 -> addr_is_in_mem U = true -> addr_is_in_mem (U + Z.land (rq_size rq) (Z.lnot 7) - 8) = true ->
    addr_is_in_mem (U + Z.land (rq_size rq) (Z.lnot 7)) = true ->
    (rq_rz rq = 16 \/ 32 <= rq_rz rq) -> rq_primary rq = true -> rq_rz rq + rq_size rq <= needed ->
    exists st' ev, am_malloc_k st sz kaddr = Some (U, st', ev)
      /\ same_but_shadow st' (hit_state (refilled st c) c n rest (mkChunk (compact_to_addr st c cp) U (rq_size rq) (rq_rz rq) c CAllocated)).
  Proof.
    intros sz kaddr cp rest Hn rq needed U TB NK Hc TAKEN AL8 IM1 IM2 IM3 RZ16 PRIM FIT.
    destruct gfa_cold as (stg & evg & EG & SG).
    unfold am_malloc_k. replace (sz <? 0) with false by (symmetry; apply Z.ltb_ge; lia). fold rq. rewrite TB.
    fold needed. replace (kMaxSize <? needed) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite <- Hc. unfold cache_alloc.
    replace ((c =? 0) || (kNumClasses <=? c)) with false by (symmetry; apply orb_false_intro; [apply Z.eqb_neq; lia| apply Z.leb_gt; unfold kNumClasses; lia]).
    rewrite EMPTY. cbn [Z.eqb]. change (max_count c / 2) with n. rewrite EG. cbn [pc_chunks pc_count]. rewrite TAKEN.
    assert (CA : compact_to_addr (set_pc stg c (mkPC (n - 1) rest)) c cp = compact_to_addr st c cp).
    { etransitivity; [| exact (sbs_compact_to_addr _ _ c cp SG)]. reflexivity. }
    rewrite CA. fold U.
    replace (compact_to_addr st c cp + needed <? U + rq_size rq) with false by (symmetry; apply Z.ltb_ge; subst U; lia).
    rewrite PRIM. cbn [negb].
    set (st2 := upd_chunk _ _).
    set (rd := Z.land (rq_size rq) (Z.lnot 7)).
    assert (RD8 : Z.land rd 7 = 0) by (subst rd; rewrite <- Z.land_assoc, (Z.land_comm (Z.lnot 7) 7), Z.land_lnot_diag, Z.land_0_r; reflexivity).
    assert (S14 : exists st4 ev4, (if 0 <? rd then poison_shadow st2 U rd 0 else Some (st2, [])) = Some (st4, ev4) /\ same_but_shadow st4 st2).
    { destruct (0 <? rd). 2:{ do 2 eexists. split; [reflexivity| apply sbs_refl]. }
      destruct (poison_shadow_some st2 U rd 0 AL8 IM1 RD8 IM2) as (st4 & ev4 & E & S). exists st4, ev4. split; [exact E| exact S]. }
    destruct S14 as (st4 & ev4 & E14 & S4). rewrite E14.
    fold rd in IM3. rewrite IM3. cbn [negb].
    assert (S15 : exists st5 ev5, (if negb (rq_size rq =? rd) then Some (paint st4 (U + rd) (U + rd + 8) (Z.land (rq_size rq) 7), [EShadow1 (U + rd) (Z.land (rq_size rq) 7)]) else Some (st4, []))
                                 = Some (st5, ev5) /\ same_but_shadow st5 st4).
    { destruct (negb (rq_size rq =? rd)); do 2 eexists; (split; [reflexivity|]); [apply sbs_paint| apply sbs_refl]. }
    destruct S15 as (st5 & ev5 & E15 & S5). rewrite E15.
    replace (negb (U - kChunkHeaderSize =? compact_to_addr st c cp) && (U - kChunkHeaderSize <? compact_to_addr st c cp + 16)) with false.
    2:{ symmetry. unfold kChunkHeaderSize. subst U. destruct RZ16 as [E|GE].
        - rewrite E. replace (compact_to_addr st c cp + 16 - 16 =? compact_to_addr st c cp) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
        - rewrite andb_false_iff. right. apply Z.ltb_ge. lia. }
    do 2 eexists. split; [reflexivity|].
    eapply sbs_trans; [exact S5|]. eapply sbs_trans; [exact S4|]. subst st2. unfold hit_state. apply sbs_upd_chunk.
    eapply sbs_trans; [apply sbs_set_pc; exact SG|].
    unfold gfa_state, refilled, set_pc. cbn. rewrite upd_nth_upd_nth. apply sbs_refl.
  Qed.
End ColdModel.

End HCW.

