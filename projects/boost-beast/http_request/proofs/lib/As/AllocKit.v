(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AllocWf.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac hci :=
  try (lazymatch goal with HH : HeapCeil |- _ =>
         repeat (match goal with
                 | |- context [?X] => is_evar X; let T := type of X in constr_eq T HeapCeil; unify X HH
                 end)
       end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_beg_eq : forall st c, region_beg st c = as_space_beg st + c * 2^32.
Proof. intros st c. unfold region_beg, kRegionSizeLog. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma free_array_base_eq : forall st c, free_array_base st c = region_beg st c + kFreeArrayOffset.
Proof. reflexivity. Qed.

Lemma compact_to_addr_eq : forall st c cp, compact_to_addr st c cp = region_beg st c + cp * 16.
Proof. intros st c cp. unfold compact_to_addr, kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. lia. Qed.

Lemma shiftl4 : forall cp, Z.shiftl cp kCompactPtrScale = cp * 16.
Proof. intros cp. unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. lia. Qed.

(* [comment removed for export] *)
Lemma regions_disjoint : forall st c c', 0 <= c -> 0 <= c' -> c <> c' ->
  region_beg st c + 2^32 <= region_beg st c' \/ region_beg st c' + 2^32 <= region_beg st c.
Proof. intros st c c' Hc Hc' Hne. rewrite !region_beg_eq. nia. Qed.

Lemma region_in_space : forall st c, 0 <= c < 32 ->
  as_space_beg st <= region_beg st c /\ region_beg st c + 2^32 <= as_space_beg st + kSpaceSize.
Proof. intros st c Hc. rewrite region_beg_eq. unfold kSpaceSize. nia. Qed.

Lemma class_of_addr_region : forall st c off, 0 <= c < 32 -> 0 <= off < 2^32 ->
  class_of_addr st (region_beg st c + off) = c.
Proof.
  intros st c off Hc Hoff. unfold class_of_addr, kRegionSizeLog. rewrite region_beg_eq.
  replace (as_space_beg st + c * 2^32 + off - as_space_beg st) with (off + c * 2^32) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia.
  rewrite Z.add_0_l. rewrite Z.land_ones with (n := 5) by lia. change (Z.ones 5) with 31. apply Z.mod_small. lia.
Qed.

Lemma in_primary_region : forall st c off, 0 <= c < 32 -> 0 <= off < 2^32 ->
  in_primary st (region_beg st c + off) = true.
Proof.
  intros st c off Hc Hoff. unfold in_primary. pose proof (region_in_space st c Hc).
  apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition carved (st : astate) (c a : Z) : Prop :=
  0 <= c < kNumClasses /\ class_size c <> 0 /\ 0 <= a - region_beg st c
  /\ (a - region_beg st c) mod class_size c = 0
  /\ a - region_beg st c + class_size c <= rg_allocated_user (get_region st c).

(* [comment removed for export] *)
Lemma carved_range : forall st c a, WF st -> carved st c a ->
  region_beg st c <= a /\ a + class_size c <= region_beg st c + kFreeArrayOffset /\ 0 < class_size c <= 65536.
Proof.
  intros st c a W (Hc & Hsz & H0 & Hm & Hle). pose proof (WF_region st c W Hc) as RO.
  pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_bound _ _ RO). pose proof (class_size_table_facts c Hc).
  unfold kUserMapSize in *. lia.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.or Sort Prop.

(* [comment removed for export] *)
Lemma carved_sep : forall st c a c' a', WF st -> carved st c a -> carved st c' a' ->
  (c = c' /\ a = a') \/ a + class_size c <= a' \/ a' + class_size c' <= a.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.astate); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWf.WF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocKit.carved); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocKit.carved_range); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.region_beg); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.class_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kFreeArrayOffset); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@kc__1); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.kNumClasses); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.rg_allocated_user); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanAllocModel.get_region); constr:(@Stdlib.ZArith.BinInt.Z.eq_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@kc__2); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.proj1); constr:(@Stdlib.ZArith.BinInt.Z.divide); constr:(@Stdlib.ZArith.BinInt.Z.mod_divide); constr:(@Corelib.Init.Logic.ex); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@kc__3); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.lt_ge_cases); constr:(@kc__4); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzSquare); constr:(@Stdlib.micromega.EnvRing.Pinj); constr:(@Stdlib.micromega.EnvRing.PX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocKit.regions_disjoint); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@kc__3 (@Corelib.Numbers.BinNums.Z))|] [|@s; @R3'; @R2'; @R1'; @Hle'; @Hm'; @H0'; @Hsz'; @Hc'; @c'; @a'; @e; @z; @Hq; @q; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__p1; @__p2; @__arith; @H; @__x6; @H1; @o; @Hq'; @q'; @x; @d; @Hna; @n; @Ha; @__p3; @__sat4; @__sat5; @Hne; @Hle; @Hm; @H0; @Hsz; @Hc; @R3; @R2; @R1; @Ca'; @Ca; @W; @a; @c; @st|] "#8:#z%'#~$^$-$_$]###$#(#'$g#*#&#)#z$+#+#%#,#I${#U#_#m#-#.#;#E#G#M#Q#^#c#a#h#n$I$e#/#5#?#C#K#L#W#]#e$K$4#=#D#H#J#O#[#\#d#f#j#o$0#0#3#2#A#F#P#S#T#V#b#k#i#u$T#1#4#7#<#@#B#X#`#g#l#6#>#R#Y#Z#s#:#9#N$l#8#p#q#r#v#t$$$%$:$=$D$B$S$p$q#w#x$u$G$A$<%%$#$?$>$P$U$V$Y$Z$\$h$n$r$s$o$H$t$z$y$x#y$~%#%$%&%(%'#}$/$'$d$)$3$&$($*$6$2$v$M$,$[$7$9$8$a$`$.$5$w$F$W$1$R$Q$c$L$J$}$i$X$m$j$;$C$E$N$b$k$@$O$f$|P$V$$W%$X$$Y%$Z&$[%$\%$]$$^%$_%$`&$a&$b%$c+$d%$e%$f$$g'$h*$i$$j$$k%$l%$m'$n($o$$p%$q%$r%$s&$t&$u)$v%$w)$x*$y%$z%${%$|&$}&$~%%#%%$%%%&%&*UT+KWSwJKNWSwONS#YSxMOJS#I)MO$#J*O&J#&&Q$$#/E&#SN##############################6#$8#(5#(7#(<#)RM$#O*M&O#&&Q$$#/E&$'.($#(&#(+#'CRO'CMJ($#*R&M#$#J$s#,M,$#,(#j##,#)S$R&#Q$*#/E,$-@($#(&#)S*S$$#R*S*&S$#)S+S*&#Q$%#/E'$(s#+($#(&#*S+&S*#)S8S+&#Q$%#/E'$(s#4($#(&#'CS8S*'CS+S$($#*S8&S+#$#S$$9S+,$#,(#j##,#/E)$*s#B($#*SO&S8#)S]SO&#Q$%#*S]/E#$$s#K($#YSxSPSOS8S+S$)SPSO$#S8&$Q$.#/E0$1s#S($#(&#()#)S^S]$#SO&SO2&%Q$$#(#2('#'CS^SQ'CSPS]($#*S^&SP#$#S]*SQ&S]#$#SP,&#,*#j##.#)S9SQ&#Q$)#/E+$,s#n($#(&#)SgSP$#SQ)S_S^&#Q$5#/E7$8s#w($#(&#*S9&S^#)SqS9&#Q$%#/E'$(s$$($#(&#'CSqSg'CS_S9($#*Sq&S_#$#S9*Sg&S9#$#S_,&#,*#j##.#/E($)s$4($#*S_&Sg#)SmS_&#Q$%#/E3$4s$<($#$ES,/S,SB($#*S,'C#E7#)S`S,+Sm#$E#1$('C#E&&*2S`S,3#$%#('#(*#(.#(2#'CS`Sm'CS,Sn($#*S`&S,#$#Sn*Sm&Sn#$#S,,&#,*#j##.#'C+E7#)SCS`+S,#$E#1$0'C#E&&22SCS`3#$%#('#(*#(.#$ESC/SCSB($#*Sh'C#E7#)S:Sh+SC#$E#1$('C#E&&*2S:Sh3#$%#('#(*#(.#*S:'C#E7#)SaS:+Sh#$E#1$('C#E&&*2SaS:3#$%#('#(*#(.#'CSaSh'CS:SC($#*Sa&S:#$#SC&SCs#&$#S:,%#,)#j##-#)SRSa+S:#$E#1$-'C#E&&/2SRSa3#$%#('#(*#*SR'C#E7#)S;Sb+SR#$E#*Sb1%#'C#E&'%2S;Sb3#$%#('#(+#)SDS;+Sb#$E#*S;1%#'C#E&'%2SDS;3#$%#('#(+#'CSDSb'CS;SR($#*SD&S;#$#SR&SR=$#S;,%#,)#j##-#)S-SD+S;#1#,'C#E&%.2S-SD3#$%#('#)SSS-+SD#$E#)S.SS+S-#*SS1$#'C#E&&%2S.SS3#$%#('#)SES.+SS#*S.1$#'C#E&&%2SES.3#$%#('#'CSESS'CS.S-($#*SE&S.#$#S-&S-:$#S.,%#,)#j##-#)S%SE+S.#&#,2S%SE3#$%#)SFS%+SE#*S%1$#'C#E)S<SF+S%#*SF&$#2S<SF3#$%#$ES%/S%SB($#'C/E7#)S=S%+SE#$E#1$4'C#E&&62S=S%3#$%#('#(*#(.#(1#'CS=SF'CS<S%($#*S=&S<#$#S%&S%?$#S<,%#,)#j##-#'Cs#$E7#)S/SF+S%#$E#1$s#)'C#E&&s#+2S/SF3#$%#('#(*#(.#$ES</S<SB($#'C;E7#)SGS=+S<#$E#1$@'C#E&&B2SGS=3#$%#('#(*#(.#*S/'C#E7#)STS/+S=#$E#1$('C#E&&*2STS/3#$%#('#(*#(.#'CSTSo'CSGS/($#*ST&SG#$#S/*So&S/#$#SG,&#,*#j##.#)S0So+S/#$E#1$+'C#E&&-2S0So3#$%#('#(*#*SG'C#E7#)SUST+SG#$E#1$<'C#E&&>2SUST3#$%#('#(*#)SVS0+ST#$E#*S01%#'C#E&'%2SVS03#$%#('#(+#'CSVSi'CSUS0($#*SV&SU#$#S0*Si&S0#$#SU,&#,*#j##.#)S'Si+S0#1#*'C#E&%,2S'Si3#$%#('#)SWSU+Si#$E#)S>SV+SU#1#9'C#E&%;2S>SV3#$%#('#)ScS'+SV#*S'1$#'C#E&&%2ScS'3#$%#('#'CScSW'CS>S'($#*Sc&S>#$#S'*SW&S'#$#S>,&#,*#j##.#)SjSW+S'#&#*2SjSW3#$%#)SkS>+SW#*S>1$#'C#E)SHSc+S>#&#82SHSc3#$%#VSySHSj'CSHSj7#F$#'CSISk7#F$#'CS?SH(#&*S?&SI#$#Sk*SH&Sk#$#SI,&#,*#j#$-#$EH/HSB($#*I'C#E7#)SXS#+S1#$E#)S2N+S(#*N1$#'C#E)SJK+Sd#*K&$#2SJK3#$%#)S@J$#S3&SXs);)SKO&#Q$%#'CSeR'CSKSJ($#*Se&SK#$#SJ&SJs(y$#SK,%#,)#k#%s)'#k#&.#k#'3#k#(6#k#)>#k#*s#$#k#+s#(#k#,s#,#j#-C#$ES1/S1SB($#*S('C#E7#)S3Sd+S?#$E#)SXS3+S1#*S31$#'C#E)S2SX+S(#*SX&$#2S2SX3#$%#)SJS2$#Sd*SJ&S3#)S@SJ&#Q$%#*S@/E#$$s)[($#VSyS@S2'CS@S27#F$#7s#8Fs#9#'CS4S4'CSeS@($#*S4&Se#$#S@&S@%$#Se,%#,)#j#$-#)SYSL+H#*SL&$#2SYSL3#$%#)SfSY+I#*SY1$#'C#E)S)Sf+S##$E#*S)&N#)S5S)&#Q$%#)SMS5$#K'CSMSM'CS5J($#*SM&S5#$#J&J%$#S5,%#,)#k#'-#k#&0#k#*6#k#):#k#(@#j#.C#)SLSZ+S4#*SZ&$#2SLSZ3#$%#+SZs#/1#s#.'C#E+SLs#+$E#*Sf&SY#&s#*Q$$#$s#'Sf'CS5S5'CS)S)($#*S5&S)#$#S),##LCS5LCS)XT,+*$#WT-*&#j#'.#j#&0#j#*5#j#)8#j#(<#_SzCS4s#$#SKHOMRKJj#/s#T#U#Hj#/s$3#7s#W'CSZSZ'CS4SK($#&S4s#)$#SK&SKs#+$#S4,%#1s#/s#.'C#EGs#Vs#+k##$#Gs#2s#3k###s#,WS{s#5s#4SFXS|&$#Sb9Hs#\'Cs#2#j#0C#HC#9Hs#Y'Cs#3#j#0C#HC#&SLs#]$#S4&S4s#_$#SL,%#j##(#+SYs#`9Hs#;'C$#j#0C#U#H+Sfs#`9Hs#c'C$#+SYs#`1#s#;'C#E)SrSM+Sf#Gs#`#k##&#Gs#A)1&s#c'C#Ek##%#WS{-s#ESGXS|($#S89Hs#h'C,#j#0C#HC#)SsSr+S)#*Sr9H#'C%#j#0C#HC#&SM'$#S)&S))$#SM,%#j##(#)StSs+S5#*Ss9H#'C%#j#0C#U#H)SlSt+SM#*St9H#'C%#'COI)SuS[+Sv#*S[9H#'C%#k#1#S6j#2C#)S[Sv+Sl#*Sv9S##'C%#UT.SNMC#<S}<#<#<#<#=C#IC)#=C&=C(.C$#.C&#?#S\IC/'.C#'.C+#?#S\UT/SA@SA$#@SA)#UT0SACCKUT1C:C$S##:C#J$CCNCCJ:C#J':C%I#:C'J#UT2CUT3C>Cs,2%s,5>C#JC%#%%>C#%SN>C#NC%#4C(S7#5-GDDF#LUT4D>Cs,?JC#-4C#S7(52GDDF#L4C&S7254GDDF#LB5GDDF#KCE4C#Sp/58GDDF#LD9GDDFME:GDDF$#4C3S7'5<GDDF#LB=GDDF#D>GDDFR0?GDDF$3#0@GDDF%4#0AGDDF)5#0BGDDF/6#0s##GDDF37#0s#$GDDF98#VT5s#%FLS~T#VT6HS#'S~#T#m$%#WT7CEIXT8HS#$#l#3*)#l#4s#/s#.#l#5s#:s#9#j#6C#j#7C#j#8C#j#9C#j#:C#j#;P#j#<P#+NS#9KH'C$#+S#N9JI'C$#'CNJk###S6/EN(#R'CKEk###S6'CJEk###S6k###S8k##&#k##)#k##,#k##/#k##3#k#6C#k#7C#k#8C#k#9C#k#:C#k#;P#k#<P#*Su$#s,s)T$SuaHS6$KSl#S[%NISOSeSnS>l#=B'#j#1s#w#[T9CS#s#}#MHOj#>s$)#7s$*m#$#VT:MS#/MS#$S#M,$#/RN$NR,$#&S[3$#Sl&Sl5$#S[,%#j##(#/S$K%s-/%#%#%#%#%#%#%#%#%#%#%#%#%#%#################################6#8C#<s$H<#<#<#<#=C#ICs$S#=C&=C(.C$#.C&#ICs$X&=CS}.C$#.C+#-C'#-C3#=Cs$].C-#.C/#-C##-C8##s$=##############################%#%#%#%#%#%#%#%#%#%#%#%#%#################################%###6#8C#6SNMC#MCEXT;C$SN#WT<CSN#VT=C#<s#K=C#-C%#-C,#%s.G####%#%#%#%#%#%#%#%#%#%#%#%#%###%#6#8C#=Cs%T-C<#-C%#-C>s%Q-C'#%s%7%#%#%#%#%#%#%#%#%#%###%#%#############################%#6#8C#-Cs%rs#}-C$#%s/1%#%#%#%#%#%#%#%#%#%#%#%#%#####%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#6#8C#-Cs&9s$H-C$#.Cs#&#.Cs#H#.Cs#K#.Cs#c#.Cs$C#.Cs$I#?#S\#s#d##########################6#8C#-C#s$W-Cs$Ys$^-C%#6s%$8C#-C#s#}6s%68C#-Cs&Zs$`-C$#%s&>%#%#%#%#%#%#%#%#%#%#%#%#%#6#8C#.Cs$zs$}.Cs%%#-Cs&n#-C&#.C7#.Cs#~#.Cs$%#.C>#.CB#.Cs#%#?#S\@SA#s&n@SAs#9#CCO:Cs&lO#:C#S#s&n:Cs&jOs&n:Cs&oN#:C%I#>Cs%%4Cs&cSp#5s&jGDDF#L4Cs&eS7%5s&lGDDF#LBs&mGDDF#>Cs%,JCs&g#>Cs0ENC+#4C%S7#5s&sGDDF#L>CSNJC#)NCs&p(4C$S7#5s&xGDDF#L4C'S7s&q5s&zGDDF#LBs&{GDDF#4Cs&hSp.5s&}GDDF#LKCs0C4C1S&#5s'$GDDF#LEs'%GDDF&#4C4S7s&n5s''GDDF#LBs'(GDDF#AC374C#S&s&~5s'+GDDF#LACs'$:4C#S&75s'.GDDF#LOs'/GDDF&#0s'0GDDF*s'$#0s'1GDDF+s'%#0s'2GDDF/s'&#0s'3GDDF0s''#0s'4GDDF7s'(#0s'5GDDF;s')#0s'6GDDFAs'*#0s'7GDDFs#(s'+#0s'8GDDFs#,s',#l#3#s&rs&ll#4s#1s';#l#5s#8s'F#j#6C#j#7C#j#8C#j#9C#j#:C#j#?C#/KJ'CJOk###S6+KJ9MN'C$#+NO9MK'C$#'CKOk###S6/EO$Os0o($#/EM$Ms0r($#'CREk###S6'CS$Ek###S6&S$S*$#S+&S+S*$#S$,%#k##(#k##+#k##.#k##2#k##6#k##9#k##=#k##A#k##s#$#k#6C#k#7C#k#8C#k#9C#k#:C#k#?C#)T>T%*T%cHOS+$S[#T$IKJS*SQS9SZS,Sjl#=s#/&#j#@s&e#U#Hj##s&p#$KS$%s$#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%###############################6#8C#-Cs$@s&U-C$#-Cs&\s&\-C&#%s1_##%#%#%#%#%#%#%#%#%#%#%#%#%#%#6#8C#-Cs&2s&k-C$#-Cs&4s&r-C&#%s%j##%#%#%#%#%#%#%#%#%#%#%#%#%#%#%###%#############################%#6#8C#-C#s&W#s#.6#8C#-C#s&B-Cs&Fs)6-Cs&$#6s#Y8C#-C#s%*.C&#.C)#.C.#.Cs#4#.Cs#7#.Cs#L#.Cs#O#?#S\-Cs%6s'H%s'p##6#8C#-C#s%S#s2T%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#6#8C#-C#s#i#s%R##################################6#8C#-C#s';668C#-C#s&=#s$I##6#8C#-C#s&e.C(#.C,#.CB#.Cs#7#.Cs#=#?#S\@SA#s)w@SAs#A#4Cs%aS&s)e5s)lGDDF#L0s)mGDDF#s)as%8l#3#s)Ks)El#4s%fs)p#l#5(s){#j#6C#j#7C#j#8C#j#9C#j#:C#j#?C#$JKk###s$sk#6C#k#7C#k#8C#k#9C#k#:C#k#?C#l#=+#s$pj#@s$l#U#Hj##s)$#ZT&s)&s)%s(zs$p#Hl#As)+s)(#l#>s)-s).#j#Bs*X#j#CC#V#IHj##s*`#j#DC#YT'Cs*ps*i#Hl#Es*{s*w#j#1s+-#j#2C#V#IHj##s+3#j#DC#YT'Cs+As+:#Hl#Es+Is+E#WT(s+Ws+R#j#Fs+[#U#Hj#Gs,Y#ZT)s-4s,Zs,Ns+_#Hl#$s,_s,\#j#%s,a#j#&s,f#j#'s,l#j#(s,o#j#)s,w#j#*s,}#j#+s-%#j#,s-)#bSzCS1s--#SIHSPS8RKNS<S.SSj#/s-f#U#Hj#/s-k#7s-i'CS1SI(#s-k*S1&S?#$#SH*SI&SH#$#S?,&#CCI4Cs*AS&s&?5s*VGDDF#LDs*WGDDFNEs*XGDDF$#0s*YGDDF#s*M%l#3#s*7s*1l#4)s*\#l#5s*js*g#j#6C#j#;P#(s-sI$EIk##$#k#6C#k#;P#/S(SBWH#S(SDl#=*%#/S?SBWH#S?S^l#=-(#ZT?S(S1SI&#H)S(S16s4A6s4>VT@$#&&#)S(SI$$#&$&$#*,%#)SdS(&#*)SdS?$$#&$-$#',%#*Sd&S(#$#S?$s#3S(,$#j##(#&s-b6)S3S1$$#VTA;:/E<$E</E<k##$#k##&#$EAWTBBAIj##T*#j#H%#$Es##k##T*#k#H(#=Cs)e.Cs+Ms)[.Cs+Q#.C%#?#S\@SA#s+I:Cs'8Js+E:Cs+FN#:Cs+FI#>Cs'XKCs#2UTCs4nWTDC$#AC&#4C#S&s+>5s+EGDDF#L4Cs+2Sps+95s+GGDDF#LEs+HGDDF#s+,4Cs+CS&s+A5s+JGDDF#LDs+KGDDFS$Es+LGDDFs'-##s'f########################################################6#KC#ACs#/#4Cs'FS&#5s+nGDDF#L4Cs+bS7s+[5s+pGDDF#LBs+qGDDF#Ds+rGDDFS*Os+sGDDFs'J#0s+tGDDFs'Ns+h#0s+uGDDF&s+i#0s+vGDDF*s+j#0s+wGDDFs#-s+k#0s+xGDDFs#0s+l#0s+yGDDFs#3s+m#0s+zGDDFs#7s+n#l#3#s+Xs+Rl#4s#@s+}#l#5s#Ds,,#j#6C#j#7C#j#8C#j#9C#j#:C#j#?C#j#;P#j#<P#j#IP#&Ks#w$#J/EK(#M$MK(%S*&KJ&Rs#&$$#'CMEk###S6&MR$#S$,#SQk##&#k##s'D#k##*#k##.#k##0#k##2#k##5#k#6C#k#7C#k#8C#k#9C#k#:C#k#?C#k#;P#k#<P#k#IP#&S3s.{$#S2$s.vs5l$s.~s5m)S@SXdH&%$#s.ws/$S3s.yS2NS=S0S'SWS9S-l#=s#')#l#Js#|s#y#l#Ks$*s$%#j#>s$,#U#Hj##s$:#&s$0s$E$#s/6ACs,Qs#s4C#S&s#w5s,YGDDF#LACs,Rs,MACs,Us#N4C$S&#5s,]GDDF#L4Cs#}S&s(H5s,_GDDF#L4C(S&s(J5s,aGDDF#LOs,bGDDFs#N#0s,cGDDFs(=s,W#0s,dGDDFs#Qs,X#0s,eGDDF(s,Y#0s,fGDDFs#xs,Z#0s,gGDDF,s,[#0s,hGDDFs#~s,\#0s,iGDDF2s,]#l#3#s,Gs,Al#4s$/s,l#l#5s$3s,w#j#6C#j#7C#j#8C#j#9C#j#:C#j#?C#j#;P#j#<P#j#IP#&Js$f$#K&Ms#l$s#J#$RK$s(&M,SQ#k##s#J#k##s(,#k##'#k##s#R#k##*#k##s#V#k##.#k#6C#k#7C#k#8C#k#9C#k#:C#k#?C#k#;P#k#<P#k#IP#&S2s/\$#S3dH#s#Fs#Es#Ds/\s/eS3s/^S2NS=S/S'SkS9S-l#==&#l#Js$as$^#l#Ks$ks$f#j#>s#?#U#Hj##s$y#ZT&s$|s$zs$ss#D#Hl#As%/s%%#m##s%GWT(s%Os%H#j#Ls%R#U#Hj#Gs0a#ZT)s0cs0bs0Vs%V#Hl#$s0hs0e#j#(s0j#j#)s0q#V#IHj##s0x#j##s14#;s15s11s1$#Hj#>s1;#j#*s1E#V#IHj##s1J#j##s1i#;s1js1bs1U#Hj#>s1n#j#+s1z#V#IHj##s2##j##s2G#;s2Hs2=s20#Hj#>s2L#j#,s2[#V#IHj##s2`#j##s3-#;s3.s2|s2p#S-j#Ms32#j#Ns3:#V#IHj##s3A#j##s3X#;s3Ys3Us3I#Hj#>s3_#j#Os3j#V#IHj##s3o#j##s41#;s42s4*s3z#Hj#>s46#j#Ps4C#V#IHj##s4H#j##s4k#;s4ls4as4U#Hj#>s4p#j#Qs5$#V#IHj##s5)#j##s5T#;s5Us5Fs59#Sgj#%s5Y#j#&s5]#V#IHj##s5d#j##s5x#;s5ys5vs5i#Hj#>s6##j#'s6+#V#IHj##s6/#j##s6H#;s6Is6Es68#Hl#>s6Us6L#j#Rs6W#j#Ss6\#V#IHj##s6c#j##s6u#;s6vs6ss6h#Hj#>s6|#j#Ts7*#V#IHj##s7.#j##s7I#;s7Js7Bs77#Hl#>s7is7M#j#Us7k#j#Vs7m#j#Ws7o#j#.C#j#-C#j#XC#j#YC#j#ZTE##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mult_below : forall s x y, 0 < s -> x mod s = 0 -> y mod s = 0 -> x < y -> x + s <= y.
Proof.
  intros s x y Hs Hx Hy Hlt.
  destruct (proj1 (Z.mod_divide x s ltac:(lia)) Hx) as [q ->].
  destruct (proj1 (Z.mod_divide y s ltac:(lia)) Hy) as [q' ->].
  assert (q < q') by nia. nia.
Qed.

Lemma carved_of_elem : forall st c cp, WF st -> 0 <= c < kNumClasses ->
  0 <= cp -> Z.shiftl cp kCompactPtrScale < rg_allocated_user (get_region st c) ->
  class_size c <> 0 -> Z.shiftl cp kCompactPtrScale mod class_size c = 0 ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st c cp W Hc A B C D. rewrite shiftl4 in *. rewrite compact_to_addr_eq. unfold carved.
  replace (region_beg st c + cp * 16 - region_beg st c) with (cp * 16) by lia.
  pose proof (class_size_table_facts c Hc) as T. pose proof (ro_alloc_mod _ _ (WF_region st c W Hc) C) as AM.
  repeat split; try lia. apply mult_below; lia.
Qed.

Lemma carved_free : forall st c cp, WF st -> 0 <= c < kNumClasses -> In cp (rg_free_array (get_region st c)) ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st c cp W Hc Hin. pose proof (ro_fa_elems _ _ (WF_region st c W Hc) cp Hin) as (A & B & C & D).
  apply carved_of_elem; assumption.
Qed.

Lemma carved_cache : forall st c cp, WF st -> 0 <= c < kNumClasses -> In cp (pc_chunks (get_pc st c)) ->
  carved st c (compact_to_addr st c cp).
Proof.
  intros st c cp W Hc Hin. pose proof (co_elems _ _ (WF_cache st c W Hc) cp Hin) as (A & B & C & D).
  apply carved_of_elem; assumption.
Qed.
