(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import DivergeSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop :=
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z /\
  (bv_unsigned a + Z.of_nat n <= bv_unsigned lo
   \/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned a)%Z.

(* [comment removed for export] *)
Definition accesses_outside_lazy
    (accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
  forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
    access_outside_range a n lo sz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_all_false {A} : forall (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
  intros f l H; induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim tm]. reflexivity.
Qed.

Lemma materialize_accesses_no_new : forall lazy materialized used limit accs,
  newly_materialized_pages lazy materialized accs = [] ->
  materialize_accesses lazy materialized used limit accs = Some materialized.
Proof.
  intros lazy materialized used limit accs Hnew.
  unfold materialize_accesses. rewrite Hnew. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

(* [comment removed for export] *)
Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages];
    intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
        as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k.
      split; [right; exact Hin | split; assumption].
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.

(* [comment removed for export] *)
Lemma page_in_ranges_outside : forall lazy (a : word) (n k : nat),
  (k < n)%nat ->
  (forall lo sz, In (lo, sz) lazy -> access_outside_range a n lo sz) ->
  page_in_ranges (page_base_of (bv_unsigned a + Z.of_nat k)) lazy = false.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.lt); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyFrame.access_outside_range); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.Bool.Bool.not_true_is_false); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_base_of); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); (KReplay.sort_at constr:(@Stdlib.Lists.List.partition) [0]); constr:(@kc__1); constr:(@Stdlib.Lists.List.existsb); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.existsb_exists); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Init.Datatypes.fst); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@Corelib.Init.Datatypes.snd); constr:(@kc__2); constr:(@Corelib.Init.Logic.False); constr:(@kc__3); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.or); constr:(@stdpp.bitvector.definitions.bv_unsigned_in_range); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@stdpp.bitvector.definitions.bv_modulus); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.div_pos); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@stdpp.bitvector.definitions.bv_wrap_small); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.X); constr:(@kc__3 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))))); constr:(@kc__2 ((@Corelib.Init.Datatypes.prod) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))))))|] [|@sz; @lo; @x; @l; @f; @A; @r; @p; @b2; @b1; @m; @n; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @H4; @H3; @H2; @H1; @H0; @H; @__sat1; @__sat2; @cstr0; @cstr; @Hk0; @heq_z; @z; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @q; @__sat3; @__sat4; @__p1; @Hhi; @Hlo; @Hpb; @Hmb; @Hdm; @Hq0; @Hz0; @Hsz_rg; @Hlo_rg; @Hdisj; @Hnw; @a0; @Htest; @Hin; @b; @Htrue; @Hout; @Hk; @k; @a; @lazy|] "#/c#q%#$&$]$B##$^$\#$$+$,$6#%$d#&$b$9#)#'#+#*#,#-#H#(#.#I$N#3#D#F#G$l#M#4#1#5#9#z#K#P$T#O#y#2#A#@#{$%$C#6#=#B#C#E$H#R$p$n$t#L#Q#:$-#0#7$A$K#N#T#W#X#V#Y#Z$S#\$x$y#S#U$z${$|#[#k$}#l%+#J#n#q#w#v#u#~$($2#/$;$=#;$>$D$J$L$U$X$Y$[$e$g$i$j$h$k$o$v#h#i#j%#$~%$%(#m#^#_#?$w%)%*$u#]%,%-#o#p#a#b$:$8$'$<$$$#$*$1$4$`$_$Z$)$.$P$r#x$m$s#|$3$f$E$R$Q$V$c$I#}$0$5$7$@$O$M$W%&%'#t$/$?$G$F$a$q%%R$T%$U%$V%$W&#R%$X%#Q$$Y%$Z'$[*$\+$]$$^($_&$`%$a$$b%$c%$d&$e%$f&$g%$h$$i%$j'$k%$l$$m'$n%$o&$p&$q%$r%$s&$t%#P%$u$$v&$w$$x&#&&$y$$z/${'$|%$}$$~*2S<2#2#2#2#2#USm#USn#VSo##I#FFI>&&IF5&#RXSpRS)MIk##$#k#$*#k#%+#$-S#)M%$#.FVSq#R&J#Kk##FJIIJMIF&J#K5S#FMUOF&J#K(%#j#&O#?O#k##)#5OFIUMF&J#K(%#j#&M#?M#JOMI&J#Kk##%#(,#5S)FOUS#F&J#K(%#j#&S##?S##k##+#j##*#JS#OM&J#Kk##8#j###Ij##9#WSrMIF/;2)$#j#'s#%#j#(s#'#j#)SP#k#'s#(?k#(s#*#k#)SP#@s#<s#<F$s#>#.O$s#@#*%#%$LAs#Bs#BF$s#D#%)#*&#6(#j#*s#F#XFs#G#S$I5s#HFS&&J&K($#j#&s#K#?s#L#5s#MFS'.S#$s#Q#*6#%$L*#16%#&J#K(*#j#&s#V#?s#W#j###Q5s#YFS*.S)$s#]#*B#%$L*#=6%#&J#K(*#j#&s#b#U#F5s#dFSQ.S%$s#h#*s#-#%$L*#s#(6%#&J#K(*#k###Qj#+s#n#5s#os#lS-@s#qs#qs#m$s#s#.S'$s#u#*%#%$LAs#ws#ws#s$s#y#%)#*&#6(#&J#K(/#>s#~s#~MI5s#~#S3@s$$s$$$$s$&#.S*$s$(#*%#%$LAs$*s$**$s$,#%)#*&#6(#&J#K(/#j###Q>s$2s$2OM@s$3s$3#$s$5#.Ss$s$7#*%#%$LAs$9s$9)$s$;#%)#*&#6(#&J#K>s$?s$?S#O5s$?#SC>s$As$AS)S#@s$Bs$B#$s$D#.S4$s$F#*%#%$LAs$Hs$H)$s$J#%)#*&#6(#&J#K6IF&J#K&JMK&JIK($#k##&#&JFK(&#6MI&J#Kk##%#((#&JOK(#-k##'#j##&#6OM&J#Kk##0#j###Ij##1#VStIF/3.)$#j#,J#j#-J#k#,J6k#-J#$s$jS%.S-$s$l#*%#%$L$s$oR%(#*%#K'#I&J(K&J%K($#$s$vS$.S3$s$x#*%#&J#K%%L%(4*$#&J#K('#j###Q.S5$s%&#%#L$s%(S&%#1*%#&J#K$s%,S'.SC$s%.#*%#&J#K.SR$s%2#%#L$s%4S*%#+*%#&J#K*IF&J#K#MIk##$##IF*MI&J#Kk##%#('##OMk##&#j##%#*OM&J#Kk##.#j###Ij##/#VSuIF/1-)$#j#.C#j#/C#k#.C4k#/C#$s%OSQ.S6$s%Q#K%#M#&$.Sv$s%U#%#L$s%WS=$s%XS4%$#K&#O#'$WSDS-S=S*$s%]S>)S?%$#Ls%fLs%bVSw$##&#$s%dS-#(#%$1##,B%#((#$s%jSE)S>%$###-$s%nS3#%#%$.##)B%#((#j###Q$s%uSF)SE%$#$s%xS5#$#%$.##(B%#$s%}S.)SF%$###@$s&%SG)S.%$#$s&(SR#$#$s&*SC%%###)B&#VSSs&.S/$s&/S/#E#USxs&1'%#(%#VSSs&4S6$s&5S6#E#'$(($#$s&9S+)S0%$#8C#&CS.$m#$#FS(S+)S()S+'$#8C%8C%MS7CS@SASBSHS('$S+&#N)&#S0=S+#E)=S8)S8#E#VSys#Js#I'Es#K#Es#K'Es#Kk##$#k##&##Es#PWSzs#Qs#PIj##ST#j#0%##Es#Rk##ST#k#0(#$s&YS?#E#'$s#,($#$s&]S9)SU%$##E#j##'#'s#cs#3#Es#W's#Ms#5#Es#B's#Cs#7($#$s&hSV)SI%$##E#j##'#$s&mS0#E#$s&oS('#s#A$s&qSW#E#'$s#D($#$s&uSX)SY%$##E#j##'#''s#K$s&{SZ#E#$s&}S['#s#O9S\9#:C#:C%:CS\0C$#0C&#C#S:US{S,DS,$#IS,ECMUS|C;C$I#US}CUS~COCE<Cs':+C$P#,&HDDG#NUT#D<CS<+C(P#,*HDDG#N7C%)+C+P#,-HDDG#N-.HDDG&)#-/HDDG+*#VT$0G8JKVT%FM&J#Km$%#WT&CEIXT'FM$#l#1*)#l#2:9#l#3?>#j#4C#j#5C##EI%MO#E#k##%#k##&#k#4C#k#5C#)S[$s'TS]XF$#S-Ml#6-&#j#7s#7#j#8s#:#V#IFj##s#>#j##s#G#/s#Hs#Gs#A#S-j#9s#K#j#:s#N#V#IFj##s$0#j##s#Z#/s#[s#Zs#T#S*j#;s#]#j#<s#_#V#IFj##s#b#j##s#k#/s#ls#ks#e#Rl#=s#rs#o#l#>s#|s#w#l#?s$$s#~#l#@s$'s$&#l#As$)s$-#l#Bs$2s$3##ES.m#$#2s'r2#2#2#2#2#L#OC#+Cs#HS1#,s#JHDDG#Nl#1#s#=s#7l#2s#Os#M#l#3s#Ts#R#'E)l#6$#F'ELm#$#XT(SGLF#3SGL#E#+C/SJs#T,s#VHDDG#NZT)s#WHDDG#l#1#s#Js#Dl#2s#\s#Z#l#3s#as#_#&C6Ek###Ql#6%#F&CLEP#m#%#WSKS/L#3S/L1L#4S/L%$#&CS/#WSLS0L84S0L#E#'$L($#3S(L1#LVT*s(B#3S+L1#L&CF#j#CC#$s(GS2%#s$\8C#&CS($m#$#FSMS2)SM)S2'$#8C%8C%MS7CS@SASBSHSM'$S2&#N)&#S8=S2#E)=S;)S;#E#$s(YSN%#%WS^#s#BS%#Es#C$s(]SI)S9%$#4#s#G#E#k##(#WS_&s#JS$$s(dS`)SN%$#3#s#N#E#k##/#$s(jSa)S`%$#VSK#s#TPs#A$s(oSY)SV%$#3#s#Y1s#Z#4%s#[%$#&C'#k##+#VSL)s#_)Sa%s$g#4#s#b#E#'$s#d($#k##s#_#VSb(s#g's#hE4s$is#i's#j##$E($#k##'#VScs$ns#n)SW%s$l#3#s#q&C#Ek##s#_#VSd&s#t)SX%s$p#4#s#w&C#$k##s#e#3&s#z$s)8Se)SZ%$#4#s#~#EF'Fs$$($#1Ms$&#E#'$s&=($#j##'#'Is$+#EM'Os$-#Es#L's#Ms%u($#1Rs$1#E#'$s&H($#j##'#'s#Ps%|#Es#J's%Gs%~#Es#A's#Bs&$($#1S's$<#E#'$s&S($#j##'##Es%C's%>s&,$s)\T+#E#'$s&/($#1S4s$G#E#'$s&^($#j##'#$s)eT,'#s&7$s)gT-#E#$s)iSf'#s&;9s%I9#9#9#9#9#9#9#:C#UT.S<VT/C#:C(WSgC$#:C-:C00C#s%U0C%#0C'#0C,#C#S:0Cs%Z+C#S:VT0s%\#DS,#s%YDS,'#ECS%;C#S#s%XECR;C$M#ECS$;C#S)s%\;C#Os%];C&I#Gs*5<C#+Cs%]P#,s%_HDDG#N+C%S1s$v,s%aHDDG#NQs%bHDDG%#-s%cHDDGs$ws%^#Gs*><C#<Cs*>7C$#HCs$~s%b7C#.+C%SJ#,s%kHDDG#N-s%lHDDGs$ss%g#+Cs%lPs%',s%nHDDG#N-s%oHDDG#s%js%g+Cs%oP,,s%qHDDG#NGS<2#<C#+C1S1#,s%vHDDG#N7C4%OCs'JWT1C#s*M+C%P#,s%{HDDG#N<C,7C#s%7<Cs*W7Cs%}#+C%P#,s&%HDDG#N+Cs&$P(,s&'HDDG#NHCs%~s%>+Cs&(P#,s&*HDDG#N+C%S10,s&,HDDG#NQs&-HDDG%#-s&.HDDG)s&)#-s&/HDDG,s&*#-s&0HDDG3s&+#-s&1HDDGs&-s&,#-s&2HDDG:s&-#-s&3HDDG@s&.#-s&4HDDGs##s&/#-s&5HDDGs#'s&0#-s&6HDDGs#1s&1#l#1#s&)s&#l#2s#;s&9#l#3s#Ds&>#j#4C#j#5C#j#DC#j#EC#j#FC#j#GC#j#HC#j#IC##ES$'S$s%Z($#k##s%U#%RS$1s%^M%#S&&C%#k##s%L##EOk##s$~##ES&'S'S&#ER%S'S*##s'}%S&s%i%S$S'#$##S&S'1S&s%m#E#'$s((($#k##'#k##)#k##-#k##0#k##2#k##4#k##6#k##9#k##?#k#4C#k#5C#k#DC#k#EC#k#FC#k#GC#k#HC#k#IC#)Sf)Sh$s+AT2$s+BT3%$&.#$s+E#$s+FT4eFS3*)('$#S5S6SOSDS?S>RS8S;SNl#6s#5,#j#Js$=#j#Ks$@#V#IFj##s$D#j##s$N#/s$Os$Ns$H#S.j#Ls$R#j#Ms$T#V#IFj##s'=#j##s$_#/s$`s$_s$Y#T5j#Ns$b#j#Os$d#V#IFj##s$g#j##s$p#/s$qs$ps$j#SOj#Ps$s#j#7s$u#V#IFj##s$x#j##s%%#/s%&s%%s${#S=l#*s%(C#l#Qs%-C#l#8s%4s%/#l#9s%;s%6#l#:s%Cs%=#l#;s%Ls%E#l#<s%Xs%N#l#=s'qs'n#l#>s'{s'v#l#Rs%es%_#l#Ss%ns%g#l#?s%ts%r#l#@s%ws%v#l#As%ys%}#l#Bs&&s&'#3S(s&W1#s&X#E#'$s(o($#m#(##Es&7's&8s(s($#m#&#WT6s+zs&;#VT7s+{s&<$s+|#VT8s+}s&>ZT9Cs&>s&:&$#.S($s,$#&C#s&Bm#&#.S+$s,(##s)*Fj#CC#ZSiC%#S=s&EF#s(1s&F.Sj$s,.#%FL%s)$s)1#$#j#CC#3SjL1#LZSiC)%S4#I%$L%s)8s(<#$#8Cs(8&CS8s(9m#$#FS;S9's&Ds&=8Cs&E8Cs&?MS7CS@SASBSHS;s&G$S9s&@#N'&#SU=S9#Es&C=SI#Es(:WS^s(:s'-S'4s&9s'.#E#k##s&K#WS_s&<s'1S*#Es&7k##s&N#VSKs(4s'41s'5s%~4s&$s'6%$#&Cs&&#k##s&B#VSLs&(s':#Es%~'s&#s'<($#k##s'7#VSbs&'s'?'s'@s%|#s%}E($#k##s&9#VScs&%s'D%s'hs'i3#s'F&C#Ek##s'4#VSd&s'I$s,cT:)Se%$#4#s'M&C#$k##s';#3&s'P)S]%s$+#4#s'Sj##s&1Q#Es(d(#s%|j###Q's&es)B(s(Ts%uj###Q#Es&>'s(#s)F#Es%k(#s%kj###Q$s,ySh'#s)K#Es$<$s,|Sk'#s)N:Cs%n:Cs%q0Cs(]s(\0C$#0Cs%h#0C'#C#S::Cs%tWSgCs%os%l0Cs(ds(b0Cs%m#0C%#0C'#C#S:DS,#s(cDS,+#;Cs%gMs(aECS);C#Os%h;C%I#+Cs%ZS1s'x,s(cHDDG#NQs(dHDDGs%Q#-s(eHDDGs'ys(`#Gs%R<C#7Cs%H#HCs(#s(g7C#s%b+C%SJ#,s(lHDDG#N-s(mHDDGs'ts(h#+Cs(mP),s(oHDDG#N+C+S1s%i,s(qHDDG#N7Cs%Rs%k+C#Ps(m,s(tHDDG#N7Cs(os%W+C#Ps%V,s(wHDDG#N[T;s(xHDDG&#HCs(ws(37C#s(4+C#P(,s(|HDDG#N+Cs(wP&,s(~HDDG#NZT<s)#HDDGS&-s)$HDDG$s({#-s)%HDDG's(|#-s)&HDDG,s(}#-s)'HDDG4s(~#-s)(HDDG7s)##-s))HDDG:s)$#-s)*HDDGs##s)%#l#1#s(ys(sl#2s#)s)-#l#3s#.s)2#j#4C#j#5C#j#DC#j#EC#j#FC#j#GC#j#HC#j#TSl##ES%'S%s(N($#k##s(I#%S)S%1s(RO%#S$&C%#k##s(@#'S$S%%S%S$##S#%S#R##S%B%#%s'-s(\##.1S%s(^#R#k###S4k##&#k##)#k##/#k##9#k##2#k##8#k#4C#k#5C#k#DC#k#EC#k#FC#k#GC#k#HC#k#TSl#)Sk)T=$s..T>$s./T?$s.0T@cFQS3'&%$S5#S6SOS?S>S2SFS.l#6s#+)#j#Js#p#j#Ks#s#V#IFj##s#v#j##s#{#/s#|s',s#z#S0j#Ls#~#j#Ms$$#V#IFj##s)x#j##s){#/s)|s'As$)#SEj#Ns**#j#Os'L#V#IFj##s$/#j##s$3#/s$4s'Qs$2#SDj#Ps']#j#7s'_#V#IFj##s'b#j##s'k#/s'ls'ks$;#S5l#*s$=C#l#Qs$AC#l#8s$Is$C#l#9s$Os$K#l#:s$Us$Q#l#;s$[s$W#l#<s$bs$]#l#=s*[s*X#l#>s*es*`#l#Rs$hs$f#l#Ss$ms$j#l#?s$ps$o#l#@s$ss$r#l#As$us$y#l#Bs$|s$}#m##Qm##Ql#Us%)s%&#l#Vs%4s%3#l#Ws%:s%;#l#Xs)&s(~#l#Ys)-s)(#l#Zs)=s);#l#[s)Ps)Q#l#\s+1s+-#l#]s+2s+.#l#0s+9s+4#j#^s+;#j#_s+E#V#IFj##s+K#j##s+[#/s+\s+Ws+U#Fl#`s+ns+a#l#Us+qs+p#l#<s,$s+~#l#Vs+{s+z#l#<s,&s,$#j#Us,<#j#Vs,D#V#IFj##s,K#j##s,Y#/s,Zs,Vs,T#Fl#as,cs,`#l#<s,os,m#j#as--#j#bs-;#V#IFj##s-?#j##s-[#/s-\s-Ps-N#Fj#<s-_#j#$s/##j#%s/$#V#IFj#cs/&#j#cs/'#YTAs/(s/(s-s#Fj#&s/(#V#IFj##s.%#j#&s/+#YTBs/,s.4s.2#Fl#ds.Ds.?#l#<s.Us.R#j#ds.}#Ps.~m#$#VTCs/%#l#Cs/(C#j#es/,#j#fs/3#j#gS7#j#/S7#j#hs/9#j#is/8##"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem materialize_model_accesses_disjoint : forall m accs,
  accesses_outside_lazy accs (m_vm_lazy m) ->
  materialize_model_accesses m accs = Some m.
Proof.
  intros m accs Hout.
  assert (Hnew : newly_materialized_pages
                   (m_vm_lazy m) (m_vm_materialized m) accs = []).
  { unfold newly_materialized_pages. apply filter_all_false.
    intros p Hp.
    destruct (accesses_pages_in accs [] p Hp)
      as [[] | (a & n & k & Hin & Hk & ->)].
    rewrite (page_in_ranges_outside (m_vm_lazy m) a n k Hk).
    - reflexivity.
    - intros lo sz Hlz. exact (Hout a n lo sz Hin Hlz). }
  unfold materialize_model_accesses.
  rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m)
             (vm_backing_used m) (vm_limit (m_vmmaps m)) accs Hnew).
  cbv iota beta.
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_disjoint : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros segs ms model ms' ranges Hstep Hout.
  rewrite (mi_account_step_of_accesses segs ms model ms' ranges Hstep).
  rewrite (materialize_model_accesses_disjoint model ranges Hout).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ts_spin_disjoint : forall segs ms model ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  to_spin segs ms model.
Proof.
  intros segs ms model ranges Hsvc Hstep Hout.
  apply ts_spin; [exact Hsvc|].
  exact (mi_account_step_disjoint segs ms model ms ranges Hstep Hout).
Qed.

(* [comment removed for export] *)
Lemma ts_step_disjoint : forall segs ms model ms' ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  to_spin segs ms' model ->
  to_spin segs ms model.
Proof.
  intros segs ms model ms' ranges Hsvc Hstep Hout Hspin.
  exact (ts_step segs ms model ms' model Hsvc
           (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
           Hspin).
Qed.
