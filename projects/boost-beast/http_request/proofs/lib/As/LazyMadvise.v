(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  Scfg SimInv ExitSim PropExec CatSim MmapSim AllocSim RelSpec
  ShapeAlg Nodes AgentNodes Gap04 RefNodes SReach AllocNodes
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Common.Cfg Require RomBase.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_233 : forall i m o,
  bv_unsigned (in_sysno i) = 233%Z ->
  syscall_spec i m o <-> madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
Lemma injected_arm_none_233 : Run.injected_arm 233 = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_b_int32 : forall w : word,
  (bv_unsigned w mod 2 ^ 32 = 4)%Z -> madvise_dontneed_b (int32 w) = true.
Proof.
  intros w H. unfold madvise_dontneed_b, int32, abi_low32, MADV_DONTNEED. rewrite H.
  apply Z.eqb_eq. reflexivity.
Qed.

Lemma madvise_dontneed_b_lit : madvise_dontneed_b (int32 (Z_to_bv 64 4)) = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_outcome : forall addr len advice i m o,
  (bv_unsigned addr mod page_size = 0)%Z ->
  madvise_dontneed_b advice = true ->
  w_is0 len = false ->
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ < two_pow_64)%Z ->
  madvise_dontneed_ok (m_vmmaps m) addr n = true ->
  madvise_spec addr len advice i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next m addr n) [].
Proof.
  intros addr len advice i m o Hal Hadv Hlen. cbv zeta. intros Hnw Hok.
  unfold madvise_spec. rewrite (proj2 (Z.eqb_eq _ _) Hal), Hadv, Hlen. cbn [negb].
  rewrite (proj2 (Z.leb_gt _ _) Hnw). rewrite bind_get_model. cbv beta zeta. rewrite Hok.
  sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_next_sbm : forall m addr n, same_but_materialized m (madvise_dontneed_next m addr n).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_lazy : forall m addr n, m_vm_lazy (madvise_dontneed_next m addr n) = m_vm_lazy m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_materialized : forall m addr n,
  m_vm_materialized (madvise_dontneed_next m addr n)
  = List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized m).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_vmmaps : forall m addr n, m_vmmaps (madvise_dontneed_next m addr n) = m_vmmaps m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_halted : forall m addr n, m_halted (madvise_dontneed_next m addr n) = m_halted m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_eager : forall m addr n, eager_used (madvise_dontneed_next m addr n) = eager_used m.
Proof. intros m addr n. apply same_but_materialized_eager. apply madvise_dontneed_next_sbm. Qed.

(* [comment removed for export] *)
Lemma apply_effect_mem_zeros_ret : forall ms r a n,
  ms_mem (apply_effect ms (mkEffect r [] [(a, n)])) = zfill a n (ms_mem ms).
Proof.
  intros ms r a n. cbn. apply functional_extensionality. intros x.
  unfold zfill, zmem, zeros_cover. cbn.
  destruct ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.

Local Lemma u64_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. exact Hz. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.

(* [comment removed for export] *)
Lemma region_free_maps_subtract : forall X (a n : word) (lo hi : Z),
  entries_nowrap X -> region_free X a n = true -> region_free (maps_subtract X lo hi) a n = true.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.entries_nowrap); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.region_free); constr:(@Corelib.Init.Datatypes.true); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@kc__2); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.entry_nowrap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyLedger.entries_nowrap_cons); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Corelib.Init.Datatypes.negb); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.iv_overlap); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.Bool.Bool.negb_true_iff); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.RelSpec.word_unsigned_range); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.two_pow_64); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.Bool.Bool.andb_false_iff); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@kc__3); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.ltb_spec); constr:(@Corelib.Init.Datatypes.BoolSpec); constr:(@Corelib.Init.Datatypes.app); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.or_intror); constr:(@Stdlib.ZArith.BinInt.Z.min_spec); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Logic.or_introl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.u64_small); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.Bool.Bool.andb_true_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.iv_subtract); constr:(@kc__1 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH))))))))))|] [|@hi; @lo; @n; @a; @X; @HF; @HX; @l; @p; @e; @b2; @b1; @b; @y; @x; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__p1; @__arith; @__sat4; @__sat3; @D; @H; @H1; @C2; @C1; @z; @__x4; @__x5; @__x6; @__sat5; @z3; @H3; @H0; @b0; @R1; @L1; @NOV; @HT; @Rs; @Rb; @H2; @Hb; @IH; @s|] "#1l#U$c#_$4#b$5$3###$#d#s#%$<#&#'#($-#A$:#B$V#U#)#*#8#w#5#;#G#F#@#/$>$Y#+$G#,#.#C#-#6#9#:#<#|#D#0#3#4#H#M#]#2#1#7#=#>#?#g#E$9$?#L#N$^#X#f$'$)#I$U$[$a$d#[#Z#Y#n#p#t#u#z#~$%$&$($*$,$+$0$2$=$@$B$C$A#K$D$$$E#J#O#S#T#P$`$_$b$N#R$e#h#^#a#y#l#v#{#x$#$7$6#i$K#c#}$1$R$X$H$Q#`#o$I$M#j#k$J$L#r#q$.#e#\$8$S#m$;$F$T$]$/$W$P$Z$O$\$cU$6&$7%$8%$9%$:%$;%$<%$='$>*$?&$@%$A&$B%$C+$D&$E*$F&$G%$H$#(&$I%$J%$K)$L'$M($N%$O%$P'$Q$$R'$S&$T$$U%$V%$W$$X&$Y%#D&$Z$$[%#(%$\%$]*$^%$_&#(-$`&$a&#(+$b%BSDB#B#B#B#B#US[#US\#VS]##USR#5O.PON#E#JAS'NL.#PO#E#Jk##&#k##)#k#$C#k#%C#k#&/#k#'0#j#(/#USS15#.$ON#E#JVSKEJj#)$#j#*'#j#$C#j#%C#j#&;#j#'<#,<S'P5#,>S(S'.#ON#E#J,AS3S(A#NL.#PO#E#Jk##'#k##+#k#$C#k#%C#k#&s#*#k#'s#+#k##>#k#+s#+#j#,s#-#:s#/s#/S(S',s#/#P5#:s#2s#2S3S(,s#2#S'.#ON#E#J,s#5IH5#EL5I%$#k##&#EI5H%$#,s#>LI5#k##%#%)#EN5L%$#k##(#j##'#,s#GNL5#k##2#j###Ij##3#VS^IH;5/)$#j#(s#M#j#-s#O#k#(s#O8k#-s#Q#:s#Ss#SS8S56#S3LE$5S3%$#:s#Xs#XS6S8E#5S5%$#:s#\s#\S0S6,s#\#S8A#S'P.#S3S(#E#Jj##(#5S8:s#cs#cS?S0E#5S07IH#E#J#ELJ#EIJ%$#k##&##EHJ%&#7LI#E#Jk##%#%(##ENJ%#-k##'#j##&#7NL#E#Jk##0#j###Ij##1#VS_IH;3.)$#j#.E#j#/E#k#.E6k#/E#>S0S6S@SE?#.SFS0S66$#S(#E%J#E%J%$#>S?S0SAS@?##E#J.SES?S0#E#J%%#:s$2s$2S+SA,s$2#S@A#S0S6.#SFS?#E#Jj##(#.S@SFS?#E#J>SESFS9S+?##E#J.S+S@SE#E#J?H#E#J#EIKk##$##EHK?I#E#Jk##%#%'##ELKk##&#j##%#?L#E#Jk##.#j###Ij##/#US`H;1-)$#j#0E#k#0E3>S+SAS:S)K#L#E$KUSaS;(s$YS;&S*#$$Sb%$#ZS:S)SGS9S+S8OAS;S9S+.#S)SG#E#J(s$aS:(s$bSH(s$cS<'$#$&#(s$fS)'(#$(#%&#(s$jSI'#+$5#'6.$&#%%#j###S=(s$qSJ(s$rS,'#<$%#(s$uS/'#'$6#(s$xR$#7#Es#qK/s#4s#;k##$#/s#=s#;#Es#mKk##$#%&##ENK/#s#;k##'#j##&##Es#lKk##-#j###Ij##.#VScIH;0-($#j#.E#j#/E#k#.E3k#/E#(s%3S7(s%4S$'$#)s###'s#$s#+)'#6%#S5#E&K#E%K/$#(s%=S>'#-)s#(##E#K)&s#)#E#K/%#j###S=(s%ESL'#+)s#-##E#K)IH#E#K&ILk##$#&HI)LI#E#Kk##%#%'#&LNk##&#j##%#)NL#E#Kk##.#j###Ij##/#VSdIH;1-)$#j#1C#j#2C#k#1C4k#2C#(s%`S-(s%aS.'$#6s#2#I&$s#3USTs%kUSTs%gVSe$#$S*%&S*%VSf'&$S*#k##%#k##'#&S*+WSg,+Ij##SU#j#3%#&S**k##SU#k#3(#VShS*2VSKSi#m##1UI#USSQUSRQLCLLCN@C$I#USjCUSkCUSMSDCC#CCSDCCs&-FC$#*C&S##+)GDDF#MUSlD*C&S1)+,GDDF#MZSN-GDDFP0.GDDF$&#0/GDDF('#VSm0FVSnHL#E#Jm$s%{#WSoCS*IXSpHL$#l#4)(#l#598#l#6>=#j#7C#j#8C#j#9C#j#:S&#'HI$L#'IL&#Nk###Pk##&#k#7C#k#8C#k#9C#k#:S&#(s&HSB(s&ISq(s&JSOZHS=%$#S6Ol#;1'#l#<s#3s#?#l#=s#;s#8#l#<s#Fs#@#l#>s#Ks#J#l#?s#Rs#P#j#>s#h#U#Hj##s#r#'s$;s$>)s#o##E#K6s#Vs$%I&s$&s#WUSrC@Cs#=N#@C#Is#?CCs&bFCs#;#*Cs#;S##+s#?GDDF#M*C%S1s#=+s#AGDDF#M0s#BGDDF#s#:s#70s#CGDDF&s#;#l#4#s#6s#1l#5,s#F#l#6s#Ls#K#j#7C#j#8C#j#9C#j#:S&#$Hs#.'LN&#Ik###Pk##&#k#7C#k#8C#k#9C#k#:S&#ZHS=s#ss#/s#-S8Ol#;-$#l#<s#]s#i#l#=s#es#b#l#<s#ps#j#l#>s#$s###l#?s#|s#z#j#>s#'#U#Hj##s$>#ZSss$As$?s$=s#-#Hl#@s$Is$F#l#?s$Ss$Q#j#As$g#j#Bs$j#V#IHj##s$o#j##s$x#;s$ys$ws$u#Hj#?s$}#USts$~m#$#Gs%#S)$s%$S)&S)s%%)s%&S)H%$#)s$}S:$s$zS;&S;s${-S<s$a<s$z#8s'9#:s'9s'9S$#,s'9#s'*nE#$##s'9I#%###s'+'s$gs%#)S,#=s$iS,8s'@#-&$8s'B#:s'Bs'B%#,s'B#s'3nE#$##s'B)#%###s'43s'D,#AS/S<S,3s'F$#.#SISH#E#J$s%1S,GS,1$S,2&3S,H$#3)S<s$y$SHs$q&s$rSH-S/s$P<s$m#8s'U#:s'Us'US.#,s'U#s'F=s$USJ8s'Y#'s$Ws$s-#%8s'\#:s'\s'\&#,s'\#s'MnE#$##s'\I#%###s'N3s'^+#AS>S/SJ3s'`$#.#S$R#E#J$SIs$}-Rs$d<s$d#8s'h#>S7S$S-#?#=s$iS/8s'l#-s$i$8s'n#>S7S$%#?#7#H7*##E#Jj#0E#>S$R>;?#7/H#E#Jj#0E#j##s&fs&_j##s&`Hj##s&n#;s&os&j%#s&_j#.E#j#/E#k#.Es&mk#/E##E:J#E5Jj##s&>s&8j##s&9Hj##s&E#;s&Fs&B%#s&8j#0E#k#0Es&D-S$s$D<s%-#8s(0#>S>S7SB#(s(2SV'#H)s%M#)%s%M7$##E#Kj#CC#j##s%ss%mj##s%nHj##s%y#;s%zs%w%#s%mj#.E#j#/E#k#.Es%zk#/E#-S71<s$X#'3#)s%]#Gs%^$$s%_%&&s%`H$#&(s(ISu-S>#<;#'%#)s%J#-SLs$c<(#'s$e#$s%O#&$s%P(s(SSC's#$s$j)$##E#K/s&s#-S.s$l<s$n#'s$n#$s$q##EJKj##s%js%dj##s%eHj##s%q#;s%rs%n%#s%dj#1C#j#2C#k#1Cs%qk#2C#(s(eSP'?s#6-SB$N7#$8$<9%#C#:%%#&(<#C&)%$#/&#(s(qSv-SV#<0#ISWI#I#I#DC#DC%DC'DC)1C$#1C&#1C(#4#S%4%S%,Q#s%f,Q%#LCO@C#Ls%,LCPLCS'@C$N#@C&I#ZSNs%hGDDFS3USMs%hCC#*C#S2s%1+s%lGDDF#M2s%mGDDF'#USMs)9CC#OC#s%n*C#S1s%7+s%rGDDF#M*C+S2%+s%tGDDF#M2s%uGDDF%#Ms%vGDDF+#FCs%u/*Cs%uS##+s%yGDDF#M2s%zGDDFs%=s%sZSXs%{GDDF#0s%|GDDF#s%ts%r0s%}GDDF&s%u#0s%~GDDF*s%v#l#4#s%qs%ll#5;s&%#l#6Bs&*#j#7C#j#8C#j#9C#j#DC#j#EC#j#FC#j#:S&##CPN%S'#-OL&#N#CP$%$#/'#'NS'$I#'OP$L#$Os%J%$#k###S='NO&#Pk##%#k##+#k##.#k#7C#k#8C#k#9C#k#DC#k#EC#k#FC#k#:S&#(s)hSw(s)iSx-SP#$%#(s)lSyP$OSP'&s#Z#PS(S:l#;s##)#l#Gs&Us&a#l#<s&]s&Z#l#Gs&hs&b#l#Hs#]C#l#Is#is#a#6s#ms#l#l#Js#qs#o#Qs#xs#~#j#?s#z#U#H&s#}s&3#EKKVSKEKR$s$(#j#?&#U#HnS4%s$0s$/%#0##s$*I#%$##)$###l#/s$5E#l#Ks$>s$;#6s$@s$O#l#?s$Gs$E#(s*(s$VNs''s$Y$s'(s$Z#Cs$Zs')%$#&s$]s'+#Cs$]s$^%$#/&#USzSDVS{C#WSQC#s#uDCSW1Cs#v#1C%#4#S%Is#{DC#1Cs#y(1Cs#}#1C%#4#S%4%S%1Cs$#-1C/#4#S%,Q#s'',Q'#,Q)#,Q0#@Cs&JLs#}@C#Is')ZSNs''GDDFS'*Cs'%S2s'&+s')GDDF#M2s'*GDDF%#Bs'*CC#OC#s')*C#S1s',+s'/GDDF#M*Cs'-S2%+s'1GDDF#M2s'2GDDF%#Ms'3GDDF+#*Cs'0S#*+s'5GDDF#MVSYCS**C#S1s'5+s'8GDDF#MVSYCs'SWS|C#s*[*Cs'9S##+s'<GDDF#M2s'=GDDF'#*C*S1s';+s'?GDDF#M*Cs'=S#(+s'AGDDF#M2s'BGDDF%#0s'CGDDF(s';#0s'DGDDF1s'<#0s'EGDDF4s'=#l#4#s'8s'3l#5s##s'H#l#6s#&s'M#j#7C#j#8C#j#9C#j#DC#j#:S&##CHL%O#-NI&#L#CH$%$#/'#$LO&S*O$Os'l%$#&S*N$Ns'o%$#k##&#k##*#k##,#k#7C#k#8C#k#9C#k#DC#k#:S&#Ss$zSBs%4s$~OPS0S+l#;:$#l#Gs'ms'y#l#<s'us'r#l#Gs($s'z#l#Hs%JC#l#Is#ds#]#Js%_#9Cs%`s%Ws#hs#g##Es%_Km#$#Ks%a#l#?s%gs%f#=s'LR8s+7#'s'Ns(6-#%8s+:#>S>S7&#=s%hS$-s%G#8s+>#(s+?#'H#)s(Z#)Hs(Z7$##E#Kj#CC#',H)s(`#).s(`7$##E#Kj#CC#'21)s(f#Gs(g$$s(h%&&s(iH$#&=s%gS7-s%K#'$#)s(R#=s'kS>'s'ls%l-#$'%#$s(X#&$s(Y=s%gS.)#s%g#E#K/s){#=s'tSL's'us'v-#$'%#$s'z#=s%^S-Ts%_S-$s%`S-#C%S-%$#&S-s%c#C(s%d%$#/&#=s%[SBWSQCs$?s%T1C#s$84#S%1Cs%X$4#S%,Q#s(Y,Q&#*Cs'wS#s%I+s(VGDDF#M*Cs(US2s%K+s(XGDDF#M2s(YGDDF%#*Cs(XS2s'|+s([GDDF#M2s(\GDDFs%R#Ms(]GDDF&#FCs($s%MOC#s(]FCs(^#*Cs(^S##+s(bGDDF#M*Cs(`S#'+s(dGDDF#M*Cs(+S#s(`+s(fGDDF#M2s(gGDDF%#ZSXs(hGDDF#0s(iGDDF#s(as(_0s(jGDDF*s(b#0s(kGDDF0s(c#l#4#s(^s(Yl#5s%ds(n#l#6<s(s#j#7C#j#8C#j#9C#j#DC#j#EC#j#FC#j#:S&#$NP#CLP%$##CLN%S'#/%#-s%HN'N#$I#'PS'$L#$Ps(7%$#k###S=k###s%Jk##)#k##-#k#7C#k#8C#k#9C#k#DC#k#EC#k#FC#k#:S&#&SCs%HP#SCs%Js%IOs&As%FPS(S:l#;=%#l#Gs)<s)H#l#<s)Ds)A#l#Gs)Os)I#l#Hs#IC#l#Is#Rs#K#6s#Ts&S#l#Js&Xs&V#Qs&_s#]#j#?s#X#U#H&s#[s(vRs%Es#as%Dj#?$#U#HnS4%s#hs#g%#0##s#cI#%$##'$###l#/s#nE#l#Ks#vs#s#6s#xs#}#l#?s',s'*#(s,is$1Ts)$R$s)%R#Cs$8R%$#&Rs)(#Cs$;s))%$#/&#1Cs&Xs%54#S%1Cs%Cs%<4#S%1Cs%?$4#S%1Cs&^s%E4#S%,Q#s)_,Q&#,Q)#,Q,#@Cs)&Ns&Y@Cs)bI#*Cs)\S#s&S+s)`GDDF#M2s)aGDDF#s#g*Cs)`S2s)_+s)cGDDF#M2s)dGDDFs%?#Ms)eGDDF&#*Cs&ZS#s)a+s)gGDDF#M*Cs%4S1s)d+s)iGDDF#M*Cs)fS#s%2+s)kGDDF#M2s)lGDDF%#OCs)hs)k*Cs%:S1#+s)oGDDF#M*C%S#s%8+s)qGDDF#M2s)rGDDF%#0s)sGDDF)s)k#0s)tGDDF/s)l#0s)uGDDF2s)m#l#4#s)hs)cl#5;s)x#l#6>s)}#j#7C#j#8C#j#9C#j#DC#j#:S&#$HN%#s#d#CLH%O#/%#$Os)f-s&KP&S*#$$s*?%$#k##s%/#k##(#k##*#k#7C#k#8C#k#9C#k#DC#k#:S&#Ss$IS-Os'`s'NPS3S+l#;6$#l#Gs*=s*I#l#<s*Es*B#l#Gs*Ps*J#l#Hs$|C#l#Is#Os#H#Js%%#9Cs%&s$ps#Ss#R#(s-^s%)1Cs&(s%~4#S%WSQCs&1s&*1C#s&/4#S%Is&.DC#1C#&4#S%,Qs&-s*M,Q$#,Q)#,Q-#*Cs*GS#s'?+s*LGDDF#M*Cs*JS2s'A+s*NGDDF#M2s*OGDDF%#*Cs*MS2s*L+s*QGDDF#M2s*RGDDFs&-#Ms*SGDDF&#FCs*Ps*R*Cs'IS##+s*VGDDF#M*C%S1s%{+s*XGDDF#M0s*YGDDF#s*Qs%u0s*ZGDDFs#Ls*R#0s*[GDDF's*S#0s*\GDDF+s*T#l#4#s*Os*Jl#5s#^s*_#l#67s*d#j#7C#j#8C#j#9C#j#DC#j#:S&#$IN#CHN%$##CHI%O#/%#&s'7s+$k###s%rk##s%p#k##s'8#k##'#k#7C#k#8C#k#9C#k#DC#k#:S&#]Hs%.S-s(Es(3OPS3S9S/l#;4$#l#Gs*~s+.#l#<s+*s+'#l#Gs+5s+/#l#Hs%aC#l#Is$4s$-#Js%i#9Cs%js%[s#Cs#B##Es%fKm#$#Ks%h#l#?s(xs(w#XS}s)#s(~s%p#6s)<s)6#l#?s)(s)&#7s)2JUSZs)39Es)4s)1%$#.s)JS$R9EJs)8$#S53s.Ms)Vs)O3s.N#s)M.#S$R#E#Jm#'#j#Ls)M#U#H&s+nSI>S$RS.s)`?#j#0Es-J's*pH)s+|#)s*rs+|7$##E#Kj#CC#'s*vs)3)s,&#Gs,'$$s,(%&&s,)H$#&$s+cs(x&s(ys+d)s*|s&2#E#K/s-*#-S-s(vNs+$#$s+%$<s+&%#C#s+'%%#&(s+)#C&)%$#/&#(s.uS~-SCs'l$$#P#OSC%s'ns(qs(ePS(S)l#;s(.s'p#l#Gs+`s+l#l#<s+hs+e#l#Gs+ss+m#l#Hs(qC#l#I4,#6s).s)-#l#Js(|s(z#Qs)':#j#?s)3#U#HRs'h=s'gj#?s)5#U#HnS4%s##B%#0##?I#%$##&$###l#/s)FE#l#Ks#)s#&#6s#+s#0#l#?s)Os)M#(s/0s*&Ns,.s*)$s,/s**#Cs**s,0%$#&s*-s,2#Cs*-s*.%$#/&#Ss#*S-s+Ms)DOPS6SAl#;s'*s&p#l#Gs+}s,-#l#<s,)s,&#l#Gs,4s,.#l#Hs)mC#l#I0)#Js*7#9Cs*8s#@43##Es*7Km#$#Ks*9#l#?s)ws)v#7s#LJUSZs#M9Es#Ns#M%$#9EJs*.#s#ZS53s/Hs*Qs/93s/I#s*H.#S$R#E#Jm#'#j#Ls#W#U#HnS4%s*^s*]%#0##s*KI#%$##s#Z$###l#/s*`E#l#Ks*es*b#j#Ms*g#U#H&S,s-<3s/Us/Fs*V3s/V#s*U.#S$R#E#J#Es*HJj#0E#'Hs%R)s-##)Hs-#7$##E#Kj#CC#'s'/H)s-)#)s'1s-)7$##E#Kj#CC#'s'5s'2)s-/#Gs-0$$s-1%&&s-2H$#&$s,ls&y&s&zs,m)s&os';#E#K/s.3#Ts*#S.$s*$S.#Cs&xS.%$#&S.s*'#Cs&{s*(%$#/&#&SOs(rP#SOs#fs(sOs)vs)jPS(S)l#;s&Fs&.#l#Gs,es,q#l#<s,ms,j#l#Gs,xs,r#l#Hs&{C#l#I1*#6s'*s*2#l#Js*%s*##Qs*,6#j#?s'/#U#HRs(m9s(lj#?s'1#U#HnS4%?>%#0##;I#%$##&$###l#/s'BE#l#Ks#%B#6s#'s#,#l#?s*Ts*R#(s05s+%Ts-4S/$s-5S/#Cs++S/%$#&S/s-8#Cs+.s-9%$#/&#Ss#$S.Os,Rs*IPS(SAl#;s%[s%I#l#Gs-&s-2#l#<s-.s-+#l#Gs-9s-3#l#Hs'kC#l#I0)#Js+6#9Cs+7s#<43#(s0Gs+9]Hs#.S.s,\s*SOPS(S+SJl#;s$~s$n#l#Gs-0s-<#l#<s-8s-5#l#Gs-Cs-=#l#Hs'uC#l#I:3#Js+B#9Cs+Cs#L,+##Es+@Km#$#Ks+B#l#?s+*s+)#9Es+=s$Z#s$is$h9EJs#X#s$gS53s0Us0Fs+W3s0V#s+U.#S$R#E#Jm#'#j#Ls+U#U#H9EJs$cs0Is$oS53s0]s0Ns0N3s0^#s+].#S$R#E#Jm#'#j#Ls$l#U#HnS4%s+ss+r%#0##s#jI#%$##+$###l#/s+uE#l#Ks+zs+w#j#Ms#q#U#HnS4%s,8s,7%#0##s,#I#%$##s#t$###l#/s,:E#l#Ks,@s,<#l#Ns,Bs,C#l#Os.ps.m#XT#S<S,S9S+3s0o#s.q.#S)SG#E#Jm#'#:s0ts0tS<S,,s0t#S;A#S9S+.#S)SG#E#Jm#(#m##$l#Ps/&s.~#l#Qs/'s/##l#@s/*s/)#l#?s/.s/-#j#Rs/C#j#@s/F#V#IHj##s/K#j##s/W#;s/Xs/Vs/O#Hl#)s/_s/\#l#?s/fs/d#j#*s0$#j#Ss0&#V#IHj##s0*#j##s04#;s05s04s0-#Hl#*s0;s08#l#?s0@s0>#j#)s0\#j#*s0a#j#$C#j#%C#j#&s17#j#'s18#j#Ts1+#j#(s18#j#Us1;#j#0s1<#V#IHj#0s1>#j#0s1?#YT$s1@s1@s0p#Hj#'s1@#YT%s1As13s1(#Hj#(s1A##"). Qed.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Local Open Scope Z_scope.

Lemma in_arg0_sys_input_m : forall ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mzero (L S : list (word * word)) (r : word * word) (M : word -> option byte) : word -> option byte :=
  fun x => if zin_rangeb (bv_unsigned x) r && negb (hiddenb L S x) then Some (Z_to_bv 8 0) else M x.

(* [comment removed for export] *)
Lemma mzero_zfill : forall L S (a n : word) M,
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> hiddenb L S x = false) ->
  mzero L S (a, n) M = zfill a n M.
Proof.
  intros L S a n M WIN. apply functional_extensionality. intros x. unfold mzero, zfill, zmem, zin_rangeb. cbn [fst snd].
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n));
    cbn [andb]; try reflexivity.
  rewrite WIN by lia. reflexivity.
Qed.

Lemma mzero_zfill_S : forall L S (a n : word) M,
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> in_rangesb x S = true) ->
  mzero L S (a, n) M = zfill a n M.
Proof.
  intros L S a n M WIN. apply mzero_zfill. intros x Hx. unfold hiddenb. rewrite (WIN x Hx).
  destruct (in_rangesb x L); reflexivity.
Qed.
Scheme kc__4 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.lzok Sort Prop.
Scheme kc__5 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.lazy_inv Sort Prop.
Scheme kc__6 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

Lemma lzok_after_madvise : forall L S Zr msF mo (addr n : word),
  lzok segs L S Zr (mkCfg msF mo) ->
  (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
                    hiddenb L S x = true -> in_rangesb x Zr = true) ->
  let mo' := madvise_dontneed_next mo addr n in
  let msF' := advance_past_svc (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])) in
  lzok segs L S Zr (mkCfg msF' mo')
  /\ restrict L S msF' = sysret (restrict L S msF) (Z_to_bv 64 0) (mzero L S (addr, n) (ms_mem (restrict L S msF)))
  /\ hid_same L S msF msF'.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.lzok); constr:(segs); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.hiddenb); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.in_rangesb); constr:(@kc__4); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.MemCopy); constr:(@Corelib.Init.Datatypes.nat); constr:(@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_next); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.restrict); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.sysret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.WithSegs.mzero); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.hid_same); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.lazy_ranges_okb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.lazy_inv); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.cfg_model); constr:(@Corelib.Init.Datatypes.option); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_halted); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.hidden_zero_on); constr:(@LinuxProcessSemantics.LinuxProcessSem.Run.cfg_ms); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.rsub); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_maps); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.apply_effect_mem_zeros_ret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MmapSim.zfill); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.leb_spec); constr:(@Corelib.Init.Datatypes.BoolSpec); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.Some); constr:(@Stdlib.ZArith.BinInt.Z.ltb_spec); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazySR.Build_lzok); constr:(@kc__5); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy); constr:(@Stdlib.Lists.List.NoDup); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized); constr:(@Stdlib.Lists.List.incl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.all_pages); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.eager_used); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.pages_total); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_size); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.vm_limit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.Build_lazy_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.madvise_dontneed_next_lazy); constr:(@Stdlib.Lists.List.filter); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.page_outside_range); constr:(@Stdlib.Lists.List.NoDup_filter); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.madvise_dontneed_next_materialized); constr:(@Stdlib.Lists.List.In); (KReplay.sort_at constr:(@Stdlib.Lists.List.partition) [0]); constr:(@kc__2); constr:(@Stdlib.Lists.List.filter_In); constr:(@Corelib.Init.Logic.and_ind); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.VmMaps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.madvise_dontneed_next_vmmaps); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.madvise_dontneed_next_eager); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyMadvise.madvise_dontneed_next_halted); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.eff_ret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.restrict_mem); constr:(@stdpp.tactics.f_equal_help); constr:(@Stdlib.Logic.FunctionalExtensionality.functional_extensionality); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyRestrict.zin_rangeb); constr:(@Corelib.Init.Datatypes.negb); constr:(@kc__6); constr:(@Stdlib.Bool.Bool.andb_false_r); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Stdlib.Bool.Bool.andb_true_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.restrict_sysret); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.LazyNodes.hid_frame_sysret)|] [|@x; @o; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__arith; @H0; @b; @b0; @H; @Hx; @l; @f; @A; @Hp; @p; @z; @v; @Hbud; @Hincl; @Hnd; @Hl; @li_budget; @li_incl; @li_nodup; @li_lazy; @Hz; @m; @Eh; @Hhid; @Emem; @HLM; @HZL; @HSZ; @HZr; @Hh; @Hinv; @HL; @lzok_LM; @lzok_ZrL; @lzok_SZr; @lzok_zero; @lzok_halted; @lzok_inv; @lzok_ranges; @msF'; @mo'; @HZ; @Hok; @n; @addr; @mo; @msF; @Zr; @S; @L|] "#*R#E$g#Y###$#%#;#&#:#[#9$(#'#+#<#,#7#8#=#(#6#?#N#>#Q#)$0#*#-#5$@#4#3$1$Q#z#}$/#@#C#.#1#B$Y#M#b#u#0#2#A$4$E$K$J$L#K#J#\#a#q$)$+$3$2$8$-$U$Z$^#j$c#k$A#O#l#f#g#/#y#|$%$&$*$,$.$7$6$5$9$:$;$>$?$<$'#D$O$R$S$W$V$X$[$N$C$\$B$]$d$e$f$g$`$_$h$i#]#X#U#W$##R#S#T#{#i#v#x#V#e$F$T#h#p$=#L#P#Z#H#c#d#`#_#o#r$I$P$b#^#m#t#w#~$$$D$H$G$M$a#I#n#sU$:&$;%$<%$=%$>%$?%$@%$A)#k$#k%$B&$C%$D$$E%$F'$G$$H&$I&$J$$K%$L$$M($N&#f&$O$$P$$Q&$R)$S%#h'$T&$U$$V$$W&$X$$Y$$Z'$['$\$$]%$^%$_$$`$$a&$b$#e'$c%$d%$e%$f$7S=7#7#7#7#7#USH#USI#R##;#'HF8S)S*S$M#$(H$)D)$#$+F%&#0&#(&#9PNE#C#JVSJFN#C#Jk##%#k##(#k#$4#'S$M8S)NS,S*#VSK8S>USH=USI#;#R;#<#1==MH<==>$#<S\RAS]<#>.)&'%#?S*#F#4S$MH'$#8S)PNS,#-PN&-PNS*+#@PN1#:%8##S''#GPNS*,($#(+#j##>#SS)N#C#J'S*S$5#APN#USLs#8'S,S*5#B#Ts#<#'$#'NS,US?#HS9S-P#.S9S-.S9S@'S9S-5#/#I#.S:#SS)SA#C#J'S@S^5#AS1SA#'S:S@5#B##:#6'SAS:US?#HS.S0S1#.S.S0.S.Q'S.S05#/#I#.R#XS_S%s#FS0S1USLs#Ek##s#]#1s#^s#^S0S1=s#^#s#C>s#Ks#F#s#Ds#Bs#@?S%#+#+S%WS4S0S1##*%#9GID#C#J+KWS4QS%#UDF,IF#2$#j#%2#$s#oQ$s#pEVS`$#)%$0%&J'&WS5%$#$s#vRJ#s#n$s#xK)#s#s0s#t$$s#{S$$s#|G$s#}I%$#K&#&E#VSKs#jS>VSas#j#,S#S$nC#$##s#)&#%#$###s#*#$$s$*M),#VSb/,00-).1WS5$#.$s$0S*$s$1O%#4K%#$s$4S,$s$5S#%#'0%#)$&&JE,SBPnC#$##s#<$#%#7###s#=#$$s$=N$s$>S(%#,0%#<SM;SMVSNLFVSNLHXScL$E#USdLUSeLVSCLs$NVSCLS=USfS=VSCL#WSgL%#XSOL'Sh#[SP)S6S+S+S2#SQTS+XSOL)Si*[SP,S6S+S+S2#SQ[Sj-S6S+S+S2#&\SR.S6S+S+S2$&#\SR/S6S+S+S2('#VSk0S26CJVSlDF#C#Jm$%#WSmLS>EXSnDF$#l#&*)#l#':9#l#(?>#j#)L#j#*L#j#+L#%DF0E#)EF)FH%FM0H#(%#k##'#k##)#k#)L#k#*L#k#+L#$s$nS&$s$oS-$s$pS7YD%$#ES$l#,3'#WOP#NWS:PN#XSos#vs#=s#Q#&JJnC#$##s#x##%#s#S#s#?#s#y#s#@m#&#j#-s#<#U#D)s#?s#A6s#~s#E&JS/nC#$##s$$##%#s#[#s#G#s$%#s#Hm#&#j#-(#U#DnS5%s#Os#N%#.##s#JE#%$##+$###l#/s#TC#l#.s#\s#Y#j#0s#^#U#D0s#as#j&S/EnC#$##s$0##%#s#g#s#S#s$1#s#T&S/JnC#$##s$3##%#s#j#s#V#s$4#s#Wm#5#j#-s#S#U#D&S/S/nC#$##s$9##%#s#p#s#\#s$:#s#]m#;#j#-=#U#DnS5%s#ds#c%#.##/E#%$##)$###l#/s#iC#l#.s#qs#n#j#05#U#DnS5%s$'s$&%#.##s#wE#%$##8$###l#/s$*C#l#.s$1s$-#XS4QS%s$:E,KE#s$H$#m#&#1s%Hs%HQS%=s%H#s%->s%5s%0#s%.s%,s%*?K#+#*s$Ns$Bs$>(#Fj#1s$E#j#$s%O#,'E#s$S#.k##s$I#k#$s%S#1s%Ts%TS%S.=s%T#s%9>s%As%<#s%:s%8s%6?R#F#4QS%S.'$#8S)GIK#-GI&-GIR+#@GI-#:%s%K##S''#GGIR,($#SS)G#C#Jm#N#AGIQ4RQS%AOG#j##%#LQ#s%j#G2RVSDs%n#2KMONs%q$#CIUSES#VSF#SG%%#/IO#)%#LG#s%x#S&2OVSDs%|#2S#MS7Ns&#$#CS(USESBVSF#SG%%#/S(O#)%#4S&S(S#LS&#s&+DSpj#2s&,#L&WSqS&S(S#*s&/'%H$#;s&2VS3s$Ts$S2S&Ds&5$#VSDs&6Dj#2'#XSrs&8'&F20WSsS&S(S#*+(&%$#MS8Ns&=D#j#2.#%s$0s$`VS3s$1#2S7Ds&B$#3s&CD#k##DC;FDHFD3HE#3MFEUHF#C#J(%#k##'#3HEDUFE#C#J(%#DMHE3MF#k##%#(*#3S$HFUMH#C#J(%#k##)#j##(#DS$MF3S$H#k##4#j###Ej##5#XStHFEDYSu70)$#j#2?#j#$E#j#3B#j#4SS#k#2s##<k#$E#k#3s#&#k#4SS#$s&kSB%#s$ZVS3$#2S;YDs&n$F#E3s&oF$WS3('F#C#J(%#2S83s&tH#$s&vS;%#.WS3$#H#C#J$s&zS8%#'WS3$#M#C#Jj#-#Ej#0,#YSv-)-#DVS$H#l#551#l#0?;#j#5s#B#j#6s'(#MS;Ns'*s#S#m#%#*s#Xs#Us#L#s#Qs#PCS&USES8VSF#SG%D#4S7S&S(/#O#)&#j#7L#/S&CS7%#+OD)$#j#8S<#/s#oWSTS&S(S#*S<*%D$#Cs#rWSwS&S(S#*L6.%$#[SxS8S;s#us#os#e8#j#9s#w#j#:s$##j#;s$'#j#<s$*#X#HFEDj#=s$.#j#>s$6#j#?s$:#j#@s$=#ZSyGIQs$@#S,5s$QAGI#m#%#BQ#s&wDs&sj#%s&x#Bs$XWSzQS%S.*s&{'%S*$#B+#s&}#s&ym#%#9OGD#C#JVSJEG#C#J,GF#s&`Ds&;j#%s&a#WNFED1s'as'aKR=s'a#s'F>s'Ns'I#s'Gs'Es'C?G#,#FVHFE*s&i,*)$#F&,#F#s&l#s&Gm#&#j#A2#j#15#j#$s'n#HGIKs$um#$#US?s$uHGIK#m#%#.IKm#M#.KGm#H#/QID.O#j#8S<#/s%%WSTQS%S.*S<(%F$#/s#4I#.G#m#&#`S{S)GIKs%+s${s#6s#-20.#US|s%0+s%0WSUGI#:s%,%#-OGK+#@OGs%D#:%s'v##S'D#j#BS'#VSVs%3s'yk##s'4S'6#$PS#ODE1s(6s(6RQQs'&#9S#OEE#&%#-S#OI,#EnC#$##s'?%#%#s&v###s'@+#j#%s'@#6CD#C+D9S&S(H#C#DTs(-+S#XS4GI#MnC#$##s'IE#%#%##1s(Hs(HGIQs&~#EE&$#,S#MnC#$##s'OE#%#+##nC#$##s'P%#%#s'+###s'Q*#k#C/#j#.C#9S(S#F#C#JnC#$##s'VD#%#s'1#2#s'W3#j#.C#6s'Y51s(Xs(XIKQs(T#&#S/US}$*CS/('$#EJ&'#nC#$##s'a##%#s'<#=#s'b>#m#'#j#C1##C3S/nC#$##s'fD#%#s'A#:#s'gA#j#.C#Js'Is(b%s'Js'OKs(d#&%#,S(S$nC#$##s'nD#%#s'I###s'o##j#.C#6s'qs'L6s'rs#&XSW%$#Dl#.*C#,OHnC#$##s'v,#%#s'Q##WS~s(us(u?$s(w#J#s(rWT#s(xs(xB$s(z#%&#Ks(v#&'#nC#$##s(###%#s'Z#,#s($,#m#/#+OXS4IK#HnC#$##s((s#+#%#s'_#1#s()$#m#'#&s#.JUT$s#/*Cs#0s##%$#ES/&s#2#nC#$##s(0##%#s'g#9#s(1,#m#'#j#Cs#,#XSWs#?s#.#EU#Dl#Cs#Rs#Q#l#.s$:C#POGs(+DQs)1s&MEs$=&$#POGs(0DnC#$##s(=$#%#s't###s(>(#m#*#*s(?s(3s#]#s&PFPOGs&QDYSXOGs&Vs#qD#s(C$#m#&#j#$s)C#YT%s)Ds(Fs#xs&C#\T&s(FS's#qs#qs#ys&Ds#o##S's#ys&Dm#$#ZT'GIGIRs&P*S's#|s#v$s&K#YT(GIRs&RDXSYs&Hs&G$#XSYs&Os&Gs$'#l#Ds&\s&X#l#Es(Qs(G#Fs(L4S.S0S1'$#8S)KRQ#-KR&-KRS%+#@KRs(V#:%s)B##S''#GKRS%,($#(+#m#0#j#Fs(a#j#Gs(g#j#Hs(i#j#Is(k#j#Js(o#j#Ks(t#j#Ls(x#[#S*S$MHFEDj#Ms(|#j#Ns)&#j#Os)(#j#Ps)*#j#Qs).#j#Rs)5#j#Ss)9#\T)S)NS,S*s)Ys)<#E4MHF'DE8S)S-PN#-S-PD-S-PS,1s)rs)rS$M+$@S-P$#:&s)`##S'(#GS-PS,D($#(,#l#Ts)WS'#l#U0SZ#m#2#j#Vs)k#j#Ws)z#j#Xs*##j#Ys*$#j#ZSZ#j#[S'#j#\s*%#j#]s*&#j#^s*'##"). Qed.
Scheme kc__7 := Elimination for Corelib.Init.Datatypes.unit Sort Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem sreach_madvise_dontneed_lazy : forall L S Zr msF ms mo x8 (Q : config -> Prop),
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 233 ->
  let addr := ms_gpr ms 0 in
  let len := ms_gpr ms 1 in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  let h := m_vmmaps mo in
  bv_unsigned addr mod page_size = 0 ->
  bv_unsigned (ms_gpr ms 2) mod 2 ^ 32 = 4 ->
  len <> Z_to_bv 64 0 ->
  bv_unsigned addr + nZ < 2 ^ 64 ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  region_free (vm_noaccess h) addr n = true ->
  (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
                    hiddenb L S x = true -> in_rangesb x Zr = true) ->
  (forall msF' : machine_state,
     let mo' := madvise_dontneed_next mo addr n in
     lzok segs L S Zr (mkCfg msF' mo') ->
     restrict L S msF' = sysret ms (Z_to_bv 64 0) (mzero L S (addr, n) (ms_mem ms)) ->
     hid_same L S msF msF' ->
     same_but_materialized mo mo' ->
     sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hal Hadv Hlen Hnw Hrf Hmc Hna HZ Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (addr := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  destruct (page_round_up_n_facts (ms_gpr msF 1) Hlen
              ltac:(pose proof (word_unsigned_range addr); fold nZ; unfold two_pow_64; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 233) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite <- Hun in HZ.
  destruct (lzok_after_madvise L S Zr msF mo addr n Hok HZ) as (Hok' & Hvis & Hhs).
  assert (Hsp : forall o, syscall_spec (sys_input segs msF x8) mo o <->
                          o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next mo addr n) []).
  { intros o. rewrite (syscall_spec_233 _ mo o Hno').
    rewrite in_arg0_sys_input_m, in_arg1_sys_input', in_arg2_sys_input'.
    apply (madvise_dontneed_outcome addr (ms_gpr msF 1) (int32 (ms_gpr msF 2)) _ mo o Hal
             (madvise_dontneed_b_int32 _ Hadv) (w_is0_false _ Hlen)).
    - fold nZ. unfold two_pow_64. exact Hnw.
    - fold nZ. fold n. unfold madvise_dontneed_ok. rewrite Hrf, Hmc, Hna. reflexivity. }
  assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])))
                                    (madvise_dontneed_next mo addr n))).
  { apply (node_family_noacc segs msF mo x8 unit (fun _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)])
             (fun _ => madvise_dontneed_next mo addr n) (fun _ => []) _ (lzok_halted Hok) Hsvc Hsp).
    - intros []. reflexivity.
    - intros []. apply not_spurious_none. rewrite Hno'. exact injected_arm_none_233.
    - intros o Ho. exists tt. exact Ho.
    - intros []. exact (lzok_halted Hok').
    - intros []. reflexivity. }
  apply (sreach_node segs _ unit _ tt _ Hnode
           (RomBase.sys_rob_memfree segs msF mo x8 Hsvc ltac:(rewrite Hno; exact RomBase.memfree_233))). intros [].
  apply (Hk _ Hok' Hvis Hhs). apply madvise_dontneed_next_sbm.
Qed.

Local Close Scope Z_scope.
End WithSegs.
