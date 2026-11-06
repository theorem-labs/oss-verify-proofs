(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Inductive ztr : Set := ZL (b : bool) (c1 c2 : int) | ZN (l r : ztr).

(* [comment removed for export] *)
Fixpoint rtree (leaf : int -> ztr) (d : nat) (acc : int) : ztr :=
  match d with
  | O => leaf acc
  | S d' => ZN (rtree leaf d' (acc << 1)%uint63) (rtree leaf d' ((acc << 1) lor 1)%uint63)
  end.

(* [comment removed for export] *)
Definition gleaf (s : PrimString.string) (acc : int) : ztr :=
  ZL (Uint63.ltb ((acc << 1) lor 1)%uint63 (PrimString.length s) || Uint63.eqb ((acc << 1) lor 1)%uint63 (Uint63.sub (PrimString.length s) 1))%bool
     (PrimString.get s (acc << 1)%uint63) (PrimString.get s ((acc << 1) lor 1)%uint63).
Definition gtree (s : PrimString.string) : nat -> int -> ztr := rtree (gleaf s).

(* [comment removed for export] *)
Fixpoint ctree (d : nat) : ztr := match d with O => ZL true 48%uint63 48%uint63 | S d' => let t := ctree d' in ZN t t end.
Lemma ctree_rtree : forall d acc, ctree d = rtree (fun _ => ZL true 48%uint63 48%uint63) d acc.
Proof. induction d as [|d IH]; intros acc; [reflexivity|]. cbn [ctree rtree]. cbv zeta. rewrite <- !IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition canon (c : int) : int :=
  (if Uint63.ltb c 58 then
     if Uint63.ltb c 52 then (if Uint63.ltb c 50 then (if Uint63.ltb c 49 then 48 else 49) else (if Uint63.ltb c 51 then 50 else 51))
     else if Uint63.ltb c 56 then (if Uint63.ltb c 54 then (if Uint63.ltb c 53 then 52 else 53) else (if Uint63.ltb c 55 then 54 else 55))
     else (if Uint63.ltb c 57 then 56 else 57)
   else
     if Uint63.ltb c 100 then (if Uint63.ltb c 98 then 97 else if Uint63.ltb c 99 then 98 else 99)
     else (if Uint63.ltb c 101 then 100 else if Uint63.ltb c 102 then 101 else 102))%uint63.
Lemma canon_hex : forall c, c = canon c -> N.ltb (hex_nybble c) 16 = true.
Proof.
  intros c H. unfold canon in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; rewrite H; vm_compute; reflexivity.
Qed.
Definition vleaf (s : PrimString.string) (acc : int) : ztr :=
  ZL true (canon (PrimString.get s (acc << 1)%uint63)) (canon (PrimString.get s ((acc << 1) lor 1)%uint63)).
Definition vtree (s : PrimString.string) : nat -> int -> ztr := rtree (vleaf s).

(* [comment removed for export] *)
Fixpoint ext (d : nat) (q pi : positive) : Prop :=
  match d with O => pi = q | S d' => ext d' (xO q) pi \/ ext d' (xI q) pi end.

Lemma rtree_inv : forall (lf1 lf2 : int -> ztr) d f q acc, acc = of_pos_rec f q -> rtree lf1 d acc = rtree lf2 d acc ->
  forall pi, ext d q pi -> lf1 (of_pos_rec (d + f) pi) = lf2 (of_pos_rec (d + f) pi).
Proof.
  intros lf1 lf2 d. induction d as [|d IH]; intros f q acc Hacc HT pi HX.
  - cbn [rtree] in HT. cbn [ext] in HX. subst pi. cbn [Nat.add]. rewrite <- Hacc. exact HT.
  - cbn [rtree] in HT. injection HT as EL ER. rewrite (Nat.add_succ_comm d f). destruct HX as [HX|HX].
    + apply (IH (S f) (xO q) (acc << 1)%uint63); [subst acc; reflexivity| exact EL| exact HX].
    + apply (IH (S f) (xI q) ((acc << 1) lor 1)%uint63); [subst acc; reflexivity| exact ER| exact HX].
Qed.

(* [comment removed for export] *)
Lemma hex_byte_at_zero : forall s pi, gleaf s (of_pos_rec 62 pi) = ZL true 48%uint63 48%uint63 -> hex_byte_at s (N.pos pi) = Some (Z_to_bv 8 0).
Proof.
  intros s pi H. unfold gleaf in H. injection H as HB H1 H2. unfold hex_byte_at.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi))) with (of_pos_rec 62 pi << 1)%uint63.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi + 1))) with ((of_pos_rec 62 pi << 1) lor 1)%uint63.
  cbv zeta. rewrite HB, H1, H2. reflexivity.
Qed.
Lemma hex_byte_at_some : forall s pi, gleaf s (of_pos_rec 62 pi) = vleaf s (of_pos_rec 62 pi) -> hex_byte_at s (N.pos pi) <> None.
Proof.
  intros s pi H. unfold gleaf, vleaf in H. injection H as HB H1 H2. apply canon_hex in H1, H2. unfold hex_byte_at.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi))) with (of_pos_rec 62 pi << 1)%uint63.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi + 1))) with ((of_pos_rec 62 pi << 1) lor 1)%uint63.
  cbv zeta. rewrite HB, H1, H2. cbn [andb]. discriminate.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma ext_of_range : forall d q i, (N.pos q * 2 ^ N.of_nat d <= i < (N.pos q + 1) * 2 ^ N.of_nat d)%N -> exists pi, i = N.pos pi /\ ext d q pi.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.nat_ind); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.Numbers.BinNums.N); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.NArith.BinNat.N.le); constr:(@Stdlib.NArith.BinNat.N.mul); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.NArith.BinNat.N.pow); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.NArith.BinNat.N.of_nat); constr:(@Stdlib.NArith.BinNat.N.lt); constr:(@Stdlib.NArith.BinNat.N.add); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.ext); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.of_N); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.N2Z.inj_iff); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.ZArith.Znat.N2Z.inj_le); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.ZArith.Znat.N2Z.inj_mul); constr:(@Stdlib.ZArith.Znat.N2Z.inj_lt); constr:(@Stdlib.ZArith.Znat.N2Z.inj_add); constr:(@Stdlib.ZArith.Znat.N2Z.is_nonneg); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Pos2Z.pos_is_pos); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.NArith.BinNat.N.succ); constr:(@Stdlib.NArith.Nnat.Nat2N.inj_succ); constr:(@Stdlib.NArith.BinNat.N.pow_succ_r'); constr:(@Stdlib.NArith.BinNat.N.lt_ge_cases); constr:(@Corelib.Init.Logic.or); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.Znat.N2Z.inj_pow); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.nat_N_Z); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.X); constr:(@kc__2); constr:(@kc__3); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.or_intror); constr:(@kc__2 (@Corelib.Numbers.BinNums.positive))|] [|@pi; @i; @q; @d; @y; @x; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @cstr0; @cstr; @Hi0; @Hi; @n; @Ha; @__x3; @__p1; @__sat4; @__sat3; @cstr2; @cstr1; @Hl0; @heq_P0; @heq_P; @X; @E; @H; @e; @Hl; @Hg0; @Hg; @o; @P; @IH|] "#*?#9$=#Q#?#R###p#>#$#%#'#&#q#o#d#(#+#-#,#.#B#Z#`#y#*#)#1#4#A#Y#I#\#H#[#3#F#^#b#a#/#0#<#x#z#5#6#9#M#K#7#2#e#g#j#i#w$$$%$*$)$.#G$1#D$0#8$7$<$;#V#U#f#h#k#l#n#|#}#~$&$'$#$+$,$-$3$4$2$5$6$8$:$=$>$/#=#@#L#W#C#_#E#T#S$9#u#t#s#J$(#X#r#m#]#{#c#v#P#O#NI$%%#5%#6%$&&#Q&#>%$'%#B%$($#=%#A%$)5#%$#@%$*$#?%$+/#`%$,$$-$#^$$.&$/'$0*$1%$2$#_$$3'$4*$5+$6)$7&#a%$8$$9%$:'$;'$<'+I1S4+#7J4$#$'#,#F+S42*#$#'-F##'#+F'DJ#&KLF#$#j#$H#;H#k##)#k#%D#k#&H#j#'S:#7S@47#$:#,#F$4%-F##%#&S@LF#3#j#$H#+J'DI#&S@JJ/I5J'C$#USADUSAC/F'C(#'DIFVSVIFWSW%$#j#(D#j#)D#)C.)C.3DC-E,%I0$3/#$4s#-,#I26s#/$#s#0-I##&#5S4%7#(#909%%#&*<##&#j#)CFU#>%#+(#A0%-%#.*s#$#)C(/s#)'C#*m#%#)C4.DDDCCCS%EEES&S's#--$s#F5#3DCS-ES.S5<-#Is#+?.DDDCCCS/EEES0S6s#//&s#H7%.DDDCCCS%EEES&S'<-#s#I8&3DCS1ES2S7Is#.B<-#A?<0-&#><5#FDJ/J(O#USDK5K*O#USXSEUSYSEVSFCJUSZCXSGC$I#US[CUS\CECs#`VSHCs#*8C$#ECS49C$S;#:(NGGM#S(BC('8C#(9C'S<#:,NGGM#S(?-NGGM'#US]G9C+S^.:0NGGM#S(@1NGGM&%#VS_2M)SISJVS`FJ'SI#SJm$%#WSaCOIXSbFJ$#l#**)#l#+<;#l#,A@#j#-C#j#.C#%Is#D(#F0Is#F%#s#G*F##&#'CIJk##$#k#-C#k#.C#5S*/PWF$#Ll#/0&#l#0s#5s#3#l#1s#9s#7#l#2s#;s#N#Fs#ls#hs#\#)HJGs#ns#m$#HHs#qJ#j#3s#u#j#%D#j#&H#<L7#4s$8#$s$;#,#F$s$5%-F##%#<K7#+L4s$AF$$#,#J2&s$?$#&-J##&#j#4D#7KUSK#UScKZSLD/&F$#4s$M%$s$0#,#I$s#z%-I##%#7PUSK#4s$U#+K$#F,#L2%s$T$#F-L##&#j#4D#4s$^-$s$_#VSds$`/ZSLD.&F$#$s#$%,#J$B'-J##%#7S*4s$h#1P+#2#s$f$#FVSeK#-K$,%KVSM$#1S*+#2#s$n$#I-P#,$PVSM$#'DS)s$n<R&#QF#%#j#$H#;H#j##)#1S)+#2#s$|$#J-S*#1Q7R4s%*#)D#'DL$m#$#1S#+#$#K,#Q2%s%-$#K-Q##&#5s%75S#%$#/K%$#/Q($#0's$c%#'*&##&#)C+)C+.DDDCCCS%EEES&S'6-$K,#)C+3DCS-ES.S57-$Q,#.DDDCCCS/EEES0S690's%As$ls$Z.DDDCCCS%EEES&S'7,#K0'3DCS1ES2S7Q/&7,#A:7/,&#7S$4s%K#'DK#=S$C:#'C8#Us$o%C=#)C>)C(`SfS:DCCSNSOEs$sSgS$)#.DDDCCCSPEEESQShs%UA%-'#3DCs%2Es%1s%*K?6-'#>-*#F1R+#2#s%U$#P-S##/S#5R%s#+#0#s%*%#s$:*'#)C(%s#0Fj#)C#U#*Us%*#0#s%2%#s$B)C%/4'C#'m#%#.DDDCCCS/EEES0S67)#s%is%8s%&)Cs$H.DDDCCCS%EEES&S'8*$Ps$I#3DCS1ES2S7S#608*#>82#J+S$$s%tS*$$#,#R2&s%r$#&-R##&#5S$/S*%s#I#%%#/R($#0(s%K%#'*&##&#Us%H,%#+(#*0%s%R%#.*-#)C(/;'C#*m#%#)C5.DDDCCCS%EEES&S's&4s#\s#@S*6#.DDDCCCS%EEES&S'@.%?6#)C53DCS-ES.S5@/$R6#.DDDCCCS/EEES0S6s##1(s&3s%^s%L.DDDCCCS%EEES&S'@/#s##:'3DCS1ES2S7R9&@/#As##@2/&#>@6#S)DS$/S$(O#DQ(Os#dUSDS+5S+*O#USiS,=S,(O#=S=VSjs#q#*Os#r=S>(O#=SBCs#v#*O#k##&#k##)#(Os#z=SRWSks#|#Ij##SS#j#5&#Cs$#&(O#k##SS#k#5*#UIL(O1*O(k##$#UFLVSFCLXSGCs%eI#VSHCs$.8C#s%b8Cs%`#6S4EC#9C%S;#:s%hNGGM#S(ZSls%iNGGMP?s%jNGGM$#8C+s%gBC#s%j8C#s%l9C*S<#:s%oNGGM#S(8C's%o9C#S;-:s%rNGGM#S(?s%sNGGM#&@s%tNGGM's%h#@s%uNGGM-s%i#l#*#s%fs%`l#+8s%x#l#,s%~s%}#j#-C#j#.C#j#6C#j#7S?#%s$II%F#(#J##L0&s&K%#J*L#%s$PJ%#L(#K0%s&Q%#L*K##&#k##*#k##.#k#-C#k#.C#k#6C#k#7S?#/SB5SR0#s&]/S3%s$a#%%#*(#ZF#)&(S#Rl#/?+#l#8s#=s#?#l#8s#Bs#?#l#9s#Hs#D#l#8s#Vs#N#l#:s#[s#Y#l#;s#_s#]#l#0s#bs#a#l#1s#fs#d#l#2s#hs#|#l#<s$3s$C#l#=s$Os$W#Fs$rs$gs$^#l#>s${s$|#+s%%$#L,#S)2%s'I$#L-S)##&#m#*#WS#s%-S)#'DQs'J&S$s%)F#$#j#$H#;H#'DS#s'O&S8s$`F#$#j#$H#;H#'DRs'T<S9&#S$F#%#j#$H#;H#j##)#1S$&S9#F#+#j#$H#U#F'DS$s'`1S8&S+#F#%#'DS8s'p1S9&SC#I#%#'DS+s'h<S,&#SCF#%#j#$H#;H#j##)#1S+&S3#J'DS+s&=1S3&S=#K'DS,s't<SB&#S=F#%#j#$H#+P'DS3#<S>&#S,P1S,&S>#P6S,&S>#PWSm%#FG*(I#HH-P#j#?3#j#@6#V#IFj##9#j##s#&#YSTs#'s#%=#Fj#As#)#j#$H#V#IFj##s#0#j#)H#YSUHs#?s#7#Fl#Bs#Is#D#j#Cs%v#U#Fj##s&*#,s%zS*6Q6S#+#$#K,#Q2%s(C$#K-Q##&#(s%ls%o0s%ns's%#s%s*s%r##&#)Cs%r.DDDCCCS%EEES&S'/s%s#Ks%ws%n3DCS-ES.S5/s%s#Qs%vs%m.DDDCCCS/EEES0S61s%u%s(Os'zs'h.DDDCCCS%EEES&S'/*#Ks%zs%q3DCS1ES2S7Qs%ys%p/*#A2/-*&#,s%[S#(s%Vs%Z3DCS-ES.S5s%]s%Os%HS#s%[s%U>%$#JBCs'Xs'Z8C#s$X9Cs$VS<#:s'_NGGM#S(?s'`NGGMs$U#9Cs$RS;s$Y:s'bNGGM#S(BCs$Us'a8C#s'c9Cs$]S<#:s'fNGGM#S(?s'gNGGM'#@s'hNGGM(s'\#@s'iNGGM+s']#l#*#s'Zs'Tl#+s$hs'l#l#,s'rs'q#j#-C#j#.C#j#6C#j#7S?#0Fs(;%#s$S*J##L#(s$QL(s$LK0s$Ns(A%#L*K##&#k##(#k##*#k#-C#k#.C#k#6C#k#7S?#%s$Ms$J(#s$OZF#s$Ps$Ms$OS#Rl#/6&#l#8s%(s%*#l#8s%-s%*#l#9s%3s%/#l#8s%As%9#l#:s%Fs%D#l#;s%Js%H#l#0s%Ms%L#l#1s%Qs%O#l#2s%Ss%g#l#Ds#5s#7#l#=s&:s&B#Fs#Gs#Bs#;#l#>s&fs&g#+s#Q$#L,#S)2%s)4$#L-S)##&#m#*#WS#s#YS)#&S$s#YF#s$J#j#$H#;H#6R&S8#F#s$J#j#$H#;H#j###s$C6S$&S9#F#s$K#j#$H#U#F6S8&S+#F#s$D#6S9&SC#I#s$C#j###s$;6S+&S3#J6S3&S=#KWSns$/s$-FGs$4s$2I#HHs$7P#j#?&#j#@s$@#V#IFj##+#j##s$P#YSTs$Q1/#Fj#A4#j#$H#V#IFj##:#j#)H#YSUHs##A#Fl#Bs#,s#(#j#Es$)#U#Fj##s'S#ZSos'Us'Ts'Ls$-#Fl#Fs'^s'[#l#Gs'dD#l#3s'ls'g#l#3s(&s'|#j#3s(6#j#%D#j#&H#j#Hs)b#j#'S:#XSps)cs(C#Fj#'S:##"). Qed.

(* [comment removed for export] *)
Fixpoint covers (bl : list (positive * nat)) (cur stop : N) : bool :=
  match bl with
  | [] => N.eqb cur stop
  | (q, d) :: bl' => (Nat.leb d 62 && N.eqb (N.pos q * 2 ^ N.of_nat d) cur && covers bl' (cur + 2 ^ N.of_nat d) stop)%bool
  end.
(* [comment removed for export] *)
Fixpoint gall (s : PrimString.string) (bl : list (positive * nat)) : Prop :=
  match bl with [] => True | (q, d) :: bl' => gtree s d (of_pos_rec (62 - d) q) = ctree d /\ gall s bl' end.
Fixpoint gallv (s : PrimString.string) (bl : list (positive * nat)) : Prop :=
  match bl with [] => True | (q, d) :: bl' => gtree s d (of_pos_rec (62 - d) q) = vtree s d (of_pos_rec (62 - d) q) /\ gallv s bl' end.

Lemma blocks_sound : forall (Q : N -> Prop) (R : positive -> nat -> Prop),
  (forall q d, (d <= 62)%nat -> R q d -> forall pi, ext d q pi -> Q (N.pos pi)) ->
  forall bl base n, (fix all bl := match bl with [] => True | (q, d) :: bl' => R q d /\ all bl' end) bl -> covers bl base (base + n) = true ->
  forall i, (i < n)%N -> Q (base + i)%N.
Proof.
  intros Q R HR bl. induction bl as [|[q d] bl IH]; intros base n HG HC i Hi.
  - cbn [covers] in HC. apply N.eqb_eq in HC. lia.
  - cbn [covers] in HC. apply andb_prop in HC as [HC HC3]. apply andb_prop in HC as [HC1 HC2].
    apply Nat.leb_le in HC1. apply N.eqb_eq in HC2. destruct HG as [HT HG].
    destruct (N.lt_ge_cases (base + i) (base + 2 ^ N.of_nat d)) as [Hl|Hg].
    + destruct (ext_of_range d q (base + i)%N) as (pi & E & X); [lia|]. rewrite E. exact (HR q d HC1 HT pi X).
    + assert (HP : (0 < 2 ^ N.of_nat d)%N) by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
      replace (base + i)%N with ((base + 2 ^ N.of_nat d) + (i - 2 ^ N.of_nat d))%N by lia.
      apply (IH (base + 2 ^ N.of_nat d)%N (n - 2 ^ N.of_nat d)%N HG); [| lia].
      replace (base + 2 ^ N.of_nat d + (n - 2 ^ N.of_nat d))%N with (base + n)%N by lia. exact HC3.
Qed.

(* [comment removed for export] *)
Definition zpt (s : PrimString.string) (base n : N) : Prop := forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Definition vpt (s : PrimString.string) (base n : N) : Prop := forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.

Theorem ztree_scan_sound : forall s bl base n, gall s bl -> covers bl base (base + n) = true -> zpt s base n.
Proof.
  intros s bl base n HG HC. unfold zpt.
  apply (blocks_sound (fun i => hex_byte_at s i = Some (Z_to_bv 8 0)) (fun q d => gtree s d (of_pos_rec (62 - d) q) = ctree d)) with (bl := bl); [| | exact HC].
  - intros q d Hd HT pi X. apply hex_byte_at_zero. unfold gtree in HT. rewrite (ctree_rtree d (of_pos_rec (62 - d) q)) in HT.
    pose proof (rtree_inv _ _ d (62 - d) q _ eq_refl HT pi X) as K. replace (d + (62 - d))%nat with 62%nat in K by lia. exact K.
  - clear HC. induction bl as [|[q d] bl IH]; [exact I|]. destruct HG as [H1 H2]. split; [exact H1| exact (IH H2)].
Qed.
Theorem vtree_scan_sound : forall s bl base n, gallv s bl -> covers bl base (base + n) = true -> vpt s base n.
Proof.
  intros s bl base n HG HC. unfold vpt.
  apply (blocks_sound (fun i => hex_byte_at s i <> None) (fun q d => gtree s d (of_pos_rec (62 - d) q) = vtree s d (of_pos_rec (62 - d) q))) with (bl := bl); [| | exact HC].
  - intros q d Hd HT pi X. apply hex_byte_at_some. unfold gtree, vtree in HT.
    pose proof (rtree_inv _ _ d (62 - d) q _ eq_refl HT pi X) as K. replace (d + (62 - d))%nat with 62%nat in K by lia. exact K.
  - clear HC. induction bl as [|[q d] bl IH]; [exact I|]. destruct HG as [H1 H2]. split; [exact H1| exact (IH H2)].
Qed.

Lemma zpt_vpt : forall s base n, zpt s base n -> vpt s base n.
Proof. intros s base n H i Hi. rewrite (H i Hi). discriminate. Qed.
Lemma vpt_app : forall s base n1 n2, vpt s base n1 -> vpt s (base + n1) n2 -> vpt s base (n1 + n2).
Proof.
  intros s base n1 n2 H1 H2 i Hi. destruct (N.lt_ge_cases i n1) as [Hl|Hg]; [exact (H1 i Hl)|].
  replace (base + i)%N with (base + n1 + (i - n1))%N by lia. apply H2. lia.
Qed.
Scheme kc__4 := Elimination for Corelib.Numbers.BinNums.Z Sort Prop.

(* [comment removed for export] *)
Lemma segment_byte_at_zero_pt : forall s (base n : N) (off : N),
  zpt s base n -> (base + n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N -> (base <= off < base + n)%N ->
  segment_byte_at [s] off = Some (Z_to_bv 8 0).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Strings.PrimString.string); constr:(@Corelib.Numbers.BinNums.N); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.zpt); constr:(@Stdlib.NArith.BinNat.N.le); constr:(@Stdlib.NArith.BinNat.N.add); constr:(@Stdlib.ZArith.BinInt.Z.to_N); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z); constr:(@Corelib.Strings.PrimString.length); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.NArith.BinNat.N.lt); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.NArith.BinNat.N.ltb); constr:(@Corelib.Init.Datatypes.true); constr:(@kc__3); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.NArith.BinNat.N.ltb_lt); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.of_N); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.Znat.N2Z.inj_lt); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@kc__4); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_N_Z); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.ZArith.Znat.N2Z.inj_le); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.ZArith.Znat.N2Z.inj_add); constr:(@Stdlib.ZArith.Znat.N2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.hex_byte_at); constr:(@Corelib.Init.Datatypes.Some); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Stdlib.NArith.BinNat.N.sub); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.N2Z.inj_iff); constr:(@Stdlib.ZArith.Znat.N2Z.inj_sub_max); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.segment_byte_at)|] [|@m; @n; @x; @z; @p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__p1; @__p2; @__p3; @__arith; @r; @q; @H4; @H3; @H1; @H0; @H; @__sat3; @z2; @H2; @cstr1; @cstr0; @cstr; @Hn0; @Hoff0; @b; @y; @__x8; @H5; @__sat4; @z3; @off; @__p4; @Hoff; @Hn; @Hs; @base; @s|] "#,-#>$S#\$-#Z$.$,#B#X#)$3###'#*#+#>#$#,#%#(#z#&$6#P$2$;#R$$#.#/#-#N#W#D#g#E#h#L#c#d#F#]#j#l#0#2$K#1#3#4#T#A#J#e#`#i#m#7#8$#$%$1$4$=#:#9$H$O$S#<#;$D#C#U#S#b#r#5#6$&$)$+$:$?$A$B$@$C#O$G$F$E$J$I$N$M$Q$P$R#=$T#M$0$/$*#I#H#Y#G#|#y$5#^#[#o#t$L#}#{$7#~#k$'$<#Q#a#n#s$($9#K#f$>#_#p#q#u#v#w#x$8#VU#S&#C%$*%$+'$,*#A%$-+$.$$/$$0%#)$$1%#E%$2&$3&$4*$5%$6/$7%$8%$9%$:%$;%$<%#D%#@%$=$#I$#B%$>5$?'$@&$A%$B'$C%$D%$E%$F)$G$$H'$I*$J/$K%$L%$M%$N%$O%$P%$Q$$R'WSYS&S#Q;S&S#*M+#IS6USE#.%#>#?)#?MS#;MS&<S##%%#*J+#.#,>#CS&#CQL#S(#S+<S#Qk##$#<QLCS#Q#S(#S+k##%#%'#CS&S##S(#S+k##+#j##&#j##$Lj##-#VSZQLYS[/+&$#j#$H#j#%H#k#$H.k#%H#*N+#.#s#&>#<M#-M,E&($#3C%j#&CL,ELj#&C#>LDHCS\#DCCS7L,E##C%#j#'C#DCCS7E,E#3C#USELDCCS7#,E#3C#j#(S8#USFLDCCS7#,E#3C#j#(S8#YSG0-(#Lj#&C#3CALCHCCS9;I9$BB#4HCS0IS1S:M@=B?#?JM;JS$<M#%%#-J$#s#&-S$/%#(s#)#%&#3C(4HCS2IS3S;J)#Ms#,s#)3C(@HHHCCCS4IIIS5S<J+%S$)#4HCS0IS1S:Ms#/s#,/)#ZSH1/,)&#J/)#Q;NJ*O+#.#s#\>#?'#-N/#6,E'$$#3C&@HHHCCCS4IIIS5S<N'#J:4Us#8+Us#+Lj#(S8#Us#(Lj#(S8#YSGs#7s#4%#Lj#&C#3C2LCHCCS9s#BIs#@$33#4HCS2IS3S;70,3+#J3/#S&USIO-O$E#*S.+#.#s#uEE#(E$,E%#C#&%%#$(E#C&E%$#5&#*S=+#.#s$%,E#*S@+#M#s$)$E$$Es$+*SA+#.#s$.$E#k##'#k##)#*S>+#N#s$4#Cs$5EUS]#Fs$7+6-s$8/$##C/#k##'#O1s$<(Es$=*SB+#6#s$@$E#($s$B%$#k##)#P(s$E(s$FE*S^+#6#s$I(s$J#$$E%$#k##)#Q(s$N*S_+#.#s$Q#C#Ek##@#R&s$T*SJ+#6#s$W#C#$k##s#&#.&s$Z*SK+#6#s$]=SL=#=#=#=#=#8C#8C%8C(8C+0C$#0C&#0C(#9#S,8CSL0C(#0C*#9#S,USMS%1S%$#1S%)#US`S%GCMGCJAC$S##GCS$GCNAC$S&#AC&Q#USaCUSbCVSNCEVSNCs$~&C$S)#'&GDDF#KUSODSS6S#:C#&C*S'#',GDDF#KH-GDDFR2.GDDF$#)/GDDF+*#&C.S*/'1GDDF#KZSc2GDDF#I-:C#Ss%4:C#WSPC5#BC#0&C'S*#':GDDF#K);GDDF+6#&C;S)('=GDDF#KH>GDDFS/2?GDDF$#H@GDDFS-:Cs%@&C#S*A's##GDDF#K2s#$GDDF&#Ks#%GDDF(#:CS6&Cs#&S'#'s#(GDDF#K:Cs##&Cs#)S'#'s#+GDDF#KIs%K:C#BC'#&C#S'0's#0GDDF#K&C*S'-'s#2GDDF#K&C/S)''s#4GDDF#K2s#5GDDF%#&C2S)7's#7GDDF#K)s#8GDDF%s#3#)s#9GDDF+s#4#)s#:GDDF1s#5#)s#;GDDF5s#6#)s#<GDDF9s#7#)s#=GDDFs#$s#8#)s#>GDDFs#1s#9#VSds#?F3S(S+VSeLS##S(#S+m$%#WSfCEQXSgLS#$#l#)*)#l#*s#Is#H#l#+s#Rs#Q#j#,C#j#-C#j#.C#j#/C#j#0C#j#1C#j#2C#j#3P#j#4P#j#5P#$EN%#Ok##s$8#k##s$AShFs%uJ/#O#CN#k##&#(EJ%#S/#CS&E%S-#5%#$ES&$EJ/NO$#J$OJ/OR(J#%%#(NOk##$#k##)#k##,#k##.#k##0#k##6#k##<#k#,C#k#-C#k#.C#k#/C#k#0C#k#1C#k#2C#k#3P#k#4P#k#5P#$S#E#CRS#(Qs&>*SQ+#-SK-SR-SJeL*)(Q&S#%$R#JNS/S-S=S@S>l#6s#3,#l#7s$GC#l#8s$KC#l#9s$Rs$M#l#:s$Ys$T#l#;s$cs$[#l#<s$ms$e#l#=s$vs$o#l#>s%&s$z#l#?s%*C#l#@s%7s%/#l#As%>s%<#l#Bs%?s%=#l#Cs%@s%>#l#Ds%Bs%O#l#Es%Zs%a#Ts&/s&,s%l#WLMs&1#l#=s&8s&6#XSiS(s&LS+##S(S+s&MIs#nUSj#USk#USl#VSSOS$USO%nS(#$##%L#%#$##VSm(EVSn(##(%#j#FS(#VS?MJ;J##H#M7s&As%z,E#/s%|##C#s&DUSCHUSCC-Q-L#C$##HQLVSoQLWSp%$#j#GH#j#&H#7QL,E#j#GC#j#&C#@HHHCCCS?III#STMs&Ss&PJs&0s&*@HHHCCCS4IIIS5S<Js&1s&+84#4HC2I1)84#Ms&Us&R-R-S-7$#EE#(E$,E%#C#&%%#$(E#C&E%$#5&#-S/-S.7$#,E#.s%gs'1EE#(E$,E%#C#&%%#$(E#C&E%$#5&#.s%fs';,E#Ms%ns'=$Es%o.s%Us'?$E#k##s%t#k##&#Ns%bs'CFs'D'/#s%Z#Cs%\#k##s%o#Os%^s'H6s%Ws'I$E#($s'K%$#k##s%n#Ps%\s'N(s'Os%V$s%WE%$#k##s%j#Qs%[s'S.s%Vs'T#C#Ek##s&##Rs%Ys'W*SR+#6#s'Z#C#$k##s&)#.&s']6s#|s'^8Cs%^0C#s%R0Cs%Z#9#S,USFS6VSqC#WSrC#s%^0C#s%X0Cs%a#9#S,=s%d8C#8Cs%h0C#s%b0Cs%g#0C&#9#S,9,S,1S%1s%_1S%,#1S%%#1S%'#1S%/#1S%6#GCOUSsCAC$M#AC#S#s%cAC#Qs%`:Cs$$&Cs%^S'#'s%`GDDF#K2s%aGDDF#s%E)s%bGDDFs%^s%]#WSPCs%as%QBC#(&Cs%]S*#'s%fGDDF#K)s%gGDDFs%Ws%b#&Cs%gS)s%V's%iGDDF#K2s%jGDDF#s%LHs%kGDDFS.&Cs%XS*s%k's%mGDDF#K2s%nGDDF%#Ks%oGDDF'#WSUCs%Is%L&Cs%pS)#'s%rGDDF#K&Cs%TS*%'s%tGDDF#K2s%uGDDF%#&C(S's%u's%wGDDF#K2s%xGDDF#s%WKs%yGDDF&#BCs%Vs%O&C#S's%g's%|GDDF#K&Cs%YS's%V's%~GDDF#K&Cs%XS)''s&$GDDF#K2s&%GDDF%#BCs%^s%c&C#S*s%\'s&(GDDF#K)s&)GDDF&s&$#)s&*GDDF,s&%#)s&+GDDFs%as&&#)s&,GDDF1s&'#)s&-GDDF<s&(#)s&.GDDFs#%s&)#)s&/GDDFs#+s&*#l#)#s%Os%Il#*s#2s&2#l#+s#8s&;#j#,C#j#-C#j#.C#j#/C#j#0C#j#1C#j#2C#j#HC#j#3P#j#4P#j#5P#$EO%#Rk##s'##Fs(_N/#R#CO#k##s%L#(EN%#S-#CJE%S.#5%#7S$S&(E##CM$%$#$&E#CME%$#5&#$EM/S$O$#R$JO/JR(O#%%##Cs%URk##$#k##)#k##,#k##.#k##7#k##=#k##B#k#,C#k#-C#k#.C#k#/C#k#0C#k#1C#k#2C#k#HC#k#3P#k#4P#k#5P#*SV+#-SQ-SWfLs%Ts%Ss%RQ%S#R$s%NS-#JNS/S.S>SASBl#6s#6(#l#7s$4C#l#8s$6C#l#Is$=s$8#l#9s$Bs$?#l#;s$Hs$D#l#<s$Os$J#l#=s$Us$Q#l#Js$\s$W#l#Ks$^C#l#:s$is$a#l#?s$lC#l#@s$ys$q#l#As(.s(,#l#Bs(/s(-#l#Cs(0s(.#l#Ds(2s(?#l#Es(Js(Q#Ts%<s%8s%'#VS?S$N;N#VSSRL#s%J#s%Ej#LH#<'J7s(\s(K,E#(#s(`@HHHCCCS?IIIs%4STS$s(_s(YNs(Ns(J4HCS0IS1S:,%#Js(bs(\?NS$<S$s(W%$#$s(Ss(d(s(es(S%$#4HCS2IS3S;Ns(Vs(RS$s(gs(a4HCS0IS1S:S$s(hs(bs(]s(Vs(RZSH*)'&$#J)&#S#;ON*R+#.#s)^>#?'#/s(Ns(`,E&$$#3Cs(Q@HHHCCCS4IIIS5S<Os(R#Ns(ds(`Us)9*3C+LCHCCS9s)=Is);s([,,#4HCS2IS3S;0*&,%#J,)#MUSIR$Es%MEEs%@(Es%A#Cs%As%B%$#$s%DE#Cs%DE%$#5&#-S=7s%V#,E#EEs%?(Es%@#Cs%@s%A%$#$s%CE#Cs%CE%$#5&#,Es(TMs(Ds*%$Es(E$Es(4k##s([#k##%#Ns(@s**Fs*+s(8/#s%A#Cs(;#k##s(V#Os(=s*/$Es(7(s(8s*1%$#k##s(T#Ps(<s*4(s*5s(6$s(7E%$#k##s(P#Qs(;s*9#Cs%;Ek##s(d#Rs%As*<#Cs%=s&[k##s(g#.s&]s*?*SW+#6#s*B0Cs%Bs(40Cs(=#9#S,0Cs(?s(79#S,1S%%s(61S%$#1S%s%9#1S%(#WSUCs'_s'c&Cs(.S)#'s(0GDDF#K&Cs'iS*%'s(2GDDF#K2s(3GDDF%#Hs(4GDDFS=&Cs'mS*s(4's(6GDDF#K2s(7GDDF%#Ks(8GDDF'#BCs'ns'v&C#S's(&'s(;GDDF#K&Cs'qS's'm's(=GDDF#K&Cs'oS)''s(?GDDF#K2s(@GDDF%#)s(AGDDF#s(<s'h)s(BGDDF)s(=#)s(CGDDFs'vs(>#)s(DGDDF.s(?#)s(EGDDFs%4s(@#)s(FGDDFs%=s(A#)s(GGDDFs%Cs(B#l#)#s'gs'al#*s%Js(J#l#+?s(S#j#,C#j#-C#j#.C#j#/C#j#0C#j#1C#j#2C#j#HC#j#3P#j#4P#j#5P#j#MP#7JS$(E##CS&$%$#%S@s'\5$#/NJ$#R$OR/ON(R#%%#k###s'Yk##(#k##s'b#k##,#k##s$|#k##s%&#k##s%+#k#,C#k#-C#k#.C#k#/C#k#0C#k#1C#k#2C#k#HC#k#3P#k#4P#k#5P#k#MP#-SV7s$g#$#E*St+#gL%s'_s'^s']Q#S#Rs$k's$jS-JNS/S.S>SASBl#6s#()#l#7s#[C#l#8s#_C#l#Is#cs#a#l#9s#gs#e#l#;s#ms#i#l#<s#ss#o#l#=s#ys#u#l#Js$#s#{#l#Ks$%C#l#:s$.s$'#l#?s$0C#l#@s$;s$4#l#As$>s$=#l#Bs$?s$>#l#Cs$@s$?#l#Ds$Bs$I#l#Es$Ss$W#Ts$cs$`s$^#VMs$i#ZSXHs$is$f#S$Ll#=s$ls'J#CMs+/ZSXS(S+s'O$#Ll#=s'\s'[#USMSD1SDJ#VSu#S&#s'[#s'Vm#'#j#Ns+U#j#Os+Z#j#Ps+c#j#LH#j#%H#j#QH#j#RSD##"). Qed.

(* [comment removed for export] *)
Ltac gall_vm :=
  cbn [gall]; repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with |- gtree _ ?d _ = _ => vm_cast_no_check (@eq_refl ztr (ctree d)) end.
Ltac gallv_vm :=
  cbn [gallv]; repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with |- gtree ?s ?d ?a = _ => vm_cast_no_check (@eq_refl ztr (vtree s d a)) end.
