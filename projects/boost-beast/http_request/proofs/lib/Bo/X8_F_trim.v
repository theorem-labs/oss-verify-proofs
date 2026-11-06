(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import ZBridge CellsX Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AXRep AXRep2.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition is_ws (b : byte) : bool := (zb b =? 32) || (zb b =? 9).
Fixpoint drop_ws (bs : list byte) : list byte :=
  match bs with [] => [] | b :: bs' => if is_ws b then drop_ws bs' else bs end.
Definition trimB (bs : list byte) : list byte := rev (drop_ws (rev bs)).
Definition trim (bs : list byte) : list byte := trimB (drop_ws bs).

Lemma drop_ws_suffix : forall bs, exists k, drop_ws bs = skipn k bs.
Proof.
  induction bs as [|b bs IH]; [exists 0%nat; reflexivity|]. cbn. destruct (is_ws b).
  - destruct IH as [k E]. exists (S k). exact E.
  - exists 0%nat. reflexivity.
Qed.
Lemma drop_ws_length : forall bs, (length (drop_ws bs) <= length bs)%nat.
Proof. intros bs. destruct (drop_ws_suffix bs) as [k E]. rewrite E, length_skipn. lia. Qed.
Lemma trimB_length : forall bs, (length (trimB bs) <= length bs)%nat.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_F_trim.drop_ws); constr:(@Stdlib.Lists.List.rev); constr:(@Corelib.Init.Peano.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_F_trim.drop_ws_length); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.Lists.List.length_rev); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_F_trim.trimB)|] [|@n; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @cstr0; @cstr; @K0; @K; @bs|] "#$+#*#Z#?###$#%#3#N#D#O#1#-#:#7#=#<#&#C#F#R#M#X#Y#)#/#.#8#9#>#@#B#'#E#H#I#G#J#L#Q#S#P#T#U#K#V#[#Z#\#W#;#2#]#4#6#5#0#A+#U%#V%#.%#/$#W$#0%#X$#Y%)K)#)#US)#US*#UL#$$D'##&##'E%D#j#$G#US+(#+)%(#$-E#.#$/F'##1#%#Dj#$G#VM4EZS,G)$D0#'+#7#%#3#9F%+#&,&%($#*C%*C%`S-GCNOPS.1'$)&#XS/)&#D#BQUR#&$(I#$s#&S0'##s#(#UR#&$(I#US1S#ULS#VS2CFUS3CXS4C$E#US5CUS6CVS$CKVS$Cs#8XS7C$S8#[S9&S%HHJ#S:US;H\S<(S%HHJ$#$VS=)J*S&S'VS>DFWS?S&#S'm$%#WS@CIEXSADF$#l#%*)#l#&32#l#'87#j#(C#j#)C#(DE(EFk##$#k#(C#k#)C##s#JS(&#$s#LS('##s#N#&#WD'#Ql#*/*#l#+s#+s#)#l#,s#2s#0#l#-s#5s#9#XSBs#=s#:s#7#l#.s#Cs#@#l#.s#Os#M#$s#Xs#U#s#Y#VMs#Zs#WZSCGs#Ws#T&$#USDD#s#]##s#^D%$#m#'#j#/s#`##"). Qed.
Lemma trim_length : forall bs, (length (trim bs) <= length bs)%nat.
Proof. intros bs. unfold trim. pose proof (trimB_length (drop_ws bs)). pose proof (drop_ws_length bs). lia. Qed.
Lemma trimB_snoc : forall l b, trimB (l ++ [b]) = if is_ws b then trimB l else l ++ [b].
Proof.
  intros l b. unfold trimB. rewrite rev_app_distr. cbn. destruct (is_ws b); [reflexivity|].
  cbn. rewrite rev_involutive. reflexivity.
Qed.
Lemma trimB_prefix : forall bs, exists k, (k <= length bs)%nat /\ trimB bs = firstn k bs.
Proof.
  induction bs as [|b bs IH] using rev_ind; [exists 0%nat; split; [cbn; lia| reflexivity]|].
  rewrite trimB_snoc, length_app. cbn [length]. destruct (is_ws b).
  - destruct IH as (k & K & E). exists k. split; [lia|]. rewrite firstn_app.
    replace (k - length bs)%nat with 0%nat by lia. cbn. rewrite app_nil_r. exact E.
  - exists (length bs + 1)%nat. split; [lia|]. rewrite firstn_app, firstn_all2 by lia.
    replace (length bs + 1 - length bs)%nat with 1%nat by lia. reflexivity.
Qed.
Lemma firstn_S_snoc : forall {A} (l : list A) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof.
  intros A l. induction l as [|y l IH]; intros [|k] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - f_equal. apply IH. exact H.
Qed.
Lemma is_ws_spec : forall b, is_ws b = true <-> (zb b = 32 \/ zb b = 9).
Proof. ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.orb); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.zb); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.Bool.Bool.orb_true_iff); constr:(@Corelib.Classes.Morphisms_Prop.or_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Stdlib.ZArith.BinInt.Z.eqb_eq); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.or_ind); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.or_intror); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_F_trim.is_ws)|] [|@lemma; @B; @H0; @H; @b|] "##k#&#F#&#-###/#5#9#8#3#0#=#<#@#6#,#*#)#4#$#:#;#>#?#B#A#%#E#F#D#C#G#.#+#1#2#7*#A&#B$#/%#C%#$%#D$#E,$P$#$#UQ#UR#(E$&$#UJ#&&#US#+UJ#&)#VK&##F#G#F(G#F&G%$#'&#(S$&#.&$,VK$##F#G#F&G#F&G%$##H*5#H+3%$#VS%C#)CDI*'E$$#j#$0#VS&:7#H?<'6#%+-WS'CDS(XLCD#/ZM1.E00#)CDI0&#--,j#$(#VNs#'s#$#Hs#(B'>#k#%CCXS)CCDDXLCD,6_S*C%D$OM7#96E)CDI/6#665j#$(#VNs#0s#*%4+k###:(S+#H#s#1#H$s#/WS,$#Ej#&A#WS-&%Ej#&B#ZS.s#$s##B%#Ej#',#XS/,,##V0/#V:9#Vs#$s###US0E#F#G'#3m#&#j#(s#E##"). Qed.
Lemma trimB_nonnil : forall bs, trimB bs <> [] -> bs <> [].
Proof. intros bs H ->. apply H. reflexivity. Qed.

Lemma land_neg8 : forall x, 0 <= x -> Z.land x (-8) = x - x mod 8.
Proof.
  intros x Hx. change (-8) with (Z.lnot (Z.ones 3)). rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^3) with 8. rewrite Zmod_eq by lia. lia.
Qed.
Lemma land_M8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
  intros x Hx. change 18446744073709551608 with (Z.land (Z.ones 64) (-8)).
  rewrite Z.land_assoc, Z.land_ones, Z.mod_small by lia. apply land_neg8. lia.
Qed.
Lemma land_M1 : forall a, 0 <= a < 2^64 -> Z.land a 18446744073709551615 = a.
Proof. intros a Ha. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_M1l : forall a, 0 <= a < 2^64 -> Z.land 18446744073709551615 a = a.
Proof. intros a Ha. rewrite Z.land_comm. apply land_M1. exact Ha. Qed.
Lemma land_FFFF : forall a, 0 <= a < 2^16 -> Z.land a 65535 = a.
Proof. intros a Ha. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma tc_size_eq : forall name tv, zlength name <= 65533 -> zlength tv <= 65535 ->
  Z.land (Z.land (zlength name + 2 + Z.land (zlength tv) 65535 + 65) 18446744073709551615) 18446744073709551608
  = elem_block_size name tv.
Proof.
  intros name tv HN HV. unfold elem_block_size, zlength in *.
  rewrite land_FFFF, land_M1, land_M8, land_neg8 by lia. reflexivity.
Qed.
Lemma elem_block_size_range : forall name tv,
  zlength name + zlength tv + 60 <= elem_block_size name tv <= zlength name + zlength tv + 67.
Proof. intros name tv. unfold elem_block_size, zlength. rewrite land_neg8 by lia. Z.div_mod_to_equations. lia. Qed.
Lemma elem_block_size_al8 : forall name tv, elem_block_size name tv mod 8 = 0.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_F_trim.land_neg8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.elem_block_size)|] [|@z; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__arith; @cstr0; @cstr; @r0; @q0; @H8; @H7; @H6; @H5; @H4; @r; @q; @H3; @H2; @H1; @H0; @H; @tv; @name|] "#&u#6$%#?#i#H#j#h#%#p###$#&#'#=#)#V#o#(#w#9#I#M#Q#R#S#*#,#-#.#3#[#^#Y#_#`#W#U#t#u#|#}#;#:#J#+#/#0#1#Z#a#d#e#g#k#q#v#x#y#{#~$##z$$#4#5#2$%$&#>$'#A#F#C#B#G#P#m#l#@#r#f#N#<#L#X#s#O#]#\#K#T#c#b#n#D#E=#g%#h%#i%#j$#k&#l%#m'#n*#o%#p&#q+#r%#s$#t%#u&#v%#w%#x$#y%#z%#{$#|%#}'#~%$#$$$$/N/#/#US:#US;#US$#%$K&#;*#$#%(J&##%#/-/#<#;##'#;2$$#+%#$J%'C#Ej#$C#VS%&('C)EUS<#%9H&###7##9##1$#0+$#0#263#$%4#$#'C'#k##/#VS&)8.E9%s#(L&###s#&##3##@$#?+$#$#A(E#.$s##3$#k##.#VS'(s#&.s#'E%s#6M&###s#4##2##s#.$#s#-+$#$#s#/.s#0#($E3$#k##.#VS((s#4%s#CR&###s#A##1##s#;$#s#:+$#0#s#<'C#Ek##s#7#VS)&s#?%s#NO&###s#L##/##s#F$#s#E+$#$#s#G'C#$k##s#B#0&s#J%s#YS*&###s#W##/##s#Q$#s#P+$#$#s#R%s#aS=&###s#_##,##s#YVS%#s#X%s#gS+&###s#e##*##s#_0#s#^6s#_#$%s#`#$#'C'#k##s#[#VS&)s#d%s#sS,&###s#q##0##s#k$#s#j(E#.$s#l3$#k##s#W#VS'(s#o%s#~S-&###s#|##/##s#v$#s#u.s#v#($E3$#k##s#T#VS((s#z%s$-S>&###s$+##/##s$%0#s$$'C#Ek##s#{#VS)&s$'%s$6S?&###s$4##-##s$.$#s$-'C#$k##s$(#0&s$0%s$?S@&###s$=##-##s$7$#s$67((E(%s$GS.7#&$(E#US/NVSAC#4S04#4#4#5C#WS1C(#5C'5C)1C$#1C&#4)5C#WS1C/(1C#(1C%#5CS01C+#VS2#S3VS4&#VS4,#USBPWS5P$#US$P8CM8CO9C$H#8CRUSCC9C$L#9C&K#USDCUSEC:Cs$_:CE)C$Q#*&GDDF#IZSF'GDDF#USGD2Cs$w:Cs$p,C$#<N2C#,C%#:Cs$m,C$#/'2C#WS6C2#2Cs%%,C$#)C(Q#*7GDDF#I-8GDDF32#)C7S78*:GDDF#I2CN)C:S##*=GDDF#I)C%S7=*?GDDF#I[SH@GDDF%#-AGDDF);#WSIC40<s%52C#WS6Cs#$#,C#-)C'Q#*s#(GDDF#I-s#)GDDFs#$s###)C1Qs#(*s#+GDDF#I-s#,GDDF%s#&#-s#-GDDF.s#'#-s#.GDDF8s#(#VSJs#/FVSKS8S9VSLJH'S8#S9m$%#WSMCEKXSNJH$#l#%*)#l#&s#9s#8#l#'s#Bs#A#j#(C#j#)C#j#*C#j#+C#j#,C#j#-C#k##s%8SO#Hs%J##L##s%D6s%CO##M'C%#k##)#(EH.Hs%H3$#k##s%3##Ms%U##R##s%O+#O6s%OS*##L'C%#k##5#'CLEk##$#k##-#k##2#k#(C#k#)C#k#*C#k#+C#k#,C#k#-C#%s%kSP&#%s%mSQ&#]JMS-L%#S,S+SRS.l#.s#&(#l#/s$+s$)#l#0s$/s$.#l#1s$1C#l#2s$8C#l#3s$Bs$:#l#4s$Ls$D#l#5s$Xs$N#l#6s$ds$Z#l#7s$qs$f#l#8s$xC#l#9s%%C#l#:s%1s%'#l#;s%=s%3#l#<s%Ls%?#l#=s%[s%N#l#>s%ls%]#US/s&'VSSs%u#7s%}(Es%}7s%n(Es%n1Cs$6s$,VS2#S3WS5P#s$*8CH9C#Ks$%)Cs#|S#s#w*s$#GDDF#I,Cs#gs#x,C#s#z,C#s#u)Cs$%S##*s$(GDDF#I-s$)GDDF(s$##-s$*GDDFs#ks$$#l#%#s#Zs#Tl#&-s$-#l#'0s$6#j#(C#j#)C#(EJ(Es#Mk##s#I#k##%#k#(C#k#)C#XJs%ys%kKHl#.*$#l#/?>#l#0BA#VSTs&;#ZSUCs&9s&6s#'s#%#VSVKJ$#s&='C#Em#&#j#?s&M#j#@s&N##"). Qed.
