(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsIface.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TRLIST : list (list Z) :=
  [ [0x74688]
  ; [0x74688; 0xa4068]
  ; [0x74688; 0xa4198]
  ; [0x74688; 0xa4364]
  ; [0x74688; 0xa4e0c]
  ; [0x74688; 0xa4e0c; 0xa4338]
  ; [0x74688; 0xa5084]
  ; [0x74688; 0xa5084; 0xa4338]
  ; [0x74688; 0xa5140]
  ; [0x74688; 0xa5140; 0xa4338]
  ; [0x74688; 0xa51a8]
  ; [0x74688; 0xa51a8; 0xa4338]
  ; [0x74688; 0xa51ec]
  ; [0x74688; 0xa51ec; 0xa4338]
  ; [0x74688; 0xa6d00]
  ; [0x74688; 0xa728c]
  ; [0x74688; 0xa75a4]
  ; [0x74688; 0xaa8d8]
  ; [0x74688; 0xad884]
  ; [0x74688; 0xb9b20]
  ; [0x74688; 0xba504]
  ; [0x74688; 0xba5d8]
  ; [0x74688; 0xba6e4]
  ; [0x74688; 0xbb7a8]
  ; [0x74688; 0xc3bf0]
  ; [0x74688; 0xc3bf0; 0xa5624]
  ; [0x74688; 0xc3bf0; 0xa5624; 0xa4e4c]
  ; [0x74688; 0xc3bf0; 0xa5624; 0xa4e4c; 0xa4338]
  ; [0x74688; 0xc3bf0; 0xd004c]
  ; [0x74688; 0xc43dc]
  ; [0x74688; 0xc43dc; 0xc376c]
  ; [0x74688; 0xc5614]
  ; [0x74688; 0xc5770]
  ; [0x74688; 0xc5b4c]
  ; [0x74688; 0xc5b4c; 0xa4e0c]
  ; [0x74688; 0xc5b4c; 0xa4e0c; 0xa4338]
  ; [0x74688; 0xc5b4c; 0xa51a8]
  ; [0x74688; 0xc5b4c; 0xa51a8; 0xa4338]
  ; [0x74688; 0xc5b4c; 0xa6be4]
  ; [0x74688; 0xc5f68]
  ; [0x74688; 0xc61f4]
  ; [0x74688; 0xc668c]
  ; [0x74688; 0xc66c4]
  ; [0x74688; 0xc767c]
  ; [0x74688; 0xc7cec]
  ; [0x74688; 0xc7cec; 0xc7944]
  ; [0x74688; 0xc7cec; 0xc79c0]
  ; [0x74688; 0xc9ba4]
  ; [0x74688; 0xc9c0c]
  ; [0x74688; 0xcebe0]
  ; [0x74688; 0xcebe0; 0xa5f44]
  ; [0x74688; 0xcf0b8]
  ; [0x74688; 0xf666c]
  ; [0x74688; 0xf6968]
  ; [0x74688; 0xf9a90]
  ; [0x74688; 0xf9b58]
  ; [0x747e8]
  ; [0x747e8; 0xa3ff0]
  ; [0x747e8; 0xa4044]
  ; [0x747e8; 0xa42d0]
  ; [0x747e8; 0x11876c]
  ; [0x747e8; 0x118784] ].

Lemma TRLIST_length : Z.of_nat (length TRLIST) = 62.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition APF_a4c70 : list (Z * list Z) :=
  [ (0x74688, [0xa4e0c])
  ; (0x74688, [0xa5084])
  ; (0x74688, [0xa5140])
  ; (0x74688, [0xa51a8])
  ; (0x74688, [0xa51ec])
  ; (0x74688, [0xc3bf0; 0xa5624; 0xa4e4c])
  ; (0x74688, [0xc5b4c; 0xa4e0c])
  ; (0x74688, [0xc5b4c; 0xa51a8]) ].
(* [comment removed for export] *)
Definition APF_c3ac8 : list (Z * list Z) :=
  [ (0x74688, [0xc3bf0]) ].
(* [comment removed for export] *)
Definition APF_a55fc : list (Z * list Z) :=
  [ (0x74688, [0xc3bf0; 0xa5624]) ].
(* [comment removed for export] *)
Definition APF_c41dc : list (Z * list Z) :=
  [ (0x74688, [0xc43dc]) ].
(* [comment removed for export] *)
Definition APF_ce8c4 : list (Z * list Z) :=
  [ (0x74688, [0xcebe0]) ].
(* [comment removed for export] *)
Definition APF_c59f4 : list (Z * list Z) :=
  [ (0x74688, [0xc5b4c]) ].
(* [comment removed for export] *)
Definition APF_c7bf0 : list (Z * list Z) :=
  [ (0x74688, [0xc7cec]) ].

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint inb (x : Z) (l : list Z) : bool :=
  match l with [] => false | y :: l' => if Z.eqb x y then true else inb x l' end.
Fixpoint list_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && list_eqb a' b'
  | _, _ => false
  end.
Fixpoint inlb (t : list Z) (L : list (list Z)) : bool :=
  match L with [] => false | u :: L' => if list_eqb t u then true else inlb t L' end.
(* [comment removed for export] *)
Fixpoint prefixes_inb (acc : list Z) (l : list Z) (L : list (list Z)) : bool :=
  match l with
  | [] => true
  | x :: l' => inlb (acc ++ [x]) L && prefixes_inb (acc ++ [x]) l' L
  end.
Definition trace_okb (L : list (list Z)) (pc0 : Z) (t : list Z) : bool :=
  negb (inb pc0 t) && prefixes_inb [] (pc0 :: t) L.
(* [comment removed for export] *)
Definition pf_okb0 (L : list (list Z)) (PF : list (Z * list Z)) (ra : Z) : bool :=
  forallb (fun pp : Z * list Z => trace_okb L (fst pp) (snd pp ++ [ra])) PF.

Lemma inb_false : forall x l, inb x l = false -> ~ In x l.
Proof.
  induction l as [|y l IH]; cbn; [tauto|]. destruct (Z.eqb_spec x y); [discriminate|]. intros H [E|K]; [congruence| exact (IH H K)].
Qed.
Lemma list_eqb_eq : forall a b, list_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [E R]. apply Z.eqb_eq in E. subst. f_equal. exact (IH _ R).
Qed.
Lemma inlb_In : forall t L, inlb t L = true -> In t L.
Proof.
  induction L as [|u L IH]; cbn; [discriminate|]. destruct (list_eqb t u) eqn:E.
  - intros _. left. symmetry. exact (list_eqb_eq _ _ E).
  - intros H. right. exact (IH H).
Qed.
Lemma prefixes_inb_sound : forall l acc L, prefixes_inb acc l L = true ->
  forall j, (1 <= j)%nat -> (j <= length l)%nat -> In (acc ++ firstn j l) L.
Proof.
  induction l as [|x l IH]; intros acc L H j Hj Hl; cbn in Hl; [lia|].
  cbn in H. apply andb_true_iff in H as [H1 H2].
  destruct j as [|j]; [lia|]. cbn [firstn]. destruct j as [|j'].
  - cbn [firstn]. exact (inlb_In _ _ H1).
  - replace (acc ++ x :: firstn (S j') l) with ((acc ++ [x]) ++ firstn (S j') l) by (rewrite <- app_assoc; reflexivity).
    apply (IH (acc ++ [x]) L H2); lia.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.

Lemma trace_okb_sound : forall L pc0 t, trace_okb L pc0 t = true -> trace_ok L pc0 t.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsTRList.trace_okb); constr:(@Corelib.Init.Datatypes.true); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.andb); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Bool.Bool.andb_true_iff); constr:(@Corelib.Init.Datatypes.negb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsTRList.inb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsTRList.prefixes_inb); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.trace_ok); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.Bool.Bool.negb_true_iff); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Lists.ListDef.firstn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsTRList.inb_false); constr:(@Stdlib.Arith.PeanoNat.Nat.le_gt_cases); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Peano.lt); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsTRList.prefixes_inb_sound); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Classes.Morphisms.subrelation_proper); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Stdlib.Sorting.Permutation.Permutation); constr:(@Corelib.Init.Logic.iff); constr:(@Stdlib.Sorting.Permutation.Permutation_in'); constr:(@Corelib.Program.Basics.flip); constr:(@Corelib.Program.Basics.impl); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Classes.Morphisms.subrelation_respectful); constr:(@Corelib.Classes.Morphisms.subrelation_refl); constr:(@Corelib.Classes.Morphisms.flip2); constr:(@Corelib.Classes.Morphisms.iff_flip_impl_subrelation); constr:(@Corelib.Classes.RelationClasses.symmetry); constr:(@Corelib.Classes.RelationClasses.eq_Symmetric); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.Equivalence_Reflexive); constr:(@Stdlib.Sorting.Permutation.Permutation_Equivalence); constr:(@Stdlib.Lists.List.firstn_all); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.Lists.List.firstn_all2); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Numbers.BinNums.xO)|] [|@b2; @b1; @b; @j; @LE; @l; @a; @y; @x; @lemma; @__ff; @__varmap; @__wit; @__x1; @__arith; @cstr1; @cstr0; @cstr; @Hj0; @GT0; @__x2; @GT; @o; @Hj; @H1; @H; @H2; @H0; @t; @pc0; @L|] "#&L#8$:#<###>#$#@#%#'$*#8#&#P#u$+#($#$)#)#4#d#Q#q#K#,#w$/#*#R#0#1#2#3#`#s#|#H#+#-#/#X#[#=#O#c#f#e#Y#{#6#5$$$%$.$0$'#7#?#D#J#L#N#S#.#U#V#_#a#b#g#h#j#i#n#m#l#k#]#o#r#y#z#}$&$($1$2$3$5$6$4$9$8$;$:$7#\#Z#M#I#W#C#E#x#T#v$-$,#F#G#^#~#;#B#A#t#p;#K&$(&#7%$)%#.$#6%$*%$+$$,%$-&$./$/'$0*$1%$2&#L&#P%$3'$4$$5$$6%$7($8%$9'6C6#WSJHFD#E#G7FD#E#G#EHG#EFG)$#k##&##EDG)&#7HF#E#Gk##%#)(##ELG)#-k##'#j##&#7LH#E#Gk##0#j###Fj##1#VSKFD83.)$#j#$E#j#%E#k#$E6k#%E#0LH*#US5C$CLH1$#IWD&#F#E'G#E%G)$#0IL*##E#G$CIL1-#P#E#G)&#WSLS#PIj##$#$CPI13#S##E#G0S#P*##E#G$CS,S#19#S6#E#G*D#E#G#EFS(k##$##EDS(*F#E#Gk##%#)'##EHS(k##&#j##%#*H#E#Gk##.#j###Fj##/#USMD81-)$#j#&E#k#&E30S)S6VD#H#E$S(2CS7S)USN#US-SO(#D$CS8SP,CF#2s#Z#S.k##&#k#'M#WSQS7S)D&C(VSRF#(F$3%FVS9$#$CS.S8&C#(H#3$HVS9$#$CS/S.,CL#2s#j#S0j##&#&C&(L#$CS0S/[S:#s#NS1S,ILDj#(%#U#Dj##/#3)L2s#tDS$j#)s#u#&C*,C#+#s#x#,k#)s#xKk#*s#z#k##s#zKUS;s#|USSs#}4s#}K#S24s$#&%#US<s$$USTs$%XSUKKKS=4s$&K(#4s$(-*#VS>s$)+VS>s$)+VS=DFj#+K#j#,K#XSVKS2#SW\S?s$.K00'S2+#\S?s$0522)0+#$CS1S0&C#,C#$USXs$4ZSYs$57#$&DUSZs$6WS[s$68#WS\s$79#XS]s$8:#S$aS^>9874S%,+)'S$S$#j#-A#VS_Cs#,&CS/US-#(s#G#US`S3'&9#$%%#+C&9D'j#,C#+C(`SaMMCCS-NN$Sb-)#-MCS&NS'S*s#Q+'-)#3s#2I's#3'IVS4$#+C%+C%-MCS@NS4Scs#8'$I&#XSA)&#D(s#ZP'P%6#+C$-MCS&NS'S*s#^84P%#XSA'%#I5S#'S#%Q#&CS$5#'$%Q#$CSBSC&C#5#'$%Q#US5SD6SDVSECFUSdCUSeCVSFCQVSGCS3.C$S+#/&RJJO#S%USfJVSFCs#0WSgC'#.C$S+#/+RJJO#S%\SH,RJJO('#VSh-O+EGVSiDH#E#Gm$%#WSjCQFXSkDH$#l#.*)#l#/76#l#0:9#j#1C#%QD9Fs#A%s#B#k##%#k#1C#&CSI'#VD#Hl#2+&#l#3s#(s#&#l#4s#.s#,#l#5s#3s#1#l#6s#5s#8#l#7s#<s#@#:s#Os#Ks#E#(s$9s#um#$#(s#ws#w%s#Gs#G-MCS&NS'S*s#ys#Hs#Es#ys#Hs#E$CSCS$&C#5#'$%Q#.Cs#/S+s#//s#2RJJO#S%l#.#s#(Bl#/s#6s#5#l#0s#9s#8#j#1C#%DDk#1C#$CSISB&C#'#UD#l#2)'#l#420#l#5s#Os#M#l#6s#Qs#T#l#7s#Xs#\#:;:9#[S:s$=s%,S1S,s$5=#Vs#qs#p#,CIs$?(s$8I%s#ds#c-MCS&NS'S*s$:s#es#bIs#ds#aVSECHUSlCXSmC$F#USnS3VSGC#.Cs#LSo#/s#ORJJO#S%.Cs#NS+%/s#QRJJO#S%\SHs#RRJJO%s#M#l#.#s#Hs#Bl#/+s#U#l#0s#Ys#X#j#1C#j#8C#VS4DF%FHk##$#k#1C#k#8C#'S)WD#s#%Il#2*%#l#4s#4s#2#l#5s#qs#o#l#6s#ss#v#l#7s#zs#~#:@?>#XSpCIs$_#ZSqs%ps$`s$Ys#$s###j#9s$\#U#Dj##s$k#ZSrs$ms$ls$gs$`#Dl#:s$ts$q#j#;s$}#j#'M#XSss%%s$zs$y#l#<s%)s%(#l#=s%-s%,#j#>s%B#j#<s%F#V#FDj##s%K#j##s%U#8s%Vs%Ss%P#Dl#=s%]s%Z#l#?s%fs%d#j#=s&$#j#@s&(#j#AC#j#Bs&)##"). Qed.

Lemma pf_okb0_sound : forall L PF ra, pf_okb0 L PF ra = true -> pf_ok L PF ra [].
Proof.
  intros L PF ra H. unfold pf_okb0 in H. unfold pf_ok. apply Forall_forall. intros pp IN.
  pose proof (proj1 (forallb_forall _ _) H pp IN) as Hp. cbn in Hp. cbn [map]. exact (trace_okb_sound _ _ _ Hp).
Qed.

(* [comment removed for export] *)
Lemma trace_ok_of_incl : forall L TRS pc0 t, incl L TRS -> trace_ok L pc0 t -> trace_ok TRS pc0 t.
Proof. intros L TRS pc0 t INC [NI OK]. split; [exact NI|]. intros j Hj. apply INC. exact (OK j Hj). Qed.
Lemma pf_ok_of_incl : forall L TRS PF ra CH, incl L TRS -> pf_ok L PF ra CH -> pf_ok TRS PF ra CH.
Proof.
  intros L TRS PF ra CH INC OK. unfold pf_ok in *. apply Forall_forall. intros pp IN.
  apply (trace_ok_of_incl L TRS); [exact INC|]. exact (proj1 (Forall_forall _ _) OK pp IN).
Qed.

(* [comment removed for export] *)
Lemma TRLIST_opnew : trace_ok TRLIST APC0_MALLOC [ARA_OPNEW].
Proof. apply trace_okb_sound. vm_compute. reflexivity. Qed.
Lemma TRLIST_driver :
  trace_ok TRLIST APC0_MALLOC [0xa3ff0] /\ trace_ok TRLIST APC0_MALLOC [0xa4044] /\ trace_ok TRLIST APC0_FREE [0xa4068]
  /\ trace_ok TRLIST APC0_FREE [0xa4198] /\ trace_ok TRLIST APC0_MALLOC [0xa42d0] /\ trace_ok TRLIST APC0_FREE [0xa4364]
  /\ pf_ok TRLIST APF_a4c70 0xa4338 [].
Proof.
  split; [apply trace_okb_sound; vm_compute; reflexivity|]. split; [apply trace_okb_sound; vm_compute; reflexivity|].
  split; [apply trace_okb_sound; vm_compute; reflexivity|]. split; [apply trace_okb_sound; vm_compute; reflexivity|].
  split; [apply trace_okb_sound; vm_compute; reflexivity|]. split; [apply trace_okb_sound; vm_compute; reflexivity|].
  apply pf_okb0_sound. vm_compute. reflexivity.
Qed.

