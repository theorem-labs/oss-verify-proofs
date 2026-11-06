(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsIface6.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition nthZ (j : nat) (l : list Z) : Z := nth j (l ++ [0]) 0.

Lemma nthZ_app_rest : forall j l rest, (j <= length l)%nat -> nth j (l ++ 0 :: rest) 0 = nthZ j l.
Proof.
  intros j l rest Hj. unfold nthZ. destruct (Nat.lt_ge_cases j (length l)) as [L|G].
  - rewrite !app_nth1 by lia. reflexivity.
  - assert (j = length l) as -> by lia. rewrite !app_nth2, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma nthZ_lt : forall j l, (j < length l)%nat -> nthZ j l = nth j l 0.
Proof. intros. unfold nthZ. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma nthZ_len : forall l, nthZ (length l) l = 0.
Proof. intros. unfold nthZ. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. Qed.
Lemma nthZ_cons_S : forall j c l, nthZ (S j) (c :: l) = nthZ j l.
Proof. intros. unfold nthZ. reflexivity. Qed.
Lemma nthZ_cons_O : forall c l, nthZ O (c :: l) = c.
Proof. intros. unfold nthZ. reflexivity. Qed.
Lemma nthZ_nil : forall j, nthZ j [] = 0.
Proof. intros j. unfold nthZ. cbn. destruct j as [|j]; [reflexivity|]. destruct j; reflexivity. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma nthZ_range : forall j l, Forall (fun c => 0 < c < 256) l -> 0 <= nthZ j l < 256.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.Arith.PeanoNat.Nat.lt_ge_cases); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Peano.lt); constr:(@Corelib.Init.Peano.le); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Lists.ListDef.nth); (KReplay.sort_at constr:(@Stdlib.Lists.List.Forall_nil_iff) [0]); constr:(@kc__2); constr:(@Stdlib.Lists.List.Forall_app); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.Lists.List.Forall_impl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_lt); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Lists.ListDef.Forall_cons); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Lists.ListDef.Forall_nil); constr:(@Corelib.Init.Logic.proj1); constr:(@Stdlib.Lists.List.Forall_nth); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.Lists.List.nth_overflow); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.N6_strcmp_spec.nthZ)|] [|@c; @l2; @l1; @P; @A; @__ff; @__varmap; @__wit; @__x1; @__arith; @cstr0; @cstr; @L0; @Ha; @a; @H; @d; @i; @F'; @L; @z; @G0; @__x2; @G; @o; @F; @l; @j|] "#%k#-#q#2#6#V###$#%#&#(#W#'#U#0#^#)#+#K#*#@#5#,#\#`#9#>#?#E#M#P#Q#[#]#S#c#d#A#C#7#=#:#-#G#F#R#T#_#a#f#e#g#b#I#i#j#h#H#l#k#n#q#p#o#m#B#r#3#<#4#;#8#N#O#Z#Y#1#D#L#J#X6#F%#c&#d&#2$#e%#f%#5%#g$#4%#h%#i$#j'#k*#l$#E%#m'#n/#o'#p*0C)DF*S)*#*#*#*#*#*#*#US7#)F#'-#j#$C#$C#FUS*CWS8CD#%CG#(C#VS9H#+H$1%HVS+$#%CH)(C#+I#1$IVS+$#%CI.2CL#D#D#)$7'$#j##(#(C(+L#k##FS:0G0H%IGF$IH#$LIH$LIG'$#k##&#$IHG$IHF'$#%LHG$LI#k##%#')#%JIH$JL#k##-#j##&#j##$Fj##/#XS;IHGFYS<1+&$#j#%8#j#&:#j#'<#j#(S,#k#%<0k#&>#k#'@#k#(S,##DF'#s#<j#$C#$C#J$C$s#:Us#>F%CS#s#<(C#+Q#&Q&%)$#,C%,C%3NCS$RS%S-Q'$)&#4)&#I-S&&S&#D#%CS&s#I(C#-#&$#D#US*S.0S.VS/CGUS=CUS>CVS0CDVS1CS).C$S'#/&MEEK#OVS0Cs#].C&S'#/)MEEK#O5*MEEK&#US?E.C+S(*/-MEEK#O5.MEEK#'\S2/MEEK'&#VS@0K,S3S4VSAFHWSBS3#S4m$%#WSCCDGXSDFH$#l#)*)#l#*:9#l#+=<#j#,C##DG)Gs#r'$#k##s#r#k#,C#VFJLl#-)$#l#.s#)s#'#l#/s#/s#-#l#0s#1s#5#j#1s#<#j#2C#ZSECs#zs#A#JL%CJs#x(C#+P#&P&%)$#,C%,C%3NCS$RS%S-P'$)&#4)&#G-S#&S##D#-s#J#Ds#HUSFC.Cs#7S(s#7/s#9MEEK#O.Cs#9S's#5/s#;MEEK#O5s#<MEEK%#l#)#s#/s#)l#*)s#?#l#+s#Cs#B##DD)Ds$;'$#l#-&#Fl#.10#l#/53#l#07;#VSGCs#aZSHCs#bDs$=$#XSIs#bs#as#$#YFCs#dJs$>#l#3s#ls#h#%CLs$@$Cs#g#$Cs#hs#(%CQs$C(C#+G#2CHs#[GUs#m#k##%#k#4C#k#5N#k##+#+Gs#m2CH,GUs#t#k##%#k#4C#k#5N#%CPs$R$Cs#y#k##%#WSJCs#{s#;[SK-$#FPDGl#6:8#j#7s$E#U#Fj##s$Q#1s$ILj#8Cs$'(C?1#J&$&J#$#,C%,C%3NCS5RS6SL)'$J&#4)&#F-P#Ds#J(C8-#&$#D#l#.%#s#7l#/)(#l#9+/#2CJs#1DVS/CHXSMC#Gs#HVS1Cs%$.Cs#}S(#/s$$MEEK#O\S2s$%MEEK#s#x#l#)#s#ts#nl#*(s$(#l#+s$,s$+#j#,C#j#:C##FG#GHk##$#k#,C#k#:C#&s#>WFs$<#Il#-*%#l#.<:#l#/@?#l#9Bs#&#XSNs#*s#'s#$#YSOCs#IJD#ZSPCDs#.<;#j#;s#0#U#Fj##s%%#ZSQs%'s%&s${s#4#Fl#<s%.s%+#VSRHG#D#)$s%:'$#m#'#j#=s%9#j#>s%H#j#?N##"). Qed.

(* [comment removed for export] *)
Fixpoint cmpi (e t : list Z) : nat :=
  match e, t with
  | c1 :: e', c2 :: t' => if Z.eqb c1 c2 then S (cmpi e' t') else O
  | _, _ => O
  end.

Lemma cmpi_le : forall e t, (cmpi e t <= length e /\ cmpi e t <= length t)%nat.
Proof.
  induction e as [|c1 e IH]; intros t; [cbn; lia|]. destruct t as [|c2 t]; cbn; [lia|].
  destruct (Z.eqb_spec c1 c2); [|lia]. specialize (IH t). lia.
Qed.

(* [comment removed for export] *)
Lemma cmpi_prefix : forall e t j, (j < cmpi e t)%nat -> nthZ j e = nthZ j t /\ (Forall (fun c => 0 < c < 256) e -> nthZ j e <> 0).
Proof.
  induction e as [|c1 e IH]; intros t j Hj; [cbn in Hj; lia|]. destruct t as [|c2 t]; [cbn in Hj; lia|].
  cbn in Hj. destruct (Z.eqb_spec c1 c2) as [E|NE]; [|lia]. subst c2.
  destruct j as [|j].
  - rewrite !nthZ_cons_O. split; [reflexivity|]. intros F. inversion F; subst. lia.
  - rewrite !nthZ_cons_S. destruct (IH t j ltac:(lia)) as [A B]. split; [exact A|]. intros F. apply B. inversion F; assumption.
Qed.

(* [comment removed for export] *)
Lemma cmpi_stop : forall e t, Forall (fun c => 0 < c < 256) t ->
  nthZ (cmpi e t) e = 0 \/ nthZ (cmpi e t) e <> nthZ (cmpi e t) t.
Proof.
  induction e as [|c1 e IH]; intros t FT; [left; apply nthZ_nil|]. destruct t as [|c2 t].
  - cbn [cmpi]. rewrite nthZ_cons_O, nthZ_nil. destruct (Z.eq_dec c1 0) as [E|NE]; [left; exact E| right; exact NE].
  - cbn [cmpi]. destruct (Z.eqb_spec c1 c2) as [E|NE].
    + rewrite !nthZ_cons_S. apply IH. inversion FT; assumption.
    + rewrite !nthZ_cons_O. right. exact NE.
Qed.

(* [comment removed for export] *)
Lemma zstrcmp_at : forall e t, Forall (fun c => 0 < c < 256) e -> Forall (fun c => 0 < c < 256) t ->
  zstrcmp e t = (if nthZ (cmpi e t) e <? nthZ (cmpi e t) t then -1 else if nthZ (cmpi e t) t <? nthZ (cmpi e t) e then 1 else 0).
Proof.
  induction e as [|c1 e IH]; intros t FE FT.
  - destruct t as [|c2 t]; cbn [zstrcmp cmpi]; rewrite ?nthZ_nil, ?nthZ_cons_O.
    + reflexivity.
    + inversion FT; subst. destruct (Z.ltb_spec 0 c2); [reflexivity| lia].
  - destruct t as [|c2 t]; cbn [zstrcmp cmpi].
    + rewrite nthZ_nil, nthZ_cons_O. inversion FE; subst. destruct (Z.ltb_spec c1 0); [lia|]. destruct (Z.ltb_spec 0 c1); [reflexivity| lia].
    + destruct (Z.eqb_spec c1 c2) as [E|NE].
      * subst c2. rewrite !nthZ_cons_S. apply IH; [inversion FE| inversion FT]; assumption.
      * rewrite !nthZ_cons_O. destruct (Z.ltb_spec c1 c2); [reflexivity|]. destruct (Z.ltb_spec c2 c1); [reflexivity| lia].
Qed.

Lemma zstrcmp_range : forall e t, zstrcmp e t = -1 \/ zstrcmp e t = 0 \/ zstrcmp e t = 1.
Proof.
  induction e as [|c1 e IH]; intros t; destruct t as [|c2 t]; cbn [zstrcmp]; try lia.
  destruct (Z.eqb c1 c2); [apply IH|]. destruct (Z.ltb c1 c2); lia.
Qed.

Lemma zstrcmp_eq0 : forall e t, zstrcmp e t = 0 <-> e = t.
Proof.
  induction e as [|c1 e IH]; intros t; destruct t as [|c2 t]; cbn [zstrcmp].
  - tauto.
  - split; [lia| discriminate].
  - split; [lia| discriminate].
  - destruct (Z.eqb_spec c1 c2) as [E|NE].
    + subst c2. rewrite IH. split; [intros ->; reflexivity| intros E; injection E; auto].
    + destruct (Z.ltb c1 c2); split; try lia; intros E; injection E; intros; subst; lia.
Qed.
