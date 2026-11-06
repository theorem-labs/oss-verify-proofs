(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.

Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_ok s base
      else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
  end.

Lemma scanN_sound : forall s fuel base n,
  scanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
      destruct (hex_byte_at s base); [discriminate|discriminate].
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Numbers.BinNums.Z Sort Prop.

(* [comment removed for export] *)
Lemma segment_byte_at_some1 : forall s (n : N) (off : N),
  scanN s 64 0 n = true ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  (Z.of_N off < Z.of_N n)%Z ->
  segment_byte_at [s] off <> None.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Strings.PrimString.string); constr:(@Corelib.Numbers.BinNums.N); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexScan.scanN); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.BinNums.N0); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.NArith.BinNat.N.le); constr:(@Stdlib.ZArith.BinInt.Z.to_N); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z); constr:(@Corelib.Strings.PrimString.length); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.of_N); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Stdlib.NArith.BinNat.N.ltb); constr:(@kc__1); constr:(@Stdlib.NArith.BinNat.N.lt); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.NArith.BinNat.N.ltb_lt); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.Znat.N2Z.inj_lt); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@kc__2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_N_Z); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.Znat.N2Z.inj_le); constr:(@Stdlib.ZArith.Znat.N2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.hex_byte_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexScan.scanN_sound); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.segment_byte_at)|] [|@m; @n; @x; @z; @p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__p1; @__p2; @__p3; @__arith; @r; @q; @H4; @H3; @H2; @H0; @H; @__sat2; @z1; @H1; @cstr0; @cstr; @Hn0; @b; @Hoff; @Hn; @Hs; @off; @s|] "#'i#8$A#X$%#V$&$$###%#(#$#<#>#)$+#C#&#'#M#8#*#,#_#`#-#s$*#K#D#E#Q#L#2$.$3#;#A#B#I#\#[#Y#c#g#.#0#l#k#5#t#w#x$)$,$0#T#?#S#P#^#a#d#b#e#f#h#/#i#n#1#o#p#3#q#4#y#|#}$##+$2$5$4$6$7$9$:$8$;#7#6#N$?$>$=$@$A$<$B#@#=#H#G$($'#~#F#R#U#Z$/#O#]#m#v#u#J#{#z#W#j#r$1$-A$($$)&$*$$+$#@%#K%$,'$-*$.+$/%$0%$1%#3$$2%$3%$4%$5'$6%$7%$8&$9$#>$#?%$:%$;'$</$=$$>&$?)$@*#S5##############################################################################################################################XSII#S6K$M#P%Q&#7S,US7#,%#8#VS-I#/I/Q'$#%J&#,#+8#2Q#2KH$M#P9IKk##$#9KH2IK$M#Pk##%#-'#2QI$M#Pk##+#j##&#j##$Hj##-#VSJKHYSK/+&$#j#$L#j#%L#k#$L.k#%L#%N&#,#s#%8#9R#/R.E&'$#0C%j#&CH.EHj#&C#8H3LCSL#3CCS'H.E#$C%#j#'C#3CCS'E.E#0C#US7H3CCS'#.E#0C#j#(S(#USMH3CCS'#.E#0C#j#(S(#YS80-(#Hj#&C#0CA`S9CLCCS.;S#9$BB#<LCS/S#S0S:R@=B?#VS-Js##/J(#B0C$U?s#(U2Hj#(S(#U/Hj#(S(#YS8>;%#Hj#&C#`S9CLCCS.s#(S#s#&#s#/s#/0<LCS-S#S;SNJ-+s#/*#XSO/-#IUSPN/N(E#%S&&#,#s#ZVSQE#'E$.E%$C#&-%#((E$C&E-$#VS<&#%S)&#,#s#f.E#%S=&#VSR#s#j(E$(Es#l%S>&#,#s#o(E#k##'#k##)#%SS&#VST#s#u$Cs#vE=#VS?s#x+4-s#yVS@$#$C/#k##'#VSU1s#}'Es#~%SV&#4#s$%(E#'$s$'-$#k##)#VSW(s$*'s$+E%S1&#4#s$.'s$/#($E-$#k##)#VSX(s$3%SY&#,#s$6$C#Ek##@#VSZ&s$9%S[&#4#s$<$C#$k##s#&#,&s$?%SA&#4#s$B5Cs%)5Cs%+5Cs%-5Cs%/6C$#6C&#6C(#VSB#SC5CS56C(#6C*#VSB#SCUSDS*>S*$#>S*)#US\S*:CR:CN;C$I#:CJUS]C;C$Q#;C&K#US^CUS_CVSECEVSECs$])C$S+#*&GDDF#OUSFDUSGS,7#1C#)C*S2#*,GDDF#O?-GDDFS`@.GDDF$#+/GDDF+*#)C.S3/*1GDDF#OZSa2GDDF#USGs$m1C#7s$o1C#WSbC5#WScC#0)C'S3#*:GDDF#O+;GDDF+6#)C;S+(*=GDDF#O?>GDDFS&@?GDDF$#?@GDDFS)1Cs${)C#S3A*s##GDDF#O@s#$GDDF&#[Sds#%GDDF(#1CS,)Cs#&S2#*s#(GDDF#O1Cs##)C#S2+*s#+GDDF#O)C(S+%*s#-GDDF#O)C*S+/*s#/GDDF#O+s#0GDDF%s#+#+s#1GDDF(s#,#+s#2GDDF,s#-#+s#3GDDF0s#.#+s#4GDDF;s#/#+s#5GDDFs#(s#0#VSes#6F0MPVSfHI$M#Pm$%#WSgCEKXShHI$#l#)*)#l#*s#@s#?#l#+s#Is#H#j#,C#j#-C#j#.C#j#/C#j#0C#j#1C#j#2S$#j#3S$#j#4S$#(EN-#S%k##s$(#k##s$1SiVS?s%JJVS@#S%$CN#k##&#'EJ-#S&$CQE-S)#VS<%#(EQ(NJ'JS%'NS%k##$#k##&#k##(#k##*#k##0#k##6#k#,C#k#-C#k#.C#k#/C#k#0C#k#1C#k#2S$#k#3S$#k#4S$#(IE$CS&I'Ks%h%Sj&#/Sk/SAcH)('K%I$S&#NS%S)S=S>S1l#5s#++#l#6s$/C#l#7s$3C#l#8s$:s$5#l#9s$As$<#l#:s$Ks$C#l#;s$Us$M#l#<s$^s$W#l#=s$js$b#l#>s$nC#l#?s${s$s#l#@s%&s%$#l#As%'s%%#l#Bs%)s%4#XSHs%Ws%Ts%8#WHRs%Y#l#<s%`s%^#XSlMs%tP#$MPs%u7s#qUSm#USn#USo#VSpS%JUSF%nM#$##%H#%#$##$&#$=#j#CM#9RJ's%fs%F<LCS/S#S0S:Rs%gs%dJs%Gs%E:CI;C#Ks$:+s$7GDDFs#fs$2s#fl#)#s#`s#Zl#*%s$:#l#+s$Fs$C#j#,C#j#-C#'HK'KIk##$#k#,C#k#-C#WHs#2s#1S1l#5)$#l#6s$]C#l#7s$aC#l#8s$hs$c#l#9s$os$j#l#:s$ys$q#l#;s%'s${#l#<s%0s%)#l#=s%<s%4#l#>s%@C#l#?s%Ms%E#l#@s%Ts%R#l#As%Us%S#l#Bs%Ws%b#XSHA@?#[SqNs&US6JQR#2Rs&,ZSrMPs#%$#Hl#<s#1s#0#USDS4>S4J#VSs#Q$s#0#s#.=#m#(#j#Ds&S#j#Es&W#j#Fs&_#j#GL#j#%L#j#HS4##"). Qed.

(* [comment removed for export] *)
Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f => if N.eqb n 0 then true
           else if N.eqb n 1 then match hex_byte_at s base with Some b => Z.eqb (bv_unsigned b) 0 | None => false end
           else let hh := N.div2 n in (zscanN s f base hh && zscanN s f (base + hh)%N (n - hh)%N)%bool
  end.
Lemma zscanN_sound : forall s fuel base n, zscanN s fuel base n = true ->
  forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|]. destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. destruct (hex_byte_at s base) as [b|]; [|discriminate].
      apply Z.eqb_eq in H. f_equal. rewrite <- H. symmetry. apply definitions.Z_to_bv_bv_unsigned.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (hh := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i hh) as [Hl|Hge]; [exact (IH _ _ H1 i Hl)|].
      specialize (IH _ _ H2 (i - hh)%N ltac:(lia)). rewrite <- IH. f_equal. lia.
Qed.
Lemma zscanN_ok : forall s fuel base n, zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.
Proof. intros s fuel base n H i Hi. rewrite (zscanN_sound s fuel base n H i Hi). discriminate. Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_some_pt : forall s (n : N) (off : N),
  (forall i, (i < n)%N -> hex_byte_at s i <> None) ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  (Z.of_N off < Z.of_N n)%Z ->
  segment_byte_at [s] off <> None.
Proof.
  intros s n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
    by (symmetry; apply N.ltb_lt; lia).
  apply Hs. lia.
Qed.
