(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2X SymExec2SoundX SymRunX SymPackX RefMemcpyLib AgentLib.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require AsScLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Scheme kc__1 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma land_m8 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.bits_inj'); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.ldiff); constr:(@Stdlib.ZArith.BinInt.Z.ones); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.testbit); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.negb); constr:(@Stdlib.ZArith.BinInt.Z.ltb_spec); constr:(@Corelib.Init.Datatypes.BoolSpec); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.Bool.Bool.andb_true_l); constr:(@Stdlib.ZArith.BinInt.Z.ones_spec_low); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.eq_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@Corelib.Init.Logic.not); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.bits_0); constr:(@Stdlib.ZArith.BinInt.Z.bits_above_log2); constr:(@Stdlib.micromega.Tauto.X); constr:(@kc__2); constr:(@Stdlib.ZArith.BinInt.Z.log2); constr:(@Stdlib.ZArith.BinInt.Z.log2_lt_pow2); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.Bool.Bool.andb_false_r); constr:(@Stdlib.ZArith.BinInt.Z.ones_spec_high); constr:(@Stdlib.ZArith.BinInt.Z.ldiff_spec); constr:(@Stdlib.ZArith.BinInt.Z.land_spec); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.shiftl); constr:(@Stdlib.ZArith.BinInt.Z.shiftr); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.ZArith.BinInt.Z.shiftl_mul_pow2); constr:(@Stdlib.ZArith.BinInt.Z.shiftr_div_pow2); constr:(@Stdlib.ZArith.BinInt.Z.ldiff_ones_r)|] [|@b; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat1; @__sat0; @L; @s; @Hx; @x; @e; @__p1; @a; @H; @__x2; @NZ; @n; @X; @b0; @Hi; @i; @z; @__sat2; @E|] "#(>#3$4#6#^###$#E#_#%#]#9#&#'#e#m#*#,#3#(#+#g#M#c#-#1#>#W#0#2#C#L#K#)#R#Y#b#o#D#y$%$&$#$,$3#J#O#Q#S#U#T#V#X#Z#\#f#i#k#l#j#P#n#r#t#w#u#x#z#|#{#.#~$'#}$)$(#s#q$*$+$-#?$1$2$4$5$6#A#H#:#G#F#8#a#`#=#[#7#<#;#B#I#d#v#N#h$/$.#@#p$$$0?#w$#x&#y%#z%#{%#|%#F)#}'#~*$#$$$+$%%$&$$'%$(%$)$$*%$+$$,%$-*$.%$/%$0%#%&$1$#%'$2%$3%(KE,S*/#,$,#,#,#,#/#0)#%E#.-##S*######################################################################################################################,#,#,#/#9F#/s#CUS.#1F#&LF&(F'$#1M'&#I$GE#j#$G#&+F2#'+#&MI&2I'$#$G#Ej#$G#US.s#Y&#F'#+'*E&7I2#'-#$G&#j#$G#VS=Fs#b%Fs#c(s#dFVS/Fs#eWS0%$#VS/Is#g%Ls#h(s#iL&PS#&4S#&s#&S#2#'%#''#'(%$G$#%Ms#r&S$S1&s#.S12#'E#'&#''%$G$#j#$G#'*E$G#&j#$G#5G0'S&4US>5)G6&%$#VS?s$,s$&%Ks$-(Ks$(%Ks$(k##$#k##&#(Ks$2WS@s$3s$-Fj##S2#j#%%#(Ks$/k##S2#k#%(#VSAKs$95SB#m##0UF#USCS+USDS+VS3CFUSECUSFCVS4CS*3Cs$=*C$S'#+&JDDH#NUSGD3CK*C#S%(+*JDDH#N6+JDDH#'-,JDDH$'#--JDDH)(#VSH.H5GS&VSIEI$G#S&m$%#WSJCKFXSKEI$#l#&*)#l#'87#l#(;:#j#)C#%Es$R(KF(KI%Is$U.$#k##&#k##(#k#)C#:QMS$l#*,$#l#+s#(s#4#l#,s#0s#-#l#+s#:s#5#WSLs$_S##)GS&s#Ds#=s#S#j#-s#M#U#E(s$cM$GEs#Jj#$G#VSMPK$CPK;#VS5$#$CS$K;#VS5$#&QP$G#Oj#.%#$CQK&FS($G#Ok#/s$p#j#0C#(KK.#s#OUSNQj#/$#[S6CK'#S(EQj#1,#U#Ej#14#;/ZSOs#EJDDHL6s#FJDDHs#>#-s#GJDDH#s#Bs#?l#&#s#<s#6l#'s#Ks#J#l#(s#Ns#M#j#)C#j#2R#.s%2Fk###s#6k#)C#k#2R#%S)s%-:#S)S,l#*)%#l#+s#Ys#e#l#,s#as#^#l#+s#ks#f#%KF0s%;F%I#4L%#Ik##%#4I%#F0s%BI%L#k##%#.(#4M%#Lk##'#j##&#0s%JL%M#k##0#j###Fj##1#WSPIFEYSQ3.)$#j##9#j#$C#j#3C#k##<7k#$C#k#3C#*Cs#sS7s#n+s#uJDDH#NZSRs#vJDDH#*Cs#qS's#v+s#xJDDH#N-s#yJDDHs#5s#t#-s#zJDDH&s#u#l#&#s#os#il#'s#~s#}#l#(s$%s$$#j#)C#j#2R#$CEKk###SS.s#jI%KIk##$#k##&#k#)C#k#2R#<s#9S)MS,l#*,$#l#,s$:s$7#l#+s$Ds$?#3Cs%oUSTs%kWSUC$#*Cs$2S'#+s$4JDDH#N6s$5JDDHs#N#-s$6JDDH#s$1$l#&#s$+s$%l#'s$:s$9#l#(s$=s$<#j#)C#j#2R#.Fs%s%Fs%uk##$#k#)C#k#2R#(KS-:#S-S)l#**%#l#+s$Is$U#l#,s$Qs$N#l#+s$[s$V#<SVs&$:#l#4s#6s#3#4S(%#s&'US8S9US8#=C#=C%=CS9WS:C$#WS:C&#VSW#SXWSYS+#s$WVS3CIUSZCXS[C$F#VS4Cs&;*Cs$VS%#+s$YJDDH#N*Cs$YS'%+s$[JDDH#N-s$\JDDH%s$W#-s$]JDDHs$Ys$X#l#&#s$Rs$Ll#'+s$`#l#(/s$c#j#)C#j#5C#(s&@I%ILk##$#k##s$O#k#)C#k#5C#4S-<S,#MS$l#*+%#l#+s$qs$}#l#,s$ys$v#l#+s%'s$~#l#4s#)s#'#XS\S(S$s#x#j#6s$/#U#Ej#7s$C#ZS]s$Es$Ds$@s$3#El#.s$Js$G#$Gs%GO&s%jP2#'E#$GO#j#$G#'Os%B5G#)GO%#s%FEl#8,+#'s%QOUS^s%R)GOs$X%$#'Os%Q's%U#$G#s%Pm#&#*Cs%)S%s%*+s%,JDDH#N*Cs%'S%s%++s%.JDDH#N6s%/JDDH#%-s%0JDDH&s%+#l#&#s%%s${l#'s%4s%3#l#(s%7s%6#j#)C#(s&nE.s%Is%ik##$#k#)C#VEQMl#*($#l#+s%@s%L#l#,s%Hs%E#l#+s%Rs%M#WS_s&wS##)GOs%\7s%k#j#-s$t#U#EnS0%s%qs%p%#$##s%hF#%$##s$w$###l#9s%sG#l#$s%ys%u#1s&'s&8&#FWS;s&)s&:F)Gs&(s%~&$#1Ls&<&#FWS;Ls&>F)Gs&4s&/&$#9Ls&C&#FWS`Ls&EF)Gs&?s&;&$#j#:s'6#j#;C#WSas&Hs&E#$Cs&Is&F1Is&H/s'77L#8$#$CE#j#<C#VSbIs&O>#s&P0s'@s&Q7I#>Es&S$C#*j#<C#8&'VScI/(K07M1(K#k##%#k##s%O#3C5WS<Cs%i#WS<C$s%j*C$S7#+s%mJDDH#Nl#&#s%bs%\l#'s%qs%p#l#(s%ts%s#j#)C#8E>8?E$C$#k#)C#7PBUE#l#*)%#l#+s%~s&.#l#,s&*s&'#l#+s&4s&/#l#=;6#>As&q3Cs&r*Cs%yS%#+s&$JDDH#Nl#&#s%us%ol#'s$/s&'#l#(s&+s&*#(Ks&xl#*$#El#+s&/s&;#l#,s&7s&4#l#+s&As&<#WSds#-s&}#)Cs#*s#20/#WSeIs'#%)Cs#0s#-$s#3#WSfIs'%')Cs#4s#6$s#;#9Is'))Cs#=s#8$#El#>s#@s#?#j#/s'l#j#0C##"). Qed.
Lemma land_7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_15 : forall x, 0 <= x -> Z.land x 15 = x mod 16.
Proof. intros x Hx. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.
(* [comment removed for export] *)
Ltac bvz_in H :=
  repeat first
    [ rewrite u_add64 in H | rewrite u_sub64 in H | rewrite u_and64 in H | rewrite u_or64 in H | rewrite u_xor64 in H
    | rewrite u_srl64 in H | rewrite u_sll64 in H | rewrite u_sltu64 in H | rewrite u_mul64 in H | rewrite u_lit64a in H ].
Ltac bvz :=
  repeat first
    [ rewrite u_add64 | rewrite u_sub64 | rewrite u_and64 | rewrite u_or64 | rewrite u_xor64
    | rewrite u_srl64 | rewrite u_sll64 | rewrite u_sltu64 | rewrite u_mul64 | rewrite u_lit64a ].

(* [comment removed for export] *)
Lemma bt_Z : forall c (x y : word) (b : bool),
  match c with
  | BC_EQ => if b then bv_unsigned x = bv_unsigned y else bv_unsigned x <> bv_unsigned y
  | BC_NE => if b then bv_unsigned x <> bv_unsigned y else bv_unsigned x = bv_unsigned y
  | BC_LTU => if b then bv_unsigned x < bv_unsigned y else bv_unsigned y <= bv_unsigned x
  | BC_GEU => if b then bv_unsigned y <= bv_unsigned x else bv_unsigned x < bv_unsigned y
  | BC_LT => if b then bv_signed x < bv_signed y else bv_signed y <= bv_signed x
  | BC_GE => if b then bv_signed y <= bv_signed x else bv_signed x < bv_signed y
  end -> branch_taken c x y = b.
Proof.
  intros c x y b H. destruct c, b; cbn [branch_taken]; unfold bv_eqb, bv_ltu, bv_lts in *;
    rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff, ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge; try exact H; try lia.
Qed.

(* [comment removed for export] *)
Lemma bv_unsigned_nonneg64 : forall w : word, 0 <= bv_unsigned w.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w). lia. Qed.
Ltac nn :=
  lazymatch goal with
  | |- 0 <= _ mod _ => apply Z.mod_pos_bound; lia
  | |- 0 <= _ / _ => apply Z.div_pos; [nn | lia]
  | |- 0 <= Z.land _ _ => apply Z.land_nonneg; left; nn
  | |- 0 <= bv_unsigned _ => apply bv_unsigned_nonneg64
  | |- _ => lia
  end.
Lemma land_m8' : forall x, 0 <= x -> Z.land x 18446744073709551608 = 8 * ((x mod 18446744073709551616) / 8).
Proof.
  intros x Hx. rewrite <- land_m8 by (apply Z.mod_pos_bound; lia).
  change 18446744073709551616 with (2 ^ 64). rewrite <- Z.land_ones by lia.
  rewrite <- Z.land_assoc. f_equal.
Qed.
Lemma lxor_m1 : forall x, 0 <= x < 18446744073709551616 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof. intros x Hx. exact (AsScLib.lxor_ones64 x Hx). Qed.

(* [comment removed for export] *)
Ltac zlits :=
  change (2 ^ 64) with 18446744073709551616 in *;
  repeat match goal with
  | |- context [?a mod ?b] =>
      lazymatch a with
      | Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac
      end;
      lazymatch b with Zpos _ => idtac end;
      let v := eval vm_compute in (a mod b) in change (a mod b) with v
  | |- context [2 ^ ?k] =>
      lazymatch k with Zpos _ => idtac | Z0 => idtac end;
      let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v
  end.
Ltac zmasks :=
  repeat first
    [ rewrite land_m8' by nn
    | rewrite land_7 by nn
    | rewrite land_15 by nn
    | rewrite lxor_m1 by (split; [nn | apply Z.mod_pos_bound; lia]) ].
(* [comment removed for export] *)
Ltac bt_gen := apply bt_Z; cbv beta iota; bvz; zlits; zmasks; Z.div_mod_to_equations; lia.
