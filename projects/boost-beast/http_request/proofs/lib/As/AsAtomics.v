(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr ZBridge CellsX TacX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma amo_aligned_lit : forall wd P,
  P mod (amo_bytes wd) = 0 -> 0 <= P < 2^64 -> amo_aligned wd (Z_to_bv 64 P) = true.
Proof. intros wd P H B. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite H. reflexivity. Qed.

Lemma unsigned_lit32 : forall z, (0 <= z < 2^32)%Z -> bv_unsigned (Z_to_bv 32 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Lemma low32_lit : forall x, (0 <= x < 2^32)%Z -> bv_unsigned (low32 (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. unfold low32. rewrite bv_extract_unsigned, unsigned_lit by lia.
  cbn [N.add]. rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z. apply Z.mod_small. lia.
Qed.

Lemma Z_to_le_bytes_4_mod32 : forall z, Z_to_le_bytes 4 (z mod 2^32) = Z_to_le_bytes 4 z.
Proof. intros z. apply (Z_to_le_bytes_mod 4 z 32). cbn. lia. Qed.

Lemma mod_mod_mul : forall a n m, 0 < n -> 0 < m -> (a mod (n * m)) mod n = a mod n.
Proof.
  intros a n m Hn Hm. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm n), Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma le4_congr : forall a b : Z, a mod 2^32 = b mod 2^32 -> le4 (Z_to_bv 64 a) = le4 (Z_to_bv 64 b).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Init.Datatypes.list); constr:(@stdpp.bitvector.definitions.bv); constr:(@LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsAtomics.mod_mod_mul); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsAtomics.Z_to_le_bytes_4_mod32); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le4)|] [|@z; @l; @Ha; @__ff; @__varmap; @__wit; @__arith; @__sat3; @__sat0; @__sat1; @__sat2; @H; @b; @a|] "#$U#+#^#.#E#$###%#&#(#2#8#>#=#D#G#I#M#V#S#T#\#]#B#`#?#a#b#4#1#9#<#@#C#H#*#K#J#L#N#O#Q#X#U#W#P#R#Y#Z#^#_#[#:#0#/#F#3#5#;#7#6#A-#T%#U%#V&#W%#X$#Y)#Z$#[$#\%#]%'S,UJ#'$'#'#'#UJ#VS-(#$E#$F$%C$#'(*#+#G*-US.#UK#)S/)#)#)###FVL,GVM-##&#%+&#j#$C#+1E+2H#+#%0#+j#$C#VS0;;$G#$#=#1##2%%7F#j#%8#$E)$#s###7#$H,$#s#&#:#%?#Fj#%@#$Gs#*%B=/j#$C#$Hs#-#A#%s#&#Aj#$C##s#$)%s#)s#$#j#$C##s#'s#3,s#,#(Cs#5%#.FVS1s#=s#8VNDs#>&Ds#:VNDs#:k##$#k##&#&Ds#CWS2s#Ds#?Ej##O#j#&%#&Ds#Ak##O#k#&(#VPHs#D&DH$Is#F&D#k##)#k##&#VPIs#J&DI$S3s#L&D#k##/#k##&#VS4Ds#V,S5#m##<UH#US6QUKQUS7CUS8CUS9CVRCDVRCs#`*s#]WS:C$#XS;C&S<#[S=(S>S#S#S$#S?VS@)S$,S%S&VSAFG%S%#S&m$%#WSBCDEXSCFG$#l#'*)#l#(32#l#)65#l#*#s#1Fl#+9s#1#l#,s##>#l#-s#*s#%#l#.s#/s#,#l#+s#9s#4#YS'Es#os#o##(Cs#os#Bs#<s#O#YS'Gs#qs#q%%(Cs#Js#H$s#W##s#fs#SUS(s#TZS)s#ls#Ss#N%$#US(s#\ZS)s#ns#[s#X$s#Z##s#ks#r#s#ls#e%s#q$#m#&#VLs#wEVMs#x#VS*s#yE(Cs#ks#g&$#VS*s#{G(Cs#{s#n$s#q#US+s#sUS+)%s#{$#m#&#j#/s$'#j#0C#j#1C##"). Qed.

Lemma amo_val_add_d : forall a b : Z,
  amo_val AMO_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold amo_val. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma amoadd_w_bytes : forall (X : word) (s : bv 32),
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 X))) s))
  = le4 (Z_to_bv 64 (bv_unsigned X + bv_unsigned s)).
Proof.
  intros X s. unfold amo_val. rewrite bv_add_unsigned. rewrite bv_extract_unsigned.
  cbn [N.add]. rewrite Z.shiftr_0_r. rewrite le_bytes_to_word_le4.
  transitivity (Z_to_le_bytes 4 (bv_unsigned X + bv_unsigned s)).
  - rewrite <- (Z_to_le_bytes_4_mod32 (bv_unsigned X + bv_unsigned s)). f_equal.
    change (bv_modulus 32) with (2^32)%Z.
    unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z.
    rewrite (Z.mod_small (_ mod 2^32) (2^32)) by (apply Z.mod_pos_bound; lia).
    rewrite Zplus_mod_idemp_l. reflexivity.
  - unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^32 * 2^32)%Z.
    rewrite <- (Z_to_le_bytes_4_mod32 (_ mod _)). rewrite mod_mod_mul by lia. rewrite Z_to_le_bytes_4_mod32. reflexivity.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma lor_lockbit : forall v, 0 <= v < 2^31 ->
  Z.lor v 18446744071562067968 = v + 18446744071562067968.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.bits_inj'); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.testbit); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.ltb_spec); constr:(@Corelib.Init.Datatypes.BoolSpec); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Stdlib.ZArith.BinInt.Z.testbit_neg_r); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.mul_pow2_bits); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.Bool.Bool.andb_false_r); constr:(@Stdlib.ZArith.BinInt.Z.eq_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@Corelib.Init.Logic.not); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.bits_0); constr:(@Stdlib.ZArith.BinInt.Z.bits_above_log2); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.ZArith.BinInt.Z.lt_le_trans); constr:(@Stdlib.ZArith.BinInt.Z.log2); constr:(@kc__2); constr:(@Stdlib.ZArith.BinInt.Z.log2_lt_pow2); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.ZArith.BinInt.Z.land_spec); constr:(@Stdlib.ZArith.BinInt.Z.lxor); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.add_nocarry_lxor); constr:(@Stdlib.ZArith.BinInt.Z.lor); constr:(@Stdlib.ZArith.BinInt.Z.lxor_lor)|] [|@b; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat1; @__sat0; @H0; @H; @s; @Hv; @v; @e; @__p1; @a; @NZ; @n; @b0; @Hn; @z; @D|] "#'.#3$*#6#\###9#$#C#]#%#[#G#&#c#,#'#*#(#-#3#+#a#1#2#>#n#A#J#I#K#O#U#h#)#o#r#u#B#w$'$(#H#N#P#S#R#T#V#W#X#Z#`#d#e#f#i#j#g#M#L#k#m#l#p#q#x#0#|#{#~#}$#$%$$#.#/#y#v#t$&#@$)$*$+#=#?#E#:#F#8#D#_#^#7#Y#<#;#Q#z#b#s5#u$#v$#w%#x%#y&#z%#{%#|'#}*#~%$#+#F)$$$$%%$&%$'$$(%$)$(FE#S)/#$S)$#$#$#/#0(#&E#,,#$'$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$###############################################################/#VS+G#%MG%%G)$#%FJ'HE#j#$H#%PJ%+J)$#'H#Ej#$H#VS:Gs#N&Gs#O(s#PGVS,Gs#QWS-%$#VS,Js#S&Ms#T(s#UM%QR%8R)$#'H#L&Ps#Z/s#<VS.Rs#\%$#'HLEj#$H#VS;s#es#`&Fs#f(Fs#b&Fs#bk##$#k##&#(Fs#kWS<s#ls#gGj##S/#j#%%#(Fs#ik##S/#k#%(#VS=Fs#r1S>#m##0UG#US?S0US@S0VSACGUSBCUSCCVSDCS)3Cs#w*C$S&#+&KDDI#NUSEDWSFC'&3CF*C$S&#++KDDI#N-,KDDI('#VSG-I1HS1VSHEJ'H#S1m$%#WSICFGXSJEJ$#l#&*)#l#'76#l#(:9#j#)C#&Es$/VS.Gs$0&#Fk##%#k#)C#VEOPl#*)$#l#+s#$s#0#l#,s#,s#)#l#+s#6s#1#WSKs#<s#;#XSLHs#;L#VSMs#>s$:%#RUSNC*C@S*s#%+s#(KDDI#Nl#&#>8l#'&s#+#l#(s#/s#.#l#*#s#?El#+s#2s#>#l#,s#:s#7#l#+s#Ds#?#XSOs#Js$GR#.Hs#Is#G0.#'HLs#P%OQ)#E'H#Lj#$H#%S%S2USP#%s#mS2ZS3HL&$#El#-,+#j#.s#W#U#E(s$UPVSQQF'CQF4#VS4$#'CS%F4#VS4$#%s#zQ)6#'H#Lj#/&#'COF%GS#%s$$S#)$#'H#Lk#0s$c#j#1C#(FF,#s#d)E)'H#Lj#$H#1HL%FOUS5O.HL&%$#j#0*#[S6CF-#S#EOj#24#U#Ej#2=#47%s$8O)E#'H#Lj#$H#%S#S%*Cs#^S*s#d+s#fKDDI#NZSRs#gKDDIM[S7s#hKDDI$#-s#iKDDI#s#d%l#&#s#_s#Yl#'s#ms#l#l#(s#ps#o#j#)C#j#3S$#,s%1G(FGk##$#k#)C#k#3S$#&S's%.WE#S'SSl#**%#l#+s#|s$,#l#,s$(s$%#l#+s$2s$-#2S#&FG0s%<G&J#2M&#Jk##%#2J&#G0s%CJ&M#k##%#,(#2P&#Mk##'#j##&#0s%KM&P#k##0#j###Gj##1#WSTJGEYSU3.)$#j##9#j#$C#j#4C#k##<7k#$C#k#4C#*Cs$;SVs$5+s$=KDDI#NZSWs$>KDDI#*Cs$8S&s$>+s$@KDDI#N-s$AKDDIs#7s$<#-s$BKDDI&s$=#l#&#s$8s$2l#'s$Fs$E#l#(s$Is$H#j#)C#j#3S$#'CEFk###SX,s#8J&FJk##$#k##&#k#)C#k#3S$#&S(s%fXE#S(RS'l#*-%#l#+s$Xs$d#l#,s$`s$]#l#+s$js$e#3Cs%rUSYs%oWSZC$#*Cs$XS&#+s$ZKDDI#N[S7s$[KDDIs#R#-s$\KDDI#s$W$l#&#s$Rs$Ll#'s$`s$_#l#(s$cs$b#j#)C#j#3S$#,Gs%w&Gs%yk##$#k#)C#k#3S$#(FS(WE#S(S'l#**%#l#+s$os${#l#,s$ws$t#l#+s%%s$|#XES[s&(:#l#-s#8s#5#*Cs$mS*s$n+s$pKDDI#N-s$qKDDI#s$l#l#&#s$gs$al#'s$us$t#l#(s$xs$w#j#)C#(s&1Ek###s%@k#)C#VES\Ql#*'$#l#+s%$s%0#l#,s%,s%)#l#+s%6s%1#YS]s#bs&9S%2#XS^S#S%s#d#.HLs#{s$,s#z#j#5s$$#U#Ej#6s$A#ZS_s$Cs$Bs$=s$(#El#/s$Hs$E#j#.s$J#U#EnS-%s%Ms%L%#$##s%HG#%$##s$M$###l#7s%OH#l#$s%Us%Q#%FGUS5G.HLs%Y%$#VS+Ms%f%#GWS`Ms%hG.Hs%es%b&$#j#8s&T#j#6C#WSas%kF#'Cs%lFVS8Js%nVS9Ms%o'CE#j#9C#VS8Ms%r'C#Ej#9C#1C)VS9Js%vWSbJs%wE.C,&%$#VScJs%yWSdJs%zEZS3C/,%$#l#:21#j#0s&]#j#1C##"). Qed.

Lemma lockword_mod : forall v, 0 <= v < 2^31 ->
  (Z.lor v 18446744071562067968) mod 2^32 = (v + 2^31) mod 2^32.
Proof.
  intros v Hv. rewrite lor_lockbit by lia.
  change 18446744071562067968 with (2^31 + 4294967295 * 2^32).
  replace (v + (2^31 + 4294967295 * 2^32)) with ((v + 2^31) + 4294967295 * 2^32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma C4_cell_congr : forall segs m A (a b : Z),
  a mod 2^32 = b mod 2^32 -> rw_cells segs m A [C4 (Z_to_bv 64 a)] -> rw_cells segs m A [C4 (Z_to_bv 64 b)].
Proof.
  intros segs m A a b H C. destruct C as [[Hwf Hb] Hw].
  split; [split|]; [exact Hwf| |exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. rewrite (le4_congr a b H). exact (fun x => x).
Qed.

(* [comment removed for export] *)
Lemma lock_cell : forall segs m A v, 0 <= v < 2^31 ->
  rw_cells segs m A [C4 (Z_to_bv 64 (Z.lor v 18446744071562067968))] -> rw_cells segs m A [C4 (Z_to_bv 64 (v + 2^31))].
Proof. intros segs m A v Hv C. eapply C4_cell_congr; [|exact C]. apply lockword_mod. exact Hv. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_cbv; simp_is_x0; simp_regs;
          first [ rewrite amo_aligned_lit by (cbn [amo_bytes]; first [assumption | lia | (Z.div_mod_to_equations; lia)])
                | match goal with |- context [amo_aligned ?wd ?a] =>
                    fail 100 "astep: cannot prove the alignment of" a "(need: P mod 4|8 = 0 and 0 <= P < 2^64 in context, address as Z_to_bv 64 P)" end
                | fail 100 "astep: no lr/sc/amo at" pc ];
          cbv beta iota zeta delta [negb];
          try (rewrite Z.eqb_refl; cbv beta iota zeta);
          simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; try (rewrite amoadd_w_bytes; try rewrite unsigned_lit32 by lia); try rewrite amo_val_add_d; mem_after_store_opt ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.

(* [comment removed for export] *)
Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

