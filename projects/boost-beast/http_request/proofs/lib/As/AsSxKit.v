(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec SeqExec StoreOk AgentLib Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame LibTail.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsPrintfFirst.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shx (o : Z) : expr :=
  EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 0) (ELit o)) (ELit 3)) (ELit 2147450880)) (ELit (-8)).
Definition shw (spz o : Z) : Z := (8 * (((spz + o) / 8 + 2147450880) / 8))%Z.

Lemma shx_denot : forall E (sp : word) o,
  ev E 0 = sp -> (ASP_LO <= bv_unsigned sp)%Z -> (bv_unsigned sp <= ASP_HI)%Z -> (-65536 <= o <= 0)%Z ->
  bv_unsigned (edenot E (shx o)) = shw (bv_unsigned sp) o.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.env); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ev); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.ASP_LO); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.ASP_HI); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.Riscv.Sem.alu64); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_AND); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_SRL); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@stdpp.bitvector.definitions.bv_shiftr); constr:(@stdpp.bitvector.definitions.bv_and); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.ZArith.BinInt.Z.shiftr); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Stdlib.ZArith.BinInt.Z.mod_small); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.Zdiv.Zplus_mod_idemp_r); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.land_m8'); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.shiftr_div_pow2); constr:(@stdpp.bitvector.definitions.Z_to_bv_unsigned); constr:(@stdpp.bitvector.definitions.bv_add_unsigned); constr:(@stdpp.bitvector.definitions.bv_and_unsigned); constr:(@stdpp.bitvector.definitions.bv_shiftr_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.edenot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EAlu); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.EVar); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2.SX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsSxKit.shx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsSxKit.shw)|] [|@b; @z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @__sat2; @__sat1; @__x3; @__x4; @__sat4; @__sat5; @H0; @r; @q; @H3; @H2; @H1; @H; @Ho; @Hhi; @Hlo; @E0; @o; @sp; @E|] "#)~#5$C#=#t#u#s###G#|#'#(#z#$#&#%#)#K#e#@#<#j#L#J$##+#-#?#V#Z#_#c#b$'$(#,#\#*#.#/$9$>$?$A#:#9#B#D#U#]#`#k#l#o#p#r#}$$$%$)$*$&#[$+$.$/$0$1$2$3$5$4$7$6$8$:$;#4#3#0#1$-$<$,$@$C$E$F#8#O#;#R#>#C#A#W#S#x#w#H#Y#g#X#^#E#N#Q#q#I#h#y#i#M#P#v$=#a#f#d#{#~$D$B#F#T#n#mI#y$#z$#{%#|&#}%#~%$#%$$%$%'$&*$')$(%$)&$*%$+%$,%$-$$.%$/+$0&$1%$2%$3$$4%$5%$6*$7%$8%$9%$:&$;%$<&$=$$>&$?$$@&$A%$B'$S$$#$#$#$#$#US<#US=#VS+OS#&$#M'&O(S>#'(N(#S?$+$#$#$#$#$#$#$#$#$#E#(#N(NH2$#:8K6QG##S$3#:<#6S&&##&##########################$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#3#:s#<#6QB#Es#B:s#?#6S'%#'s#A#3s#F's#CP%#K4#%%#-4#';(#&C*#j#$s#I#:s#KJFs#LK#3s#.:s#N#WS,s#Os#5#WS@s#P&#Fs#Q#7's#R#'s#S6*$#&CG/j#%C#'s#W)'s#X>%$#)s#Z#*G*&C#6j#%C#'s#^4's#_20$#%G+)s#b#*#2&C#>j#%C#'s#fs#L's#g;*$#Fs#iPs#S's#j#0#G%#6)s#m#*#=&C#s#)j#%C#'s#qK's#rs#)%$#)s#t#0G/%#@)s#w#*#s#'&C#s#3j#%C#)s#{J%s#;G)s#}#0#8%#s#))s$$#*#s#0&C#s#<j#%C#)s$(s#k)s$)K%s#E#)s$+#*Gs##0$#%#s#4)s$/#*#s#;&C#s#Gj#%C#)s$3s#D*.G0,#%#s#<)s$7#*#s#C&C#s#Oj#%C#)s$;s#^*6+04#%#G)s$?#*#s#K&C#s#Wj#%C#)s$Cs#c%)+)s$E#*#G&C#s#]j#%C#%s#6J3s$P3s$LVS-$#.&#&Cs#hGj#%C#VSA('1H)(H)1H)k##$#k##&#(H.WSB/.Mj##S.#j#&%#(H0k##S.#k#&(#VS/H5>S0#m##0UM#9S#9#9#7C#7C%7CS#/C$#/C&#?#S%9)7C#7C-/C#)/C%#?#S%USCR@R$#@R+#USDRGCOUSECHC$M#USFCUSGC8Cs$gACs%$+C$L#,&FDDE#I8CH+C&L#,)FDDE#I<*FDDE&#USHDACS$#s$Z############################################################3#8C#+Cs#$L#,s#/FDDE#I$s$~##############$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#3#8C#+C#Ls#H,s#SFDDE#IBCs#Js#R+Cs#PL#,s#VFDDE#I8Cs$)WSIC#s%r+C'S(#,s#ZFDDE#I<s#[FDDE'#5s#\FDDE+s#S#5s#]FDDEs#0s#T#5s#^FDDEs#Vs#U#VSJs#_E>S1S2VSKGO&S1#S2m$%#WSLCHMXSMGO$#l#'*)#l#(s#is#h#l#)s#ns#m#j#*C#j#+C#(s%sM(MH2$#(Ms#D(AO%NJ(H#1$s$B2$#k##'#k##)#k##+#k#*C#k#+C#'s&7S3YGS)#JKPl#,3%#l#-s$8s$D#l#.s$@s$=#l#-s$Js$E#WS4s$Rs$O#XSNCs$Os$S#.Js$Q%s%-#.#s$SWSOJs%/s$T-Cs$Ts$R'$#&Cs$Y%0Gs&,%#s%i.#s$Y#s#a##########################$#$#$#3#*5#'s&[S5%#P4#s%y%#s&%4#s%{;s%|#&C)#j#%C#VS-s$ws&J4s%~#%Gs&,.#s$x*#0&C#*j#%C#*G3&C#-j#%C#&CG/j#%C#>Cs&)*s&,9VSPs&/s&1&Cs&2HUSQ#;s&49.;s&5%$#&C=#k##'#VSR?s&91Hs&:'s&{S)%#S5.#s&=(H#1$s&?2$#k##)#VSS(s&B1s&CH%s#OS).#s&E1s&F#($H2$#k##(#VST(s&J's'/S*%#S34#s&M&C#Hk##?#VSU&s&P's'5S6%#S*.#s&S&C#$k##s#%#4&s&V's';S7%#S6.#s&YVS/Hs&Z>S0#m##s#$UK#(HG1Gs&_2$#9s%99#9#7C#ES$VSVC#7C(WSWC$#VSXCs&iWSYC#s%F/Cs%H#/Cs%J#/C'#/C,#?#S%7C0/Cs%G)/Cs%I#/C.#/C&#?#S%@R#s%H@R*#GCJHC#Os%FGCNHC$M#ACs'e+Cs%BL#,s%HFDDE#I8Cs'#+C&S(#,s%KFDDE#I<s%LFDDE&#+C&S8s%H,s%NFDDE#IZSZs%OFDDE#ACs'RBCs%O#WS[C+s%HBC#/+C%S8#,s%UFDDE#I5s%VFDDE)s%M#+Cs%VL),s%XFDDE#I+C+Ls%T,s%ZFDDE#I<s%[FDDE%#+Cs%ZLs%1,s%]FDDE#I+Cs$kLs%\,s%_FDDE#I8Cs'ABCs%W#+Cs%]L#,s%cFDDE#I+C%S(s$j,s%eFDDE#I<s%fFDDE%#5s%gFDDE*s%^#5s%hFDDE-s%_#5s%iFDDE0s%`#5s%jFDDE6s%a#5s%kFDDEAs%b#l#'#s$ks$el#(s#*s%n#l#)s#/s%s#j#*C#j#+C#j#/C#j#0C#(HN1Ns'N2$#k##s#|S\;s'QO%#K&Cs$g#k##&#(s('J(JH2$#(Js%T(s%1K%Ks'a(H#1$s&R2$#k##'#k##)#k##+#k##/#k##5#k#*C#k#+C#k#/C#k#0C#'s(KS]]GJS^#KNS*S7S_S`l#,?%#l#1s&Ss&P#l#2s&]s&X#l#3s#ms#j#l#4s#rC#l#5s#vC#l#6s#}s#x#l#7s$(s$##l#8s$1s$*#l#3s$;s$3#l#9s$Ds$=#VSas'p#-Cs'os$Is$Hs$G#.s'rs&lWS4s'ss&m&-Cs'ts$N%$#0s'ws(D8Cs(E+Cs&@L#,s&FFDDE#Il#'#s%Fs%@l#(s&Ks&I#l#)s&Qs&N#(Hs(Kl#,$#GWSbs($s(M#-Cs$as$\-,#.Ks&z%s((#.#s&|ZScCs()s$g&#Gl#9s%+s%*#%s'Zs'P)s(n#0#s'5%#s'7)s(q#*#s'14s',s(3%#s(;4#s(5;s(6#&C'#m#.#=s(ys(=-Cs'9s'4$s()#=s({s(B-Cs'Cs'<$s(&#=s(}s(2-Cs'Ms'F$s'u#=s)#s(f-Cs'Zs'P$s'x#=s)%J-Cs'es']$s'n#WS9s)'Ks(:-Cs'ns'h$s((#WS:s))s(ks(9-Cs'|s't$s()#WSds)+s(=s(:-Cs(*s(%$s(3#WS9s)-s(;s(O-Cs(2s(/$s(:#WS,s)/s(<s(N's)0#WS:s)1s(>s(P-Cs(<s(:&$#6QKs(F6S&#s(v6Q#s(W6S'#s(U's)7#&C#@m#)#VS+PS#-s):Ks(O$#NUSeS#CJDQ$#Cs)&DS&$#Cs(dDQ$#Cs(cDS'$#VS;P#'s)F#&C#s#/m#/#USfJVS;P#'s)K#VSgs(9J&C$#m#(#m##$j#:s);#j#;s)J#j#<s)M#j#=s)P#j#>C#j#?s)T#j#@Sh##"). Qed.

Lemma shw_range : forall spz o, (ASP_LO <= spz <= ASP_HI)%Z -> (-4032 <= o <= -64)%Z ->
  (shw ASP_LO o <= shw spz o <= shw ASP_HI o)%Z
  /\ (2147450880 + (spz - 4096) / 8 <= shw spz o)%Z /\ (shw spz o + 8 <= 2147450880 + spz / 8)%Z.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.ASP_LO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPrintfFirst.ASP_HI); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.div_le_mono); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsSxKit.shw); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC)|] [|@__ff; @__varmap; @__wit; @__arith; @__x1; @__x2; @b; @a; @__x3; @__x4; @__x5; @__x6; @__x7; @__sat9; @__sat10; @__sat11; @__sat12; @H1; @H0; @Hs; @s2; @s1; @__p1; @r; @q; @H4; @H3; @H2; @__p2; @heq_q; @q0; @H5; @__p3; @heq_r; @r0; @H6; @heq_t; @H7; @__sat4; @__sat5; @__sat6; @__sat7; @heq_u; @u; @t; @MONO; @M8; @Ho; @H; @o; @spz|] "#/s#?$1#B#U#V#T#Y#[#$#i#?#&#)#(#%#*#'###+#0#Z#,#N#-#/#3#u#4#9#.#1#2#7#6#5#8$.#J#:#<#>#=#E#F#_#`#q#z$0#;#M#O#P#Q#S#\#b#c#]#j#K#o$#$*$)$,$-$/$2#D#l#H#I#k#W#R#C#g#a#d#|#s$$#v#{#x#e#m#^#p#t#r#n#X#h#y#f#L#w#}#~$%$&$'$(#G$+$1K#f%#g%#h$#i$#j%#k'#l*#m%#n+#o&#p%#q*#r&#s%#t&#u%#v%#w'#x%#y%#z%#{$#|%#}&#~%$#%$$%$%%$&$#2&$'&$()$)%$*%$+%$,%$-%$.$$/&$0&#S;I#IS<*$#&S6&#&#&#&#%#%#%#%#%#%#H###I%S6%#%#%#%#%#H##I#*+##IR?*USCS'USDS'USECUSFCUSGC;CG;C)(C$S%#)&FDDE#HVSH'E6S=S>VSIRO,S=#S>m$%#WSJCGIXSKRO$#l#$*)#l#%10#l#&43#-G6l#'$#R>CO4C#I6<CS6<Cs#%(C$J#)8FDDE#HUSLD+:FDDE$#$l#$#60l#%*=#l#&A@#j#(C#j#)C##RI#IOk##$#k#(C#k#)C#@OLIl#')$#YSMOIs#,7#j##s#.#j#*C#j#+C#'Os#0'Is#1#$#k##s#4#k#*C#k#+C#$OM$IMVL$##%$$LP'#s#;$OP'#s#=#%#k##(#&s#S&#&#&#&#&#&#&#&#&#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#?#$A#$@$VQ$##%$$QS#'#s#_$#)'#s#a$LS#'#s#c$#-'#s#e#'#k##,#5(s#h#G)#Gs#j$NS('#s#l#G#k##&#k##(#$NS&5#s#q#G$$PS.'#s#t#G#k##.#k##'#$.A5#s#y#G$$PS)'#s#|$#s#&'#s#~#G#k##8#k##)#$0s#+5#s$'#G$$S&S$'#s$*$#s#0'#s$,#G#k##B#k##)#7CS?8S?8#8#8#7C#/C(#9#S+VSN*#:S'#s$8>CP4C#Ls$8>CN4C$O#>CQ>CM4C$P#4C&I#<Cs$X;Cs#H1C$#<Cs$M1C#%(C%J#)s$CFDDE#H+s$DFDDE#s$-s$.&s$T<C#<Cs$U1C$#%s$e<C#1C#&(C&J#)s$MFDDE#H(C3J0)s$OFDDE#H+s$PFDDE%s$9#(C-J))s$RFDDE#HACs$Qs$@ACs$Rs$@(C$J#)s$VFDDE#H+s$WFDDE's$@#+s$XFDDE*s$A#+s$YFDDE7s$B#l#$#s$Us$Ol#%As$\#l#&s#*s$_#j#(C#j#)C#j#,C#j#-C#j#.C#j#/C#j#0C#$Ns#n$Ms#o#$#k###s$H$QL$NL#$##PS#k##$##NM3s$sL3s$tQ#$#k##&#k##(#k##.#k#(C#k#)C#k#,C#k#-C#k#.C#k#/C#k#0C#$S#S$'#s%%$#s$+'#s%'^R%s#\S#S&S$#s#ZNMPl#'?(#l#1s#as#Y#l#2s#ls#d#l#3s#us#o#l#4s$#s#x#l#5s$0s$%#l#6s$Us$N#=OM=IM#$#m#&#j#7s%5#j#8C#j#9C#k##s%8'k#8C#k#9C#%s$P&#&#&#&#&#&#&#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#?#=#Q=NQ#$#&s$s&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#?#=#Q#s#%#*s#%#%s&*%#%#%#%#%#?#2N#'#s&-$s%3###s#1$s#2s&0'Ns&1$s%7##%#*'#>CI;Cs#:(C#Js%{)s&3FDDE#HBs&4FDDEL.s&5FDDE$#+s&6FDDE#s%{%l#$#s&2s&,l#%*s&9#l#&s&=s&<#j#(C#j#:K##s#ER*#I#s#GIk##$#k#(C#k#:K##Ms#(@#MQl#'+%#@s#NN#;Cs#,(Cs&4J#)s&HFDDE#H.s&IFDDE7#+s&JFDDE#s&3$l#$#s&Fs&@l#%>s&M#l#&s&Qs&P#j#(C#j#:K##Rs#6*I##Is#8k##$#k#(C#k#:K##s#_M@#MQl#'+%#@Ns#?#XS@s#`s#>7#$NQ'#s&a$MNC#s&c,Cs&dGUSO#$PM'#s&g3s&h#0%s&i$$#,C'#k##)#D)s&m$S#P0#s&o#G#-$s&q*$#k##s&_#E(s&t-s&uG$S&S#0#s&w-s&x##$G*$#k##(#F(s&|$S(S&'#s&~,C#Gk##>#G&s'%$S.S(0#s'',C#$k##s###'&s'*$S)S.0#s',VSPGs'-6SQ#m##s&wUN##GR-Rs'2*$#7Cs%_HS6VSRC#7Cs%dIC$#/C#s%g/C(#9#S+7Cs%h/C(s%k/C$#9#S+:S'#s'?:S'(#4Cs%bOs'?>CL4C$I#(Cs'?Js%W)s'AFDDE#H(Cs%YS%s'@)s'CFDDE#H.s'DFDDE%#(Cs'CS5s'D)s'FFDDE#HZSSs'GFDDE#<Cs'd1Cs'5#1Cs%Us%a(C$S5#)s'LFDDE#H+s'MFDDE(s'6#(Cs%YJ')s'OFDDE#H1Cs%[s'N(C*S%#)s'RFDDE#H.s'SFDDE&#+s'TFDDE)s'=#+s'UFDDE3s'>#l#$#s'Qs'Kl#%:s'X#l#&>s'[#j#(C#j#)C#j#,C#j#-C##GL-Ls'c*$#k##s#_ST$LQ3s'gO$#N,C%#k##'##&'$'s'l-)#*%#k##'#k##.#k#(C#k#)C#k#,C#k#-C#ZROS/S0LIS#l#'7$#l#5s#Is#F#l#;s#NC#l#<s#QC#l#=s#Ws#S#l#>s#]s#Y#l#?s#fs#_#l#5s#ns#h#l#6s#ys#p#3s(#R##s#|$$s(%-s#~#*%#$Is'-'#s()$Os'/C#s(+$Ls'1'#s(-3s(.#0%s(/$$#,C'#k##s$+#D)s(3$Qs'90#s(5#G#-$s(7*$#k##s(%#E(s(:0s&0s(;-s(<##$G*$#k##s$(#Fs&5s(@'s&5s(A,C#Gk##s$=#Gs&8s(D$Ps'J0#s(F,C#$k##s$B#'&s(I$S#s'O0#s(K$S*S0'#s(M6C#,CS($m#$#$S,S*5#s(R#G$$S2S3'#s(U#G#k##s'K#k##'#8s''7C#ICs$'s$)/C#s'./C%#9#S+/Cs$-s'1/Cs'-#9#S+:S'#s(a:S''#4Cs'*Ls(a4Cs$%I#(Cs(`Js&y)s(bFDDE#H(Cs&{S%s(a)s(dFDDE#H.s(eFDDE%#1Cs(Rs'*1Cs&rs'#(C$S5#)s(iFDDE#H+s(jFDDEs$%s(S#;Cs(|(C#Js'')s(mFDDE#HBs(nFDDEP.s(oFDDE$#(Cs%AJs$*)s(qFDDE#HBs(rFDDES#.s(sFDDE$#(Cs'#J0)s(uFDDE#H(C2S%s$()s(wFDDE#H.s(xFDDE%#+s(yFDDE(s(b#+s(zFDDE-s(c#+s({FDDE3s(d#+s(|FDDE9s(e#l#$#s(xs(rl#%@s)##l#&s##s)&#j#(C#j#)C#j#,C#j#-C#j#.C#j#:K#j#@K##GQ-Qs)1*$#$s$*M,Cs#f#k##s$.##s)BN*#P#s&<N*#S&#s'$s'/$s'%s);-s'1#*%#k##'#k##*#k##-#k##1#k#(C#k#)C#k#,C#k#-C#k#.C#k#:K#k#@K##S2s&*#S3s)N_R$#QS3S2S$NLS(S*S,l#'?&#l#1s#Ys#S#l#As#\s#]#l#?s$}s$z#l#;s#cC#l#Bs#fC#l#Cs#ls#h#l#=s#qs#n#l#>s#xs#s#l#?s$$s#z#l#5s$-s$&##s$6s$/-s$0s$5*$#2S&s&1'#s)[2S(s&3C#s)]2S.s&5'#s)_3s)`#0%s)a$$#,C'#k##s%]#D)s)e2S)s&=0#s)g#G#-$s)i*$#k##s)W#E(s)l2S$s&D0#s)n-s)o##$G*$#k##s%[#F(s)s2S/s&K'#s)u,C#Gk##s%q#G&s)x2S0s&P0#s)z,C#$k##s%v#'&s)}2S*s&U0#s*#$S)s))'#s*%6C#,CS($m#$#6Cs$2,CS$s$3m#$#$S/s)15#s*-#G$$S*s)4'#s*0#G#k##s)&#k##'#$S4S15#s*5#G$$S7S-'#s*8#G#k##s).#k##'#/Cs(es(j/Cs$A#9#S+8s$D7C#ICs%is(j/C#s(p/C%#9#S+:S'#s*D:S'*#4Cs(gOs(i4C#Is%c(Cs*CJs(X)s*EFDDE#H(Cs(ZS%s*D)s*GFDDE#H.s*HFDDE%#;Cs'%WSACs*6#1Cs(Vs(_(C$S5#)s*MFDDE#H+s*NFDDEs%es*7#ACs*Ms(f1C#s*N(Cs%fS%#)s*RFDDE#H.s*SFDDEs$C#(Cs$GJs%j)s*UFDDE#H.s*VFDDE#s$B(Cs'(Js*C)s*XFDDE#HBs*YFDDES&.s*ZFDDE$#(Cs(fJ3)s*\FDDE#H(C5S%s%k)s*^FDDE#H.s*_FDDE%#+s*`FDDE(s*I#+s*aFDDE-s*J#+s*bFDDE1s*K#+s*cFDDE7s*L#+s*dFDDE>s*M#l#$#s*`s*Zl#%s#%s*g#l#&s#(s*j#j#(C#j#)C#j#,C#j#-C#j#.C#j#:K#j#@K#j#DK#2Ls'L,C#s$Ek##s%p#3s*xN$#s*y-s%r#*P#*s$HS&*s$GS.2Ms'U#)#-$)*$#k##'#k##)#k##+#k##0#k##s$V#k#(C#k#)C#k#,C#k#-C#k#.C#k#:K#k#@K#k#DK##S7s'p#S-s+83s+5S,##s#]aR&%#MS,S-S7PNS)S*S1S4l#'B(#l#1s#bs#\#l#2s#ks#e#l#As#ns#o#l#Es#rs#s#l#>s&ks&h#l#Fs#yC#l#Bs#|C#l#Gs$&s#~#l#Cs$,s$(#l#=s$4s$.#l#>s$<s$6#l#?s$Es$>##s&$s$G-s$Hs&#*$#'S.s+HCS)s+I'S$s+J3s+K#0S$s+L$$#,CS$#k##s'H#DS$s+P0S/s+Q#G#-$s+S*$#k##s+A#ES/s+V0S0s+W-s+X##$G*$#k##s'D#FS0s+\'S*s+],C#Gk##s'Y#GS*s+`0S,s+a,C#S,k##s']#'S,s+d0S3s+e2S1s(='#s+g6C#,CS($m#$#$S0s*p'#s+l6C#,CS$$m#$#$S-S4'#s+q6C#,CS*$m#$#2S7s(L5#s+v#G$2S8s(O'#s+y#G#k##s*o#k##'#$S3s+&5#s+~#G$$S1s+)'#s,%#G#k##s*w#k##'#$S8SB5#s,*#G$$S9S:'#s,-#G#k##s+##k##'#4Cs,.Ls*S4Cs'NI#(Cs,-Js*O)s,/FDDE#H(Cs*QS%s,.)s,1FDDE#H.s,2FDDE%#1Cs*>s*T(Cs+|S5#)s,5FDDE#H+s,6FDDEs'Ms+{#(Cs*BJs,#)s,8FDDE#H(Cs,%S%s'G)s,:FDDE#H.s,;FDDE%#+s,<FDDEs$@s,%#+s,=FDDEs$Es,&#+s,>FDDEs$Is,'#+s,?FDDE+s,(#+s,@FDDE0s,)#l#$#s,<s,6l#%7s,C#l#&s$`s,F#j#(C#j#)C#j#,C#j#-C#j#.C#j#:K#j#@K#j#DK#,CLs%|k##s'K##s$9M-Ms$9*$#k##s$7#k##s$9#k##s$;#k##)#k##s&*#k#(C#k#)C#k#,C#k#-C#k#.C#k#:K#k#@K#k#DK##S9s)D#S:s,h3s,eS4##s#<aR&%#S#S4S:S9S&PS/S1SBS8l#':(#l#1s#As#;#l#2s#Js#D#l#3s#Ss#M#l#As#Vs#W#l#Es#\s#]#l#Hs#bs#c#l#=s(As(>#l#Fs#iC#l#Bs#kC#l#Is#ps#m#l#Gs#us#r#l#Cs#|s#w#l#=s$'s#~#l#>s$/s$)##s'VS)-S)s'U*$#6Cs$2,CIs$3m#$#6Cs%f,CQs%gm#$#$S&s,)'#s-%6C#,CP$m#$#5S,s-)#GS,'S2s-+#G#k##s+}#k##&#2S3s)b5#s-0#G$#Gs$)k##s,'#k##%#$S$s,:5#s-6#G$#Gs$*k##s,-#k##%#$S1S25#s-<#G$#Gs$+k##s,3#k##%#8s%`8#7C#VSUCs-DJC#s%cJC$s+t/Cs(q#/Cs+q#/C&#/C)#9#S+8,7C#7C/JC-#/Cs(r,/Cs'U#/C%#/C(#9#S+:S'#s-T:S'-#4Cs+wOs+v4C#Is'RACs-Rs(j1C#s-S(Cs+mS%#)s-WFDDE#H.s-XFDDEs'D#WSACs+ps%n(Cs+eJ#)s-[FDDE#H.s-\FDDE#s%a1Cs+qs+}(Cs+hJ#)s-_FDDE#H1Cs+js-^(C&S%#)s-bFDDE#H.s-cFDDE&#ACs-bs+x1Cs+|s+}(C$J#)s-gFDDE#H1C&s-f(C&S%#)s-jFDDE#H.s-kFDDE&#(Cs'_Js,()s-mFDDE#H;Cs-w(Cs,+J#)s-pFDDE#H.s-qFDDE&#(Cs*CJs,-)s-sFDDE#HBs-tFDDES(.s-uFDDE$#1Cs,:s-c(C#Js,%)s-xFDDE#H1Cs,=s)3(C<J#)s-{FDDE#H.s-|FDDE&#+s-}FDDE*s-f#+s-~FDDE/s-g#+s.#FDDE6s-h#+s.$FDDE?s-i#+s.%FDDEs#'s-j#+s.&FDDEs#,s-k#l#$#s-~s-xl#%s#3s.)#l#&s#6s.,#j#(C#j#)C#j#,C#j#-C#j#.C#j#/C#j#:K#j#@K#j#DK#-Ls)**M#3s.:I2Qs*n#$#*#S##s,)s(W$s,*s.?-s(Y#*%#3s.BS#$MP#$#$%s.E-%#*%##s.TS##S#s.M*$##s+OS#*#S$$s-RM3s.NP#$#$$s.P$s-VS##$#*&#k##*#k##-#k##1#k##8#k##=#k##B#k#(C#k#)C#k#,C#k#-C#k#.C#k#/C#k#:K#k#@K#k#DK##S-s+D2S-s+;3s.eS)$#s.f-%#3s.hS(##S-cR)%#S*S4S-S(S/S)S&S.S$S0S2S1l#'s#6+#l#Js$2s$.#l#Ks$9s$5#l#Ls$@s$<#l#Ms$Hs$C#l#As(~s)##l#Es$Ks$L#l#Hs$Qs$R#l#Ns$Us$V#l#>s$\s$Y#l#Os&/C#l#?s&4s&1#l#Ps'zC#l#5s($s'}#l#;s)RC#l#6s)Zs)U#l#<s*xC#m##s+JXS@s+[s+Ks*|#l#Qs,Js,G#l#Rs.Rs.L#=S;O=LO#$#=S<O#%#*%#'s&os/*$s.0###)$*s/-'Ls/.$s.4##%#*'#*+#m#2#j#Ss/6#j#Ts/M#j#UC#j#VC##"). Qed.

(* [comment removed for export] *)
Fixpoint shkn (offs : list Z) : list kentry :=
  match offs with
  | [] => []
  | o :: r => KRange (shx o) (shw ASP_LO o) (shw ASP_HI o) :: KZero (SA (shx o) 0) (ELit 8) :: shkn r
  end.

Lemma shkn_ok : forall E mem (sp : word) offs,
  ev E 0 = sp -> (ASP_LO <= bv_unsigned sp)%Z -> (bv_unsigned sp <= ASP_HI)%Z ->
  Forall (fun o => -4032 <= o <= -64)%Z offs ->
  (forall a, (2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8)%Z ->
             mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
  know_ok RSEGS E mem (shkn offs).
Proof.
  intros E mem sp offs E0 Hlo Hhi Hoffs Qsh0. induction offs as [|o r IH]; [constructor|].
  inversion Hoffs as [|o' r' Ho Hr]; subst o' r'.
  pose proof (shx_denot E sp o E0 Hlo Hhi ltac:(lia)) as SHX.
  pose proof (shw_range (bv_unsigned sp) o (conj Hlo Hhi) Ho) as (SR1 & SR2 & SR3).
  cbn [shkn]. constructor; [|constructor; [|apply IH; exact Hr]].
  - apply krange_intro. rewrite SHX. exact SR1.
  - eapply (kzero_intro RSEGS E mem (shx o) (edenot E (shx o)) 0 (ELit 8) 8);
      [reflexivity | reflexivity | rewrite SHX; unfold ASP_LO in *; clear - SR2 Hlo; Z.div_mod_to_equations; lia | lia
      | rewrite SHX; unfold ASP_HI in *; clear - SR3 Hhi; Z.div_mod_to_equations; lia |].
    intros i Hi. rewrite SHX. apply Qsh0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint outside_zb (a : Z) (w : Z) (rs : list (Z * Z)) : bool :=
  match rs with
  | [] => true
  | (lo, len) :: r => ((a + w <=? lo) || (lo + len <=? a))%Z && outside_zb a w r
  end.

Lemma outside_zb_sound : forall rs a w x,
  outside_zb a w rs = true -> (a <= x < a + w)%Z -> (0 <= a)%Z -> (a + w <= 2 ^ 64)%Z ->
  Forall (fun r => 0 <= fst r < 2 ^ 64)%Z rs ->
  outside (Z_to_bv 64 x) (map (fun r => (Z_to_bv 64 (fst r), snd r)) rs).
Proof.
  intros rs a w x. induction rs as [|[lo len] r IH]; intros Hb Hx Ha Hw Hrs; [exact I|].
  cbn [outside_zb] in Hb. apply andb_true_iff in Hb as [H1 H2].
  inversion Hrs as [|rr r' Hr Hr']; subst. cbn [fst snd] in Hr.
  cbn [map fst snd outside]. split; [| apply IH; assumption].
  unfold in_rng. rewrite !u_small by lia.
  apply orb_true_iff in H1. destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.

Lemma cells_ok_frame : forall mem mem' (rs : list (Z * Z)) cs,
  cells_ok mem cs -> frame_mod mem mem' (map (fun r => (Z_to_bv 64 (fst r), snd r)) rs) ->
  Forall (fun r => 0 <= fst r < 2 ^ 64)%Z rs ->
  forallb (fun c => match c with (a, w, _) => outside_zb a (Z.of_nat w) rs && cell_wf_b c end) cs = true ->
  cells_ok mem' cs.
Proof.
  intros mem mem' rs cs Hc FM Hrs Hb. unfold cells_ok in *.
  induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hb. apply andb_true_iff in Hb as [H1 H2]. apply andb_true_iff in H1 as [H1 Hwf].
  unfold cell_wf_b in Hwf. repeat (apply andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  inversion Hc as [|c cs' Hcell Hcs]; subst. constructor; [| apply IH; assumption].
  unfold cell_ok in *. rewrite <- Hcell. apply (frame_mod_rdn RSEGS mem mem' _ w (Z_to_bv 64 a) FM).
  - intros i Hi. rewrite u_small by lia. apply (outside_zb_sound rs a (Z.of_nat w)); try assumption; lia.
  - rewrite u_small by lia. lia.
Qed.

Lemma none_range_frame : forall mem mem' (rs : list (Z * Z)) lo hi,
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  frame_mod mem mem' (map (fun r => (Z_to_bv 64 (fst r), snd r)) rs) ->
  Forall (fun r => 0 <= fst r < 2 ^ 64)%Z rs ->
  outside_zb lo (hi - lo) rs = true -> (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  forall i, (lo <= i < hi)%Z -> mem' (Z_to_bv 64 i) = None.
Proof.
  intros mem mem' rs lo hi Hn FM Hrs Hb Hlo Hhi i Hi.
  rewrite (frame_mod_byte mem mem' _ (Z_to_bv 64 i) FM); [apply Hn; exact Hi|].
  apply (outside_zb_sound rs lo (hi - lo)); try assumption; lia.
Qed.

Lemma byte_frame : forall mem mem' (rs : list (Z * Z)) a v,
  mem (Z_to_bv 64 a) = v ->
  frame_mod mem mem' (map (fun r => (Z_to_bv 64 (fst r), snd r)) rs) ->
  Forall (fun r => 0 <= fst r < 2 ^ 64)%Z rs ->
  outside_zb a 1 rs = true -> (0 <= a)%Z -> (a + 1 <= 2 ^ 64)%Z ->
  mem' (Z_to_bv 64 a) = v.
Proof.
  intros mem mem' rs a v Ha FM Hrs Hb H0 H1.
  rewrite (frame_mod_byte mem mem' _ (Z_to_bv 64 a) FM); [exact Ha|].
  apply (outside_zb_sound rs a 1); try assumption; lia.
Qed.

Lemma rdn_frame : forall mem mem' (rs : list (Z * Z)) a n v,
  rdn RSEGS mem (Z_to_bv 64 a) n = v ->
  frame_mod mem mem' (map (fun r => (Z_to_bv 64 (fst r), snd r)) rs) ->
  Forall (fun r => 0 <= fst r < 2 ^ 64)%Z rs ->
  outside_zb a (Z.of_nat n) rs = true -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn RSEGS mem' (Z_to_bv 64 a) n = v.
Proof.
  intros mem mem' rs a n v Ha FM Hrs Hb H0 H1. rewrite <- Ha.
  destruct n as [|n']; [reflexivity|].
  apply (frame_mod_rdn RSEGS mem mem' _ (S n') (Z_to_bv 64 a) FM).
  - intros i Hi. rewrite u_small by lia. apply (outside_zb_sound rs a (Z.of_nat (S n'))); try assumption; lia.
  - rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint kbytes (kn : list kentry) (b : expr) (k : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match kread RSEGS kn b k 1, kbytes kn b (k + 1) n' with
            | Some (ELit v), Some r => Some (v :: r)
            | _, _ => None
            end
  end.
Definition zbytes (vs : list Z) : list byte := map (fun v => Z_to_bv 8 v) vs.

Lemma word_to_le_bytes_1 : forall v, word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. discriminate.
Qed.

Lemma kbytes_rdn : forall E M kn b n k vs,
  know_ok RSEGS E M kn -> kbytes kn b k n = Some vs ->
  flat E (SA b k) (Z.of_nat n) -> (estart E (SA b k) + Z.of_nat n < 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (estart E (SA b k))) n = Some (zbytes vs).
Proof.
  intros E M kn b n. induction n as [|n IH]; intros k vs HK Hb Hf Hlt.
  - cbn in Hb. injection Hb as <-. reflexivity.
  - cbn [kbytes] in Hb. destruct (kread RSEGS kn b k 1) as [[v| | | | | | |]|] eqn:Hr; try discriminate.
    destruct (kbytes kn b (k + 1) n) as [r|] eqn:Hr2; [|discriminate]. injection Hb as <-.
    change (S n) with (1 + n)%nat. cbn [zbytes map].
    change (Z_to_bv 8 v :: map (fun v0 => Z_to_bv 8 v0) r) with ([Z_to_bv 8 v] ++ zbytes r).
    assert (Hf1 : flat E (SA b k) (Z.of_nat 1)) by (unfold flat in *; cbn [Z.of_nat] in *; lia).
    pose proof (kread_rdn RSEGS E M kn b k 1 (ELit v) HK Hr ltac:(lia) ltac:(lia) Hf1) as R1.
    assert (R1' : rdn RSEGS M (Z_to_bv 64 (estart E (SA b k))) 1 = Some [Z_to_bv 8 v]).
    { rewrite <- (flat_u E _ _ Hf1), Z_to_bv_bv_unsigned. cbn [edenot] in R1. rewrite word_to_le_bytes_1 in R1. exact R1. }
    apply rdn_app_Z; [exact R1' | | unfold flat in Hf1; lia | lia].
    assert (Hf2 : flat E (SA b (k + 1)) (Z.of_nat n)) by (unfold flat, estart in *; cbn [a_base a_off Z.of_nat] in *; lia).
    replace (estart E (SA b k) + Z.of_nat 1)%Z with (estart E (SA b (k + 1))) by (unfold estart; cbn [a_base a_off]; lia).
    apply IH; [assumption | assumption | assumption | unfold estart in *; cbn [a_base a_off] in *; lia].
Qed.

(* [comment removed for export] *)
Lemma kbytes_rdn_sp : forall E M kn i (sp : word) k n vs,
  know_ok RSEGS E M kn -> ev E i = sp -> kbytes kn (EVar i) k n = Some vs ->
  (0 <= bv_unsigned sp + k)%Z -> (bv_unsigned sp + k + Z.of_nat n < 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp + k)) n = Some (zbytes vs).
Proof.
  intros E M kn i sp k n vs HK Ei Hb H0 H1.
  assert (ES : estart E (SA (EVar i) k) = (bv_unsigned sp + k)%Z) by (unfold estart; cbn [a_base a_off edenot]; rewrite Ei; reflexivity).
  rewrite <- ES. apply (kbytes_rdn E M kn (EVar i) n k vs HK Hb); [unfold flat; rewrite ES; lia | rewrite ES; lia].
Qed.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
