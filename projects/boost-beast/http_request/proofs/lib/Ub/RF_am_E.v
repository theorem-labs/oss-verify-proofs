(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import F_memcpy.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_E.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
  bytes_at usegs m S src -> length src = Z.to_nat n ->
  rw_cells usegs m D [CB (Z.to_nat n) junk] ->
  0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
  (S + n <= D \/ D + n <= S) ->
  mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' D [CB (Z.to_nat n) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x79550) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
      [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
  destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
  do 15 eexists. split; [reflexivity|]. auto.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma ru64s_read : forall m A ws (i : Z) w a,
  bytes_at usegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes usegs m a 8 = Some (le8 w).
Proof. ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.USegs.usegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64s); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.Lists.List.nth_error); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u64s_split); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Nat.mul); constr:(@kc__1); constr:(@kc__2); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.mul); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_mul); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Lists.ListDef.firstn); constr:(@Corelib.Lists.ListDef.skipn); constr:(@Corelib.Init.Nat.sub); constr:(@Stdlib.Lists.List.app_nil_r); constr:(@Stdlib.Lists.List.firstn_0); constr:(@Stdlib.Arith.PeanoNat.Nat.sub); constr:(@Stdlib.Arith.PeanoNat.Nat.sub_diag); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.length_le8); constr:(@Stdlib.Lists.List.firstn_all2); constr:(@Corelib.Init.Peano.le); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.Lists.List.firstn_app); constr:(@Stdlib.Lists.List.app_nil_l); constr:(@Stdlib.Lists.List.skipn_0); constr:(@Stdlib.Lists.List.skipn_all2); constr:(@Stdlib.Lists.List.skipn_app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at_ov_read); constr:(@Corelib.Init.Nat.add); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.Lists.List.length_app); constr:(@kc__1 ((@Corelib.Init.Datatypes.list) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))))))|] [|@a; @post; @pre; @x; @y; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__sat2; @__sat3; @z1; @H1; @cstr0; @cstr; @Hlen0; @Hlu0; @z; @o; @l; @n; @__sat4; @z2; @H2; @cstr1; @H; @Hlu; @Eu; @Hlen; @E; @e; @Hi; @Hn; @Hb; @w; @i; @ws; @A; @m; @HCANB; @HSECB; @HCEILB|] "#-Q#H$j#_#t###V$B#z#$$C$A#%#>#&#b#'#B$K#+#?#(#-#.#@#*#)#n#,#/#1#5#C$1#0#2#3#6#j$L#D#R#U#7#:#8#;#f$%$&$6$J$`#N#i#9#=#d$'$a$i$j#L#]#\#4$/$:$I$E$M$O$R$S#H#G$\$]#A$l#w#K#S#T#W#Y#Z#[#a#e#p#}$*$)$.$0$9$8$7$<$=$;$>$@$F$D$N$P$T$U$Q$Z$[$^$_$b$c$d$e$f#E$g#<$V#r#P#M#u#Q#c#g#k#o#v$W#s$#$h#h$H$G$X#X#m#l#{#|#q$$$5$Y#O$+#~$($-$3$4$2$?#y#^#`$,$k#xT#Y&$@&$A$$B%$C%$D$$E$#U%#O$$F%$G)$H$$I%#F%#V%#($$J&$K&$L%$M%$N$$O'$P*$Q&#T%$R%$S$$T'$U%$V/$W%$X5$Y&$Z%$[$$\$$]/$^'$_%$`%$a%$b%$c+$d'$e$$f$$g%$h&$i(USaSN(S9(#(#(#(#(#(#(#(#(#(#(#(#(#%#(#(#(#(#(#(#(#(#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#E#USbSN*$#(s#&(#(#(#(#(#(#(#(#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#E#*s#%#&s#%#m#s#W#UScS:USdS:*F#%S9E#%$%#%#%#%#E#VSe)#<-#&-#m#0#USfS:USgS:*F#<$)&$#m#'#USO.USP#USO3USP#O#k##&#P')NXShOS%P#O*+NWSi,P#,-L#&$#*FPE@0#S%1S)#7##4N#0'S*1S##7#P6O#=S+=#=#=#=#=#=#=#>OS&E#.S*,.##.%#j#$s#&#+S*XSjS)#S%L4s#)S)E$s#*I##s#&S,#'s#,I+S##D$#)S,)I.S))E$s#1$#$s#2&##?(#'s#4(/8,#D$#&&#&.#&2#j#%s#7#As#8#j#&s#9#As#:#4s#@S#E$s#AI##s#=S&#+S,#D:#)S&.S#$s#E#7$s#F:##s#3&#/s#+)#D7#&%#&+#&.#j#%s#J#As#K#j#&s#L#As#M#0s#ES#1S&#7#>OS'#s#7,s#As#(#s#A$#j##)#4s#ZS,E$s#[I##s#WS'#+S&#Ds#4#)S'.S,$s#_#s#1$s#`s#4##s#M&#/s#E)#Ds#1#&%#&+#&.#j#%s#d#As#e#j#&s#f#U#E4s#mS&E$s#nI##s#jS-#+S'#Ds#G#)S-.S&$s#r#s#D$s#ss#G##s#`&#/s#X)#Ds#D#&%#&+#&.#j#%s#w#As#x#4s#~S'E$s$#L##s#{S2#'s$%L+S-#D$#)S2)L.S'$s$)#s#W$s$*%##s#s'#'s$,'/s#l+#D$#&&#&-#&1#j#%s$/#As$0#0s$(S-1S.#7#>OS3#s#v,s$$2#s$$$#j##)#4s$=S-E$s$>N##s$:S.#'s$@N+S2#D$#)S..S-$s$C#s#q$s$Ds$@##s$1&#'s$Fs$B/s$**#D$#&&#&,#&0#j#%s$I#U#E4s$PS2E$s$QP##s$MS3#'s$SP+S.#D$#)S3)P.S2$s$W#s$)$s$X%##s$E'#'s$Z'/s$>+#D$#&&#&-#&1#4s$bS.I$s$cS%##s$_S4#'s$eS%+S3#D$#)S4)S%.S.$s$i#s$=$s$j%##s$W'#'s$l'/s$P+#D$#&&#&-#&1#0s$fS41S/#7#>OS5#s$X.S3,s$c##s$c%#j##*#'s$|S*+S4#D$#)SQ)S*$s%#+s#Z$s%$$##s$m&#'s%&&/s$f*#D$#&&#&,#4s%-S4N$s%.S)##s%*S/#'s%0S#+S/#D$#)S5)S#.SQ$s%4#s#=$s%5%##s$~'#'s%7'/s$w+#D$#&&#&-#'s%>S,+S5#D$#)S;.S/$s%A#s#8$s%Bs$s##s%/&#'s%Ds$u/s%(*#D$#&&#&,#0s%=S;1SG#7#>OS<#s%/.S5,s%:##s%:%#j##*#)S=$s%R's#2$s%Ss$n##s%@%#'s%Us$p+S;/s%:##D%#&'#'s%\S'+S=#D$#)S<.S=$s%_#s#/$s%`s$N##s%M&#'s%bs$P+SG/s%G##D%#&'#)S>.SG$s%i#s%>$s%js$F##s%W&#'s%ls$H+S</s%Q##D%#&'#0s%eS>1SH#7#>OM#s%W.S<,s%b##s%b%#j##*#'s%ys$:+S>/s%^##D%#)SH.S>$s&##s%$$s&$s$.##s%m&#'s&&s#z+SH/s%g##D%#+M/s%j#2#0s%}M#C$#?FM0s&$##C#&USICj#'CE#CIEUSk#j#(C#j#'C#2E5C#j#'D#5Cs&/?FEj#'C#5CMGCDCCS?.H$SJMM#BDDDCCCS@HHHS6SAs&#s&4'83#GDCCCHH00)83#5C7@CC323.95$88#'s&Ds$%#D#<2$#C#9USID2I#C#4#DIEVSlIEWSm%$#j#(D#j#'D#5C,U6M0s&F#BDDDCCCS@HHHS6SAs&6s&G:s#+$6@DC.Hs#$'20&s#+$#H20#E's&XS/+S$#D$#2%?FS$#C$#5C%UBS$5CS$GCDCCS?s#.Hs#$SJS$S$#@DC:Hs#03,)&+%#H+(#S*'s&bs$3F#2$*F#'s&hS;F#2$*F#QFQ<FQ?FQ#C#Q&%#*QF#C&F&$#I&#?FS0VSns',s'&<Fs'-*Fs'(<Fs'(k##$#k##&#*Fs'2WSos'3s'-Ij##SR#j#)%#*Fs'/k##SR#k#)(#JCS+JCs&jJCs&lCC$#CC&#K#SBL(#JCs&oUSpS9VSqC#WSrC#+CC&#CC.#K#SBL0#CC1'K#SBL3#CC43K#SBL6#USSS14S1$#4S1(#4S1,#4S15#PS1VSsCLUStCXSuC$I#USvCUSwCZSx#KGGJPVSTCS9VSTCs'\8C$SC#9'KGGJ#R[SU(KGGJ'#VSVCF8C'S7#9+KGGJ#R8C*SC%9-KGGJ#R[SU.KGGJ%#[Sy/KGGJ)#USzG8C*S7.92KGGJ#RVSVCs'IWSWC#2WSWC$28C$SC#97KGGJ#RM8KGGJ(*#M9KGGJ,+#VS{:J5SXSYVS|EL#SX#SYm$%#WS}CFIXS~EL$#l#**)#l#+s#$s###l#,s#)s#(#j#-C#j#.C#j#/SZ##CEI&L#*IF#CEF&$#I&#*FL0s'dL0s'eN#C$#k##&#k##(#k#-C#k#.C#k#/SZ#<FS[YE#S[NPQl#04%#l#1s#\s#Y#l#2s#fs#a#l#3s#hC#l#4s#rs#j#l#5s#vs#t#l#6s#{s#y#l#7s#~s$(#l#8s$/s$=#Ns$Ws$Ts$B#/s'gs$/2#1QE7#>OS0#s'k.S$,s'v##s'v%#j#9C#)S(:s(2,#3s(3s'r#,s'|##s'|E)j#:s'}#)S/.M$s(9#s&V$s(:%#+S(/s'{#:s(=#E3s(>s'}#,s(+##s(+#4j#;s(-#:s(B<-'s(C.D>#:s(E#.$s(F&#3s(Gs(*E,s(4##s(4#=j#;s(6#USSs(KD2s$H$s(MBs&W:s(N$#$s(OE#3s(Ps(3#,s(=##s(=#s#&j#;s(?#D:E:s(U#*$s(V-#3s(Ws(:#,s(D##s(D#s#-j#<D#:s([E0$s(\3#3s(]s(@#,s(J##s(J#s#3j#<D#$s(a8E3s(bs(E#,s(O##s(O#s#8j#;s(Q#3s(fs(Is#0's(gs#1Ds(K#3s(i#s'*$s(j&#,s(WE#s(W#s#@j#;s(Y#'s(ns#CDs(R#3s(p#s&z$s(qE#,s(^##s(^#s#Gj#;s(`#Ds(XE3s(v#s'$$s(ws#L#,s(d##s(d#s#Mj#<D#3s({Es')$s(|s#Q#,s(i##s(i#s#Rj#<D#$s)$s#UE,s(m##s(m#s#Vj#;s(o#,s(ps#N5s(p#$s)*s#Ps#=VT#s)+s#Q-s(ts#R=%$#3s)-S+s'JVT$s).s'K-s(ws#B*%$#VS\s(os(oUS]s(p-DS+1%$#UT%M-Ds(s8$s#+#;Es(tj#<D#;s(vs(v*s),s),@DCSDHSESKs(xs)-s%\s(xs)-s%\#Ds#Us#p2s#V0s)0s%@#C$#5C%0s)3s%@BDDDCCCS@HHHS6SAs)#s)4s%cs%Gs%As%?@DCs%WHs%ms%Ps#\(%s#w$#H*'#I's)ES5#D#s#g2$?FS(#C$#5C%Us%jS(5CS(GCDCCS?s%vHs%lSJS(S(#@DCs%bHs%xs%[+)&s#o%#H+(#S)'s)Ns&mF#2$*F#'s)TS=F#2$*F#QFS0<FS0#Cs%CS0&$#*S0F#Cs%FF&$#I&#?FS88Cs$hS7s$h9s$zKGGJ#Rl#*#s$cs$]l#+s%#s$}#l#,s%+s%&#l#0#s#.El#1s%Fs%C#l#2s%Ps%K#l#3+C#l#44-#l#586#l#6=;#l#7@s#&#l#8s#,s#1#Ns#8s#7s#6#-Ds)Qs#:#s#es#=XT&s)os)Rs$9#-s)\s$:s#Zs#>s#h#3s)qs)Ts$:XT's)rs)Us$<s(3-s)_s#gs#d%$#$s)ts$+s$=VT(s)us$>-s)bs$?s$.%$#:s)wS+s$@VT)s)xs$A-s)es$Bs#r%$#VS\s$Ts$TUS]s$U-DS+s#z%$#-Ds$Ws$%#s$<I;s$=s$X*s#Fs#EBDDDCCCS@HHHS6SAs)cs)ts&Gs&+s&(s&#@DCSDHSESKs$@s#Hs#Es$[s#G#8Cs%>SCs%-9s%AKGGJ#R8Cs%@S7s%/9s%CKGGJ#RMs%DKGGJ%s%6#l#*#s%-s%'l#+s%Hs%G#l#,s%Qs%L#j#-C#j#.C#0s*$I#CE#*Is$|k##$#k#-C#k#.C#)M's*7#2#WEN#S#l#0-'#l#1s%xs%u#l#2s&&s%}#l#3s#=C#l#4s#Fs#?#l#5s#Js#H#l#6s#Os#M#l#7s#Rs#X#l#8s#^s#c#Ns##B@#XT*s*Ds$zs$k#-s*1s$Xs$Ps#&s$a#:s*Fs$|s$jXT+s*Gs$}s$ns$l-s*4s$`s$\%$#-s*5s$ms$f#s$vL1S^s%#7#>OQ#s*/6s$os*0's*NE;$#j#;s*<#'s*Qs$v6s$m#;(Ej#<D#6s$Ls':6s&RE;,#j#<D#'s*Ys(c6E#6s&W#;1#j#<D#6s*A'6E#;5#j#<D#6s%<s*E6s*Fs'H6s%>#;%#1s$,s*Z2s'L1s*\#1s$/#*&#BDDDCCCSLHHHSFSMs%Es$1s#Is*Ns*_s'25C'BDDDCCCSLHHHSFSMs*Ps*as'4s'R(#BDDDCCCSLHHHSFSMs%Hs$4s#L-(#@DCSDHSESK/+&-(#Fs%/*Fs$8QFS8<FS8#Cs#tS8&$#*S8F#Cs#wF&$#I&#?FT,RCs&'s&(RCs&)s&7RCs&)#8C%S7#9s&=KGGJ#RMs&>KGGJs&.s&0#l#*#s&'s%}l#+s&Bs&A#l#,s&Ks&F#j#-C#j#.C#*FI1s#Ys*{1s*|L1s#[#*%#k##'#k#-C#k#.C#'s+2s()2#WE#NS%l#0.&#l#2s&ss&p#l#=s&}s&x#l#><C#l#?s#%>#l#@s#(s#'#l#5s$Fs$D#l#6s$Ks$I#l#7s$Ns$T#l#8s$Zs$_#Ns#8s#3s#.#-Ds%vs#=#s%[I-Ds+$s#B#s%8s$lWS_s+Bs%hs)_-Ds#Ls#I$s#P#'s+Ds%hWS_s+Es%ls%j-Ds#Rs#P%$#-s+3s%ks#U#s%tL\T-OQS^s%us%~s++T.#-s+4s%ss%qs#^s#[#0s+>S$ZT/Cs&$s%y$#El#As&'s'|#j#Bs(&#j#Cs(+#V#IEj##s(2#j##s(D#Ss(Es(As(8#Ej#As(K#j#Ds(V#V#IEj##s([#j##s(w#Ss(xs(os(f#Ej#As(|#j#Es)/#V#IEj##s)4#j##s)Y#Ss)Zs)Ls)C#Ej#As)^#j#%s+]#V#IEj##s)s#j#'s+`#YS`s+as*4s*,#Ej#As*H#j#&s+c#V#IEj##s*\#j#'s+f#YS`s+gs*ys*q#El#Fs+Gs+0#-s+ns+Ys+J#PEj#As+]#j#Gs+c#j#Hs+e#j#Is+k#j#$s+s#j#Js+t#j#KC#j#Ls+q#j#MC#j#Ns+t#l#Os+{s+|#l#Ps,&s,'#l#Qs,6s,7##"). Qed.

(* [comment removed for export] *)
Lemma rrw_cells_app_split : forall m A cs1 cs2,
  rw_cells usegs m A (cs1 ++ cs2) -> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. try hcb. try hsb.
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma rrw_cells_app_join : forall m A cs1 cs2,
  rw_cells usegs m A cs1 -> rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells usegs m A (cs1 ++ cs2).
Proof. try hcb. try hsb.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x6cd90) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ rmrep (am_init_st st) m'.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.False Sort Prop.

(* [auxv_read8] is new in this file, ported from the in-tree donor
   projects/bzip2/bzip2_compress_target/proofs/lib/RS0/RMallocTree.v:347, which
   is the same donor this tree's Ref/RMallocTree.v:326-332 took [auxv_keys]
   from.  It is NOT a name LPS #38 removed; it is the [le8]-shaped companion of
   this file's [ru64s_read], which reads through the pre-#38 [u64s] block that
   [auxv_keys] replaced.  Declared here, not in RMallocTree.v, because this
   lane owns only RF_am_E.v and Spec/KLink2.v. *)
Lemma auxv_read8 : forall m A w a, bytes_at usegs m A (le8 w) -> a = wa A -> ov_read_bytes usegs m a 8 = Some (le8 w).
Proof. try hcb. try hsb.
  intros m A w a H ->. rewrite <- (Z.add_0_r A). change 0 with (Z.of_nat 0).
  rewrite (bytes_at_ov_read usegs m A (le8 w) 0 8 H) by (rewrite length_le8; lia). reflexivity.
Qed.

Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv usegs m -> rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 64 ->
  (c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = hsecret -> 0 <= c_secret (ctx st) < 2^64 ->
  evt usegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6ccdc) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  (* Ported from the in-tree plain-text donor
     projects/bzip2/bzip2_compress_target/proofs/lib/RS0/RF_am_E.v:128-315,
     the same donor that supplied this tree's [auxv_keys] retable
     (Ref/RMallocTree.v:326-332).  The recorded [KReplay.run] body that stood
     here referenced [...Ref.RMallocTree.rauxv_list] at column 5577 of its
     215,652-character constr array.  LPS #38 DELETED that name: the old
     [rauxv_list] spelled TEN auxv pairs with a literal [0;0] terminator, which
     is not the vector this release presents, and [rauxv_ok] now bounds the
     block with [auxv_keys] instead (Ref/RMallocTree.v:319-353).  The array is
     POSITIONALLY INDEXED (Common/KReplay.v:224-243), so the entry cannot be
     dropped, and no existing global is type-identical to it ([rauxv_list] was
     list-valued, [auxv_keys] is a Prop) -- so there is no re-emission under the
     type-identity guard either.  Declaring a local [rauxv_list] to make the
     blob resolve would re-introduce content #38 removed, under a published
     chain, so it is not done; the blob is replaced by the donor's plain proof.
     Same reasoning, same unit, as MainOpen.v:152 on
     [build_stack_bytes_within_span].
     Donor adaptations, each re-keyed from THIS tree's own statements:
       alloc_ceiling -> hceil, run_secret -> hsecret, run_guard -> hcanary,
       bz_ceil -> [try hcb; try hsb] (HeapCeil.v:15, HeapSecret.v:20),
       cps_pose/cps_destruct -> plain (0 in this unit), tauto_fast -> tauto,
       and rmrep_globals carries a SIXTH conjunct here (RVMLOCK,
       Ref/RMallocRep.v:132) that the donor's five-conjunct pattern lacks. *)
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5 & _) & _). unfold ctx_head_cells in C1.
  try hcb; try hsb; unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & x3 & x4 & x5 & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & X3 & X4 & X5 & X6 & X11 & X12 & X23 & XR).
  unfold RAUXV_CELL in AVC.
  (* the 27 keys of [auxv_keys] (Ref/RMallocTree.v:340-353); the tail after
     AT_EXECFN is the per-CONFIG_RSEQ disjunction *)
  destruct AVL as (AV0 & AV2 & AV4 & AV6 & AV8 & AV10 & AV12 & AV14 & AV16 & AV18 & AV20 & AV22 & AV24 & AV26 & AV28 & AV30 & AV32 & AV34 & AV36 & AV38 & AV40 & AV42 & AV44 & AV46 & AV48 & AV49 & AV50 & TAIL). rewrite <- (Z.add_0_r av) in AV0.
  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
  st1. st1. st1. st1. st1. st1.
  st1. rewrite sx32_wz by lia. st1. st1.
  st1.
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{ (* already initialised: the walk is skipped *)
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; try hcb; try hsb; lia. }
  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  (* one loop turn per auxv key that is neither AT_RANDOM (25) nor AT_NULL (0) *)
  Ltac skip_iter i key HB :=
    let RD := fresh "RD" in
    st1;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (auxv_read8 mX _ (wz key) (wa (_ + 8 * i)) HB ltac:(f_equal; lia)) as RD end;
    st1; try clear RD;
    st1; change (bv_eqb (wz key) (Z_to_bv 64 25)) with false; cbv iota;
    st1; change (negb (bv_eqb (wz key) (Z_to_bv 64 0))) with true; cbv iota;
    st1.
  skip_iter 0 33 AV0. skip_iter 2 40 AV2. skip_iter 4 41 AV4. skip_iter 6 42 AV6.
  skip_iter 8 43 AV8. skip_iter 10 44 AV10. skip_iter 12 45 AV12. skip_iter 14 46 AV14.
  skip_iter 16 47 AV16. skip_iter 18 51 AV18. skip_iter 20 16 AV20. skip_iter 22 6 AV22.
  skip_iter 24 17 AV24. skip_iter 26 3 AV26. skip_iter 28 4 AV28. skip_iter 30 5 AV30.
  skip_iter 32 7 AV32. skip_iter 34 8 AV34. skip_iter 36 9 AV36. skip_iter 38 11 AV38.
  skip_iter 40 12 AV40. skip_iter 42 13 AV42. skip_iter 44 14 AV44. skip_iter 46 23 AV46.
  (* AT_RANDOM (25) at index 48: the loop takes its value from index 49 *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (auxv_read8 mX _ (wz 25) (wa (_ + 8 * 48)) AV48 ltac:(f_equal; lia)) as RD end.
  st1. try clear RD.
  st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (auxv_read8 mX _ (wz rnd) (wa (_ + 8 * 49)) AV49 ltac:(f_equal; lia)) as RD end.
  st1. try clear RD. st1. st1. st1.
  (* split the frame so memcpy writes only the secret word *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge usegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  st1.
  call rmemcpy_callZ3.
  1:{ exact RND. } 1:{ apply length_le8. } 1:{ exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ lazymatch goal with H : mem_inv usegs ?mX |- mem_inv usegs ?mX => exact H end. }
  lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz hsecret))] |- _ => rename H into DST end.
  st1. st1.
  (* AT_EXECFN (31), then AT_RSEQ_* under CONFIG_RSEQ, then AT_NULL *)
  skip_iter 50 31 AV50.
  destruct TAIL as [(AV52 & AV54 & AV56) | AV52].
  (* the per-CONFIG_RSEQ tail is opened only here, so its facts still read the
     entry memory [m]: carry them across MU (they lie above sp, outside the
     frame and the context words) *)
  { pose proof (bytes_at_transport _ _ _ _ _ _ AV52 MU ltac:(cbn [disjoint_from]; rewrite length_le8; lia)) as T52.
    pose proof (bytes_at_transport _ _ _ _ _ _ AV54 MU ltac:(cbn [disjoint_from]; rewrite length_le8; lia)) as T54.
    pose proof (bytes_at_transport _ _ _ _ _ _ AV56 MU ltac:(cbn [disjoint_from]; rewrite length_le8; lia)) as T56.
    clear AV52 AV54 AV56. rename T52 into AV52. rename T54 into AV54. rename T56 into AV56.
    skip_iter 52 27 AV52. skip_iter 54 28 AV54.

    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (auxv_read8 mX _ (wz 0) (wa (_ + 8 * 56)) AV56 ltac:(f_equal; lia)) as RD end.
    st1. try clear RD.
    st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
    st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
    (* the memcpy destination narrowed to the single secret word *)
    lazymatch type of DST with rw_cells _ ?mX _ _ =>
      assert (DST8 : rw_cells usegs mX (bv_unsigned sp + -64) [C8 (wz hsecret)])
        by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
            split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
      clear DST end.
    st1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; try hcb; try hsb; lia);
      pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
    clear MUh. unfold RCTX in MUc.
    st1. st1.
    set (stI := upd_ctx (fun c => set_init_done 1 (set_secret hsecret c)) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
    { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        change (pw stI ?q) with (pw st q). unfold wz at 2.
        (* the donor hard-codes its own RCTX here as the decimal 371176; this
           mirror pins ITS OWN value by computing RCTX from its own
           RMallocRep.v, so the two mirrors can never share one tree's address *)
        let ctxa := eval cbv in RCTX in
        lazymatch goal with H : rw_cells usegs ?mX ctxa _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MRX.
    st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch goal with Hm : rw_cells usegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells usegs mX (bv_unsigned sp + -56) ?csc |- _ =>
        pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
        cbn [app] in J2; clear Hm Hc;
        lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
          apply (rw_cells_merge usegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
      end end.
    apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
    unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
  }
  { pose proof (bytes_at_transport _ _ _ _ _ _ AV52 MU ltac:(cbn [disjoint_from]; rewrite length_le8; lia)) as T52.
    clear AV52. rename T52 into AV52.

    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (auxv_read8 mX _ (wz 0) (wa (_ + 8 * 52)) AV52 ltac:(f_equal; lia)) as RD end.
    st1. try clear RD.
    st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
    st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
    (* the memcpy destination narrowed to the single secret word *)
    lazymatch type of DST with rw_cells _ ?mX _ _ =>
      assert (DST8 : rw_cells usegs mX (bv_unsigned sp + -64) [C8 (wz hsecret)])
        by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
            split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
      clear DST end.
    st1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; try hcb; try hsb; lia);
      pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
    clear MUh. unfold RCTX in MUc.
    st1. st1.
    set (stI := upd_ctx (fun c => set_init_done 1 (set_secret hsecret c)) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
    { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        change (pw stI ?q) with (pw st q). unfold wz at 2.
        (* the donor hard-codes its own RCTX here as the decimal 371176; this
           mirror pins ITS OWN value by computing RCTX from its own
           RMallocRep.v, so the two mirrors can never share one tree's address *)
        let ctxa := eval cbv in RCTX in
        lazymatch goal with H : rw_cells usegs ?mX ctxa _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MRX.
    st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch goal with Hm : rw_cells usegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells usegs mX (bv_unsigned sp + -56) ?csc |- _ =>
        pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
        cbn [app] in J2; clear Hm Hc;
        lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
          apply (rw_cells_merge usegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
      end end.
    apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
    unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
  }
Qed.

End HCW.

