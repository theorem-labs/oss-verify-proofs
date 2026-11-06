(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame HeapCeil SymExec2 SymExec2Sound SymRun RefPrintfLib MemSplit LibTail MainMem.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsPrintfFirst.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amem_grows_wmono : forall m m', mem_grows m m' -> wmono asegs m m'.
Proof.
  intros m m' Hg x Hw. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - assert (m' x <> None) as H' by (apply Hg; congruence). destruct (m' x); [discriminate|contradiction].
  - destruct (m' x); [discriminate|]. exact Hw.
Qed.
Lemma aframe_mod_wmono : forall m m' rs, frame_mod m m' rs -> wmono asegs m m'.
Proof. intros m m' rs [_ Hg]. apply amem_grows_wmono. exact Hg. Qed.

Lemma find_segment_asegs : forall (x : Z),
  find_segment asegs x 1 =
    if ((0x10000 <=? x) && (x + 1 <=? 0x4d000))%Z then Some Asan.Asan_segment_000
    else if ((0x4d000 <=? x) && (x + 1 <=? 0x115000))%Z then Some Asan.Asan_segment_001
    else if ((0x115000 <=? x) && (x + 1 <=? 0x11d000))%Z then Some Asan.Asan_segment_002
    else if ((0x11d000 <=? x) && (x + 1 <=? 0x67f000))%Z then Some Asan.Asan_segment_003
    else None.
Proof. intros x. reflexivity. Qed.

Lemma aro_addr_true : forall (a : word), 0x10000 <= bv_unsigned a < 0x115000 -> ro_addr asegs a = true.
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x4d000); cbn [andb]; [reflexivity| | lia | lia].
  destruct (Z.leb_spec 0x4d000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x115000); cbn [andb]; [reflexivity| lia | lia | lia].
Qed.

Lemma aro_addr_false : forall (a : word), (bv_unsigned a < 0x10000 \/ 0x115000 <= bv_unsigned a) -> ro_addr asegs a = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x4d000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x4d000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x115000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x115000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x11d000); cbn [andb]; try lia; try reflexivity;
  destruct (Z.leb_spec 0x11d000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x67f000); cbn [andb]; try lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amem_inv_ro_none : forall m, mem_inv asegs m -> forall i, 0x10000 <= i < 0x4d000 -> m (Z_to_bv 64 i) = None.
Proof.
  intros m Hinv i Hi. destruct (m (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
  pose proof (Hinv _ _ E) as Hro. rewrite aro_addr_true in Hro; [discriminate|]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma amem_inv_frame : forall m m' rs,
  mem_inv asegs m -> frame_mod m m' rs ->
  Forall (fun r => bv_unsigned (fst r) + snd r <= 2 ^ 64 /\ (bv_unsigned (fst r) + snd r <= 0x10000 \/ 0x115000 <= bv_unsigned (fst r))) rs ->
  mem_inv asegs m'.
Proof.
  intros m m' rs Hinv [Hout Hg] Hrs a b Hab.
  destruct (ro_addr asegs a) eqn:Ero; [|reflexivity]. exfalso.
  assert (Hcase : OSSVerify.Proofs.boost_beast.http_request.lib.Frame.outside a rs \/ (bv_unsigned a < 0x10000 \/ 0x115000 <= bv_unsigned a)).
  { clear Hab Ero Hout Hg Hinv. induction rs as [|[r n] rs IH]; [left; exact I|].
    inversion Hrs as [|x l [Hnw Hr] Hl]; subst. cbn [fst snd] in Hnw, Hr.
    destruct (IH Hl) as [Ho|Hx]; [|right; exact Hx].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r)) as [Hlt|Hge]; [left; cbn; split; [unfold in_rng; lia|exact Ho]|].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r + n)) as [Hin|Hout']; [|left; cbn; split; [unfold in_rng; lia|exact Ho]].
    right. lia. }
  destruct Hcase as [Ho|Hx].
  - rewrite (Hout a Ho) in Hab. pose proof (Hinv a b Hab). congruence.
  - rewrite aro_addr_false in Ero by exact Hx. discriminate.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.

(* [comment removed for export] *)
Lemma amem_inv_wbytes_high : forall m (A : Z) bs,
  mem_inv asegs m -> AIMG_TOP <= A -> A < 2 ^ 64 -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  mem_inv asegs (wbytes m (Z_to_bv 64 A) bs).
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.AIMG_TOP); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.wbytes); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.ZArith_dec.Z_lt_le_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.ro_addr); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.wbytes_below); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.u_small); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.Tauto.AND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsDrvMem.aro_addr_false); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.CatExec.wbytes_above)|] [|@s; @o; @z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @__sat66; @__sat65; @cstr; @Hab; @Hlt; @l; @__p1; @Hin; @__x3; @Hout; @Hge; @b; @a; @Hl; @HA64; @HA; @Hinv; @bs; @A; @m|] "#'q#8$.#@#m###n#l#%#$#R#,#v#)#.#/#s#1#'#(#0#&#+#3#4#C#*#-#W#2#>#e#7#<#;#A#B#Q#T#X#Y#]#_#a#f#z#~#}#Z$*$+$(#8#V#M#?#E#G#P#^#`#c#b#d#h#i#k#q#t#w#x#{#|#y$$#[$'$,$&$.$-$/$%#6$0#=#D#F#S$##p#o#K#J#I#L#j#H#O#N#U#u#g#r#\$):#u$#v%#w%#x%#y$#z'#{*#|%#}$#~%$#&$$+$%$$&%$'%$(%$)%#%&#V'$*%$+%$,)$-%#S.##########US1#US2#US1(US2#USG#k##&#US3%VS4S)H$SHH/1/-VSI$#%S%#*,S%+#,R#$#'13S*5S&#MI02E-2$#USJH&8H$J#%$/VS5$#&<S%VS6#K%$K$K%2$#&AR%#S+$S+$2$#VS7S)S#-S,#S8j#$%#&s#(S#%#N1s#*O5S$#NM0s#)M-s#)E#j#%s#*#US$M*s#-O+#,E#$#s#(j#&C#*s#2NUS9#+$$J#VSKs#0s#/%Js#1$Js#1%Js#1k##$#k##&#$Js#6WSLs#7s#6Ij##S:#j#'%#$Js#8k##S:#k#'(#VSMJs#=VS;SN#m##0UI#USOS/US3S/6CHUSPCXS<C$I#USQCUSRC7CS.7Cs#XWSSC$#3Cs#KWSTC#s#U(C%P#))GDDF#LUSUD.+GDDF$#$VSV,FVS;S,S=VSWEH-S,#S=m$%#WSXCJIXSYEH$#l#(*)#l#)65#l#*;:#j#+C#j#,C#,EI$#s#\,IH$#s#^k##%#k#+C#k#,C#*s#jS'+#4#S(Ol#--&#l#.s#*s#6#l#/s#2s#/#l#.s#<s#7#l#0s#@s#>#&s#us#M6CI(Cs#(S>s#$)s#*GDDF#L'S.####'###'#'#'#'#'#########################/#'S.####'#'#'#'#'#'#'#########################/##S.####'###'###'#########################/##5########################/#3Cs#&(C#Ps#|)s#~GDDF#L3CJ(C#Ps$#)s$%GDDF#L[SZs$&GDDF#s#Z.s$'GDDF's#{#.s$(GDDFs#\s#|#l#(#s#{s#ul#)s#`s$+#l#*s$1s$0#j#+C#%Es$p$s#4I$JH%Hs$sVS5$#k##&#k##(#k#+C#4S(S$Ql#-,$#l#.s$>s$J#l#/s$Fs$C#l#.s$Ps$K#l#0s$Ts$R#VS?O#8COs$Xs#ts#s#&s%/S*%#Ej#&C#(Cs$?S>s$>)s$AGDDF#L.s$BGDDF#s$:#l#(#s$9s$3l#)s$Fs$E#l#*s$Ks$J#j#+C#j#,C#%EI%IHk##$#k#+C#k#,C#&s%?N4S(#S#l#-*%#l#.s$Ws$c#l#/s$_s$\#l#.s$is$d#l#0s$ms$k#8CO7#s$/;ZS[NS$s${M;#ZS@s%Ds${s$xRs$w#0s%FS#-s%Fs$y#WNS*MEl#1&$#j#2s%&#U#Ej#3s%/#$Ns%*&s%QM,Os$yVS6$#%%$$%&2$#,S$s%(%s#+#$$s#,2$#VS7S)S&-S,#S8j#$%#&s%^S&*s%\S$+#,Q#%&#*s%`QUS9#+$$J#USASBUSA#9C#9C%9CSBWSCC$#WSCC&#VS\#S]WS^S/#s%'(Cs$|Ps$})s%#GDDF#L(Cs#bPs$~)s%%GDDF#LZS_s%&GDDFR's%y##'###'#########################/#3Cs$*(C#Ps%9)s%;GDDF#L[S`s%<GDDF8#.s%=GDDF:s%5#.s%>GDDF=s%6#l#(#s%5s%/l#)s%Bs%A#l#*Bs%F#j#+C#j#,C#j#4SD#$IE$s$LH$s$8HVSaR#k##%#k##'#k#+C#k#,C#k#4SD#&s&@Q#s&B##################/#%.s$=YE#S0/S&S(l#-:1#l#.s%ds%p#l#/s%ls%i#l#.s%vs%q#l#0s#Ls#J#VSbK#j#5s#P#U#Ej#3s#\#$s#Ts#W1s&XS-5S'#QK0s&WK-s&WE#j#%s&X#US'K*s&[S-+#,E#&s&aS+$$#j#&C#6CS%XS<Cs%wI#7Cs%K(Cs%rP#)s%vGDDF#L.s%wGDDF#s%o#l#(#s%ns%hl#)(s%z#l#*s&$s&##j#+C#j#,C#j#6C#$s%hH$s%gS%k##$#k#+C#k#,C#k#6C#*s&sSc+#XEs#:#S0S#l#-,&#l#.s&3s&?#l#/s&;s&8#l#.s&Es&@#l#0s#ws#u#&s&~s#(4S0S'S(l#-s$ds$\#l#.s&:s&F#l#/s&Bs&?#l#.s&Ls&G#l#0s#~s#|#VS?S-#8CS-s#%+*#YSdQS's#1K#ZS@s'(s#1s#.S*s#-#0s'*S&-s'*s#/#WQS+KEl#1&$#j#7s#8#U#Ej#3s$8#ZSEs$:s$9s$5s#<#El#$s$@s$=#j#8s$D#U#Ej#3s&s#ZSEs&us&ts&ps$H#El#$s&{s&x#l#'s'&s&~#j#1s'(#j#9s':#j#:s'=#1s'?S#WSFM#RVS4S)#m#&#j#;s'3#j#<s'8#j#=s'=#j#>s'?#j#?s'A#j#@C#j#As'D##"). Qed.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.option Sort Prop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma astore_ok_of_wview : forall m (n : nat) (a : word),
  (bv_unsigned a + Z.of_nat n < 2 ^ 64) ->
  (forall i, 0 <= i < Z.of_nat n -> wview asegs m (Z_to_bv 64 (bv_unsigned a + i)) <> None) ->
  store_ok RSEGS m a n = true.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.nat_ind); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.None); constr:(@Corelib.Init.Datatypes.bool); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok); constr:(@OSSVerify.boost_beast.http_request.images.Asan.M.loaded_segments); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.S); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u64_range); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_succ); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.add_0_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.Z_to_bv_bv_unsigned); constr:(@kc__2); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@stdpp.bitvector.definitions.BV); constr:(@Corelib.Init.Logic.I); constr:(@Corelib.Init.Datatypes.false); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.u_add1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Logic.False_ind); constr:(@kc__2 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))|] [|@i; @a; @n; @Hw; @Hn; @x; @y; @m; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat1; @__sat0; @cstr; @Hn0; @z; @b; @H0; @W0; @o; @__x2; @__sat2; @H; @__x3; @Hi; @IH|] "#(o#7$8#G#r###J#s#q#D#$#?#%#A#y#(#N#B#-#{#Q#*#&#T#+#)#'#W#,#=#S#_#k#w#/#0#U#.#3#1#;#:#>#P#7#[#Z#f#Y$)$,$/$4$7$3$2$.#E#X#]#b#c#e#g#i#h#j#l#n#p#}$#$$#~$&$'$*$+$-$0$1#2$8#6$9#5$:$(#@#L#V#I#K#H#u#t#C#M#^#|#o#<#O#\#a#`#d#z$6#F#R#m#v#x$%$5B#1%#-%#y&#)$#z%#{%#|$#}%#~'$#*$$%$%&$&/#;$$'&$(+$)$$*%$+/$,5$-'$.$$/*$0%$1$$2'$3%$4%$5%$6)$7&3S-3#3#3#3#3#US8#US9#US8(US9#US:#k##&#-(E&J#$#;1;-VSI$#$&#(FE&S&$E#*%#-3S&##J45#.PS)#US;4%4$#)#k##*#k#$C#<S.OLS&%S$#S'k##%#k##3#k#%?#j#&K#&S4#=#$#9$E%*9#.PO4%s#$#3)#k##&#k#$C#'S$S'j#'$#j#(,#j#%s#.#0L&##s#,#$#s#(0S*&#$E#*s#*#.PS%s#%%s#5#s#$)#k##&#k#$C#USJL-s#>L(F#$$s#5*$#(FF0O&#$F#*&#&O;S-#$#$F#*+#'S<,WS=--#j#)CE$JEUSK#j#*C#j#)C#'CF&E'C#j#)K##E1j#)C#'C4/KKCCS+II$S/O5#/KCCCII//':4#5CCM0M,FF+:5#ZS>=:=52##s#M<$#s#T#s#O9$#s#VU,=U7##s#S##JEXSLCCSM#'C#j#+C#j#&C#'Cs#Y/KCCCII??7s#*+36CCCCCCQ@@@Q%s#[s#[$s#*+#'Cs#b%Cs#cs#cm#$#5CCMs#$M@4.&s#es#e#742#L8S)&S)(F#VSNs#ls#k$Fs#m(Fs#m$Fs#mk##$#k##&#(Fs#rWSOs#ss#rJj##S?#j#,%#(Fs#tk##S?#k#,(#VSPFs#y'SQ#m##0UJ#USRS0USSS0=CJUSTCUSUC>CF?CS-+C$S1#,&HDDG#NUS;D+C'S1',)HDDG#N>Cs#L1C)#+C+S##,-HDDG#N9.HDDG'#2/HDDG+*#VSV0GVSWEL%S$#S'm$s#q#WSXCFJXSYEL$#l#-)(#l#.98#l#/<;#j#0C##Js#\$F#*s#d#k##s$<#k#0C#&S5VE#S*l#1*%#l#2s#'s#3#l#3s#/s#,#l#2s#9s#4#l#4s#=s#;#l#5s#?s#O#XS@s#ks#fs#T#VJF##s$DF4s$V#.PS%#%s$T#s$C)#-s$ZS*##F4s$\E.PS,#%s$Z#s$I)#j#6C#USZ)@C)$E*#4s$c+.PS(#%s$a#s$P)#-s$gO4s$h#.PRE%s$f#s$U)#j#7s$k#US[O@s$m($EO#.PS,O%s$l#s$[)#l#8&#El#83/#l#8B=#.PS%S&%s$r#s$a)#.S.S(S*%s$uEs$d)#WS\s${s$5S]WSAs$|S(#<S.S2#RnS:$s${$#)S$J#%$#7##SB%S$#S'k#9(#j#:s$}#VS^s%#E%s%##s$n)#-s%)S(##s$@#Es#>$#s$}j#6C#0R&##)#$#s%&&R##s$I#-#$#s%*Us$<&Us$G##1#'C2'C*/KKCCS+IIs$AS/R+#/KCCCIIs$Ls$Ls$D0(#6CCCCCCQs$Ms$Ms$MQs$266&0(#5CCMs$NMs$J0(#s%3s%3s$-70,#S%8S5(Fs#T=CLUS_CXSCC$J#?Cs%K1C#s#n1Cs#u#>Cs%?WS`C#s%I+C%S##,s#{HDDG#N1Cs#s)+C#S#&,s#~HDDG#N2s$#HDDG&s#z#l#-#s#rs#ml#./s$&#l#/s$*s$)#j#0C#j#;C##Es#m$#s%K#s#oL$#s%Mk##%#k#0C#k#;C#&S6-s%]S7WE$#Ol#1-&#l#<s$9s$E#l#2s$As$>#l#<s$Ks$F#l#4s#%s#$#l#5s#'s#1#-s%es#G0S40#:C#:C%:CS4AC$#AC&#VSD#SEWSFS0#s$F+Cs$BS1s#,,s$DHDDG#N+Cs$<S#s#*,s$FHDDG#N2s$GHDDGs#*s$B#2s$HHDDG&s$C#l#-#s$;s$6l#.s#4s$K#l#/+s$N#j#0C#j#;C#(FJ#Ls%5#J#$#s%r$%s%sk##$#k##(#k#0C#k#;C#XEs#)s#(S*Ol#1-$#l#<s$^s$j#l#2s$fs$c#l#<s$ps$k#l#4s#Js#I#l#5s#Ls#V#VSGS(#ZSHCs#cs#`s#)s#(#$Es$C*s&$#-s&2R##s%I#EL4s&5#.PSa#%s&3#s%~)#j#6C#0S2&##,#$#s&2&S2##s%U#0#$#s&6Us%H&Us%S##4#'C5'C*/KKCCS+IIs%MS/S2+#/KCCCIIs%Xs%Xs%P0(#6CCCCCCQs%Ys%Ys%YQs%>99&0(#5CCMs%ZMs%V0(#s&?s&?s%970,#S,8S3&S3(F#1Cs$ws#h1Cs$~#+C#Sbs#c,s%&HDDG#Nl#-#s$us$pl#.s#ns%)#l#/s%-s%,#j#0C#j#;C##s%nJ#E##s%aJ%C$#k#0C#k#;C#-s&^S6VES%#l#1+%#l#<s%:s%F#l#2s%Bs%?#l#<s%Ls%G#l#4:8#l#5<s#&##s#60#s#6J%C$#-s&iS5#s&$L#$#.PS6s$n%s&i#s&X)#j#6C#(F(0S3&#$+#*&##s#*s&/$.#*)#'S<*WS=++#'C2'Cs#0/KKCCS+IIs&&S/S3s#1#/KCCCIIs&1s&1s&).*#5CCMs&2Ms&.66&.+#ZS>1.1+(##90$#s&v#;/$#s&xUs&.s#9Us&9##?#'C@/KCCCIIs&<s&<s&49&.6CCCCCCQs&=s&=s&=Qs%~BB$9&#5CCMs&>Ms&:,&#s'#s'#s%y7,*#R8S7&S7(F#+Cs%aS#s$L,s%dHDDG#N9s%eHDDGs%a#1Cs%^s%d+Cs%fS1#,s%hHDDG#N+C%S#s$Q,s%jHDDG#N9s%kHDDG%#2s%lHDDG)s%g#l#-#s%_s%Zl#.s$Xs%o#l#/s%ss%r#j#0C#j#;C#$EJ*s'6#(Fs#J$s#Ks$(*$#k##&#k#0C#k#;C#&ScWE#S(S%l#1-%#l#<s&&s&2#l#2s&.s&+#l#<s&8s&3#l#4B@#l#5s#$s#,#XS@s#<s#9s#1#VS,s#G##s#Is&j##L@Cs#Is#E%#El#=s#Ps#M#WSAs'XRs%;-s'Y#0s$Q:C#AC#s$NVSD#SEWSFS0#s&6=CS&XSCCs$|J#USdS-?C#1C#s&/1Cs&6#+C#S#s$z,s&:HDDG#N+Cs%$S#',s&<HDDG#N9s&=HDDGs$W#2s&>HDDG#s&9s$V2s&?HDDG's&:#l#-#s&2s&-l#./s&B#l#/2s&E#j#0C#j#;C#j#>C##Es$U$#s'h(FL$LS&*$#k###s$Wk##'#k#0C#k#;C#k#>C#&SeYE#S%s#}OS)l#1/%#l#<s&Xs&d#l#2s&`s&]#l#<s&js&e#l#4s$8s$6#l#5s$:s$D#VSGR#ZSHCs$Ts$Ns#0s#.#j#?s$W#j#$C#WS,s%js$[#j#9s%c#j#7s(+#U#Ej#7s(-#%s(-s'xs'x)#%S$SBS''s(0s'{UE#VSf%#j#9'#YSgs(5s%q*#EU#Jl#:s%|s(6#l#9s&%s%~#l#,s']s'Y#<S.S)Ls'g%S$#S'm#%#j#'s'b#j#(s'l#j#%s(A#j#@s(%#j#&K#XShs(&s't#Ej#&K#j#+s(B##"). Qed.

Lemma astk_stk_ok : forall m lo hi (sp : word) K,
  stk asegs m lo hi -> lo <= bv_unsigned sp - K -> bv_unsigned sp <= hi -> 0 <= K -> hi < 2 ^ 64 ->
  stk_ok RSEGS m sp K.
Proof.
  intros m lo hi sp K (H1 & H2 & H) Hlo Hhi HK Hhi2 a n Ha Hn. pose proof (u64_range a).
  apply astore_ok_of_wview; [lia|]. intros i Hi. rewrite <- wa_eq. apply (H (bv_unsigned a + i)). lia.
Qed.

Lemma aseg_rom_high : forall x : word, 0x67f000 <= bv_unsigned x -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1%Z.
  change Asan.M.loaded_segments with asegs. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x4d000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x4d000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x115000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x115000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x11d000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x11d000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x67f000); cbn [andb]; try lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma astk_grows : forall m m' l h, stk asegs m l h -> 0x67f000 <= l -> h <= 2 ^ 64 -> mem_grows m m' -> stk asegs m' l h.
Proof.
  intros m m' l h (S1 & S2 & S3) Hl Hh Hg. split; [exact S1|]. split; [exact S2|].
  intros x Hx. destruct (S3 x Hx) as [Hw [b Hb]].
  assert (E0 : exists b0, m (wa x) = Some b0).
  { unfold mrd in Hb. destruct (m (wa x)) as [b0|] eqn:E; [exists b0; reflexivity|].
    rewrite seg_rom_same in Hb. change asegs with RSEGS in Hb.
    rewrite aseg_rom_high in Hb; [discriminate|]. rewrite wa_eq, u_small by lia. lia. }
  destruct E0 as [b0 E0].
  assert (E1 : exists b1, m' (wa x) = Some b1).
  { destruct (m' (wa x)) as [b1|] eqn:E; [exists b1; reflexivity|]. exfalso. apply (Hg (wa x)); congruence. }
  destruct E1 as [b1 E1]. split.
  - unfold wview. rewrite E1. discriminate.
  - exists b1. unfold mrd. rewrite E1. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acells_ok_frame : forall m m' rs cs,
  forallb cell_wf_b cs = true -> cells_ok m cs -> frame_mod m m' rs ->
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall r, In r rs ->
     a + Z.of_nat w <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= a end) cs ->
  cells_ok m' cs.
Proof.
  intros m m' rs cs Hwf Hc FM Hd. unfold cells_ok in *.
  induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_ok in *. rewrite <- Hok. apply (frame_mod_rdn RSEGS m m' rs w (Z_to_bv 64 a) FM); rewrite u_small by lia; [|lia].
  intros i Hi. apply outside_of_disjoint. intros r0 Hr0. pose proof (Hx r0 Hr0) as D. rewrite u_small by lia. lia.
Qed.

Lemma arange_none_frame : forall m m' rs lo hi,
  (forall i, lo <= i < hi -> m (Z_to_bv 64 i) = None) -> frame_mod m m' rs ->
  (forall r, In r rs -> hi <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= lo) -> 0 <= lo -> hi <= 2 ^ 64 ->
  forall i, lo <= i < hi -> m' (Z_to_bv 64 i) = None.
Proof.
  intros m m' rs lo hi Hn [Hout _] Hrs Hlo Hhi i Hi. rewrite Hout; [apply Hn; exact Hi|].
  apply outside_of_disjoint. intros r Hr. rewrite u_small by lia. destruct (Hrs r Hr); lia.
Qed.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.

Lemma ardn_frame : forall m m' rs (a : Z) n bs,
  frame_mod m m' rs -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs ->
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall r, In r rs -> a + Z.of_nat n <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= a) ->
  rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
Proof.
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Frame.frame_mod); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn); constr:(@OSSVerify.boost_beast.http_request.images.Asan.M.loaded_segments); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Init.Datatypes.Some); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Logic.or); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Frame.frame_mod_rdn); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Frame.outside); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.MainMem.outside_of_disjoint); constr:(@kc__3); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2Sound.SX2S.u_small); constr:(@Stdlib.micromega.EnvRing.PEpow)|] [|@r; @o; @i; @z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__p1; @__p2; @__arith; @__sat1; @__sat0; @cstr; @H; @Hr; @Hi; @Hrs; @Hn; @HD; @FM; @bs; @n; @a; @rs; @m'; @m|] "#'>#7$*#A#s#t#r###$#J#&#%#{#.#'#*#(#-#)#7#+#z#d$##/#0#F#,#=#j#6#;#:#>#H#O#P#^#`#i#y#~$$$'$($+$,#@#C#N#Y#]#_#b#a#k#n#o#q#|$%$)$*$&#5#[$-#2#3#Z#V#U#B#I#L#K#v#u#p#M#Q#X#<#G#R#l#g#f#x#}#S#T#h#c#w#?#E#D#\#e#m#W@#i%#j%#k%#l'#m*#n+#o$#p%#q%#r$#s%#t%#u'#v%#w&#x%#y*#z&#{&#|$#}&#~&$#$$$'$%&$&$$'%$(%$)),S,,#,#,#,#,#US/#US0#US/(US0#US1#k##&#VS?'C9#9'WS@PNJUS1$--J:S*R#KVS2'H;&$##IN)N$P#US3:US36VSA$#%&#WS42GS$)O$S$#4:CH.<##%#5=CH$%###S$*&#k##,#k#$=#-s#$O:S*Q#R-s#&S$:S*Q#O;>#Gj#%?##IG)S$%G#+%#$KH-s#/#VSB#Mk##&#k#&C#j#'C#%G=+-#$S+H-s#7#WS4s#2GM$MJ4s#9CK.s#;#%G#5s#<CK$%###G*&#j#'C#VNHG)Q$M###s#+#s#)M*$#)M$S(###1#/S(*$#$S)P4s#MCJ.s#O#%%#5s#PCJ$%###(*&#j##+#)S($S)###+<S))S)#I#VSCs#Js#I%Is#K#Is#K%Is#Kk##$#k##&##Is#PWSDs#Qs#PHj##S5#j#(%##Is#Rk##S5#k#((#VSEIs#WVS6SF#m##0UH#6S76#0C#0C%0CS71C$#1C&#=#S-USGS&7S&$#9S&>CK>CNUSHC/C$J#/C&H#USICUSJC2CS,US8s$*2C#8C%#US8S,2C#&C%S%#'*FDDE#LUSKDZS9,FDDER2Cs$3&C#S'+'/FDDE#L30FDDE&#8C0&&C#S','3FDDE#LZS94FDDEO[S:5FDDE$#(6FDDE(-#(7FDDE/.#VSL8EVS6S;S<VSMGK;S;#S<m$%#WSNCIHXSOGK$#l#)*)#l#*BA#l#+s#)s#(#j#,C#j#-C#j#.C#j#/C#j#0S##j#1S##$GJ##K%KN+P#$KJ%#N*#Ok##&#k##)#k#,C#k#-C#k#.C#k#/C#k#0S##k#1S##4s$VCS+.s$X#5s$XCS+$$#$S.M#$##IM)SP\G%$#)MS.PQl#2;,#l#3s#Ss#_#l#4s#[s#X#l#3s#es#`#l#5s#is#g#j#6s#k#U#Gj##s#{##s#tS)/Cs#NKs#M>CJ/C$H#2Cs$q8Cs#G#&C#S%s#M's#OFDDE#LVS=CI&C#S%s#F's#RFDDE#L3s#SFDDE#s#I&C)S%s#E's#UFDDE#L[S:s#VFDDEs#D#(s#WFDDE&s#N#(s#XFDDE+s#O#l#)#s#Cs#=l#*1s#[#l#+s#cs#b#j#,C#j#-C#j#.C#j#/C#j#0S##j#1S###s#8G#IK+#P$NP##s#<*O#k##&#k##)#k#,C#k#-C#k#.C#k#/C#k#0S##k#1S##%s#7s#:%Ms#5\G$#s#;s#<MS.PQl#24&#l#3s$*s$6#l#4s$2s$/#l#3s$<s$7#l#5s$@s$>#j#6s#2#U#Gj##s$Q#ZSQs$Ss$Rs$Hs#6#Gl#%s$\s$W#-s%As$f.s%B#<Q#Is$_6s$50C#1Cs$6s$41C$#=#S-6'0C#1C#s$8=#S-7S&#s$77S&(#/Cs$6Hs#D&Cs$&S's$+'s$2FDDE#L3s$3FDDEs#?#8Cs$3s$.VS=Cs%CWSRC#s%V&C%S'#'s$8FDDE#L&Cs#GS%s$8's$:FDDE#L&Cs#IS%s$,'s$<FDDE#L&Cs$.S')'s$>FDDE#L3s$?FDDE%#(s$@FDDE(s$7#(s$AFDDE+s$8#(s$BFDDE1s$9#l#)#s$-s$'l#*6s$E#l#+8s$L#j#,C#j#-C#j#.C##IH%HK+$#$HJ%#s%Y$JN#I#%$s%\+$#k##s#M#k##(#k##+#k#,C#k#-C#k#.C#)SSZG#S$STOQMl#24%#l#3s$ms$y#l#4s$us$r#l#3s%#s$z#l#5s#=s#<#VS>s%H#?Cs%Is%As#Bs#@#j#7s%K#j#$s%|#WSUs%NQ#j#8s%Q#j#&C#.s&*s%d<R)R#I#7S&s#Cs$s/Cs$qHs$o&Cs$kS's#8's$mFDDE#L3s$nFDDEs#6#(s$oFDDEs#7s$f#(s$pFDDEs#4s$g#(s$qFDDEs#}s$h#l#)#s$\s$Vl#**s$t#l#+,s${#j#,C#j#-C#$HK%#s&(#IJ%Js&*+$#k##s#w#k##'#k##s#7#k#,C#k#-C#YGs%[S(NROl#2.$#l#3s%9s%E#l#4s%As%>#l#3s%Ks%F#l#5A?#VS>O#?COs%ws#%s#$#$Gs&6##s&:j#'C#&Cs$}S%s#X's%1FDDE#L(s%2FDDEs#Rs%)#l#)#s$ys$sl#*s#'s%5#l#+s%>s%<#j#,C#j#-C#$GH%#s&E#As&Fk##$#k#,C#k#-C#WGs%tS(Rl#2*$#l#3s%Rs%^#l#4s%Zs%W#l#3s%ds%_#l#5s#:s#8#?CO7#s#<;]SVS*QS+S$Rs&CN;#VS2s&^PZSWs&]s&Ds&@$#Jj#9s&G#j#:s&T#j#(s&[#j#;s&]#j#<s&c#j#=s&e#j#>SX#j#?C#j#@s&i#j#As&l#j#Bs&m##"). Qed.

(* [comment removed for export] *)
Lemma arw_cells_frame : forall m m' rs A cs,
  rw_cells asegs m A cs -> frame_mod m m' rs ->
  (forall r, In r rs -> A + Z.of_nat (cells_size cs) <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= A) ->
  rw_cells asegs m' A cs.
Proof.
  intros m m' rs A cs RC FM Hrs.
  eapply rw_cells_transport; [exact RC | apply frame_mod_munch; exact FM | apply (aframe_mod_wmono _ _ _ FM) |].
  clear RC FM. induction rs as [|[r k] rs IH]; [exact I|]. cbn. split.
  - destruct (Hrs (r, k) (or_introl eq_refl)); cbn [fst snd] in *; lia.
  - apply IH. intros r' Hr'. apply Hrs. right. exact Hr'.
Qed.
