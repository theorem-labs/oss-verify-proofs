(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep Exec Frame TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt CXXRep HeapSR_iface XRep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Export XFuzz_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition FUZZ_LIVE2 : Z := 2^30.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section W.
  Variable H : hsr.
  Variable FT : mem -> Prop.

  Definition fuzz_stmt_with2 : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
           (s : PState) (LB : list block) (D N lo B : Z) (ds : list byte) (errv : word),
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N ->
      (* [comment removed for export] *)
      bytes_at rsegs m D ds -> Z.of_nat (length ds) = N -> N < 2^26 -> D mod 16 = 0 ->
      (1 <= N -> exists pD, In (pD, D, N) LB) -> (N = 0 -> D = P_FUZZ_EMPTY) ->
      (* [comment removed for export] *)
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + FUZZ_LIVE2 <= hs_LIVE_MAX H -> Z.of_nat (length LB) + FUZZ_CNT <= hs_LIVE_CNT_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->
      (* [comment removed for export] *)
      bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - FUZZ_STACK ->
      (* [comment removed for export] *)
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      XImg m -> CanaryReads m -> HStat FT m ->
      bv_unsigned ra mod 2 = 0 ->
      bv_unsigned sp <= 0x7fffffffffff ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      F = bvmap_empty -> fc = Z_to_bv 32 0 ->
      hs_SR H (fuzz_post H FT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_FUZZ_ENTRY) fc None m (seg_rom rsegs)) mo).
End W.

Definition fuzz_stmt2 (H : hsr) : Prop :=
  exists FT : mem -> Prop, ft_local FT /\ fuzz_stmt_with2 H FT.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma fuzz_stmt2_of_1 : forall H, fuzz_stmt H -> fuzz_stmt2 H.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.HeapSR_iface.hsr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.fuzz_stmt); constr:(HCEIL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.mem); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.ft_local); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.fuzz_stmt_with); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt2.HCW.fuzz_stmt2); constr:(@kc__1); constr:(@Corelib.Init.Logic.ex_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt2.HCW.fuzz_stmt_with2); constr:(@Corelib.Init.Logic.conj); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap); constr:(@Corelib.Numbers.BinNums.xI); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.Model); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.PState); constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.block); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Datatypes.length); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.P_FUZZ_EMPTY); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.HeapSR_iface.hs_RHEAP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.HeapSR_iface.hs_KREL); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.HeapSR_iface.lb_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt2.FUZZ_LIVE2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.HeapSR_iface.hs_LIVE_MAX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.FUZZ_CNT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.HeapSR_iface.hs_LIVE_CNT_MAX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.HeapSR_iface.hs_rauxv_ok); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.stk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.FUZZ_STACK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.RATP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.XImg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.CanaryReads); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.HStat); constr:(@LinuxProcessSemantics.Riscv.Prelude.bvmap_empty); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XFuzz_stmt.FUZZ_LIVE)|] [|@FT; @pD; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__arith; @__sat38; @__sat36; @__sat34; @__sat32; @__sat29; @__sat30; @__sat31; @__sat33; @__sat35; @__sat37; @__sat39; @cstr0; @cstr; @errv; @ds; @B; @lo; @N; @D; @LB; @s; @mo; @m; @fc; @F; @t6; @t5; @t4; @t3; @s11; @s10; @s9; @s8; @s7; @s6; @s5; @s4; @s3; @s2; @a7; @a6; @a5; @a4; @a3; @a2; @a1; @a0; @s1; @s0; @t2; @t1; @t0; @tp; @gp; @sp; @ra; @FZ; @FL; @H; @FT0; @x; @H0|] "#'Q$+$z$D$O###$$t$0#%%%#(#'#)#&#-$=$H$R#1#4#3%&#+#,$C#D#.#*#0#/#_#2#8#6#B#k#I#F#Q%$$1$5$8$T$U$Q#`#a#b#c#Y#[#\#<#7#^#]$j$h#?#@#C#f$q#S$v$y%*%+%)%(%-%'%.%2%3#X#G$/$+$>$G$S$V$W$X$[$]$^$_$a$b$c$d$f$i$g$e$k$l$m$n$o$p#m#u#w$x$w${$|$z$}%#%,%/$~%0%4%5%1$*%6#t#j#i#h#g#e#d#Z#W#V#U#T#R#P#O#N#M#L#K#J#H#E#A#>#=#;#:#9$A$@$9$7$6$.$?$P$<$E$`$M$K$;$N$Y$4$3$2$J$I$L$s$u$:$B$F$Z$\$r;$b$$c%$d$$e&$f%$g$$h%$i$$j%$k%$l&$m$$n%$o%$p$$q%$r%$s&$t$$u$$v%$w$$x$$y%VS_HEk##S9S`.E-HIE/$#j#$&#US:I-HLE/(#.F-HKF/$#US:Mj##$#-HMI.N-HS'LVS;OE/2#j#$4#.KVS;S(K%P%#%#%#%#%#*#5##**#VSa#%*)5#6S)*.5#6#7-K&-S*#XSbQS+S,N0'L1#&C#S,(9#P%###%#(#2(#)S'#(>+O#&C#D(P$#OVS<RCVS<#CXS=RCES-XS=%C#S.WSc%#S#j#%R#VS>R#k##*#&CS+D&CS-Sdk##$#XSeS/S0S#S$WSfS?S%S$8S%,#Sg9S@$$#0S)S$1#,#ShUSiSA$$#WSjSBS1S#'s#7SC$#S0(s#:2s#)#)S%#'s#<SD+#s#$&C#D's#?SEXSkQSFS2#USlH$#SG's#CSHVSm#Sn$S1#'s#FSI%s#E%###%#%#USo#,)#USpS2USJSKWSqSK$#XSrQSL&#VSsQSM7s#SSt&s#SS/#USuS3USvSNVSwS4S*'s#XSO+#s#H&C#D#s#I########################################################################################(#$s#3#VSxs$+s$-&s$+S5#7s$+D&s$+S5#0S)S6USP#1$$D#0s$-S3USP#1$$D#'s$:S4:#s#~$D$$Ds$$'s$>Sy+#s$&$D#k##&#k##(#%s#F%#(#3s$5#)Ds$6$D%2s$8&)D#k##%#k##'#$Ds$<4s$=+Fj##G#j#&%#$D*k##G#k#&(#3s$Cs#y$Ds#z)Ds#zk##$#k##3#4s$Hs#~Fj##G#j#&0#$Ds$$k##G#k#&3#%s#a(#3s$P#$D$2s$R%)D#k##%#k##A#4s$V)Fj##G#j#&>#$D)k##G#k#&A#3s$\s$W$Ds$X)Ds$Xk##$#k##s#,#4s$as$\Fj##G#j#&s#)#$Ds$^k##G#k#&s#,#'s$xSz:#s$h$D$'s${S{+#s$k$D#k##s#3#k##'#:S7s$g$DS7+SQs$i$D#k##s#I#k##&#VS|Ds$uVSRS}#m##s#CUN#UM$US(%US.&USJSS6SSVS~CIUT#CXT$C$F#UT%CUT&CVSTCPVT'Cs%(*s#9WSUC$#WSVC&#VSTCs%CXSWC$SX#[SY*S8JJS&#SZUT(J*s#[WSUC+#WSVC-#XSWC#SX)[SY0S8JJS&#SZ\T)1S8JJS&)(#VT*2S&VSRS[S\VT+EI&S[#S\m$%#WT,CDFXT-EI$#l#'*)#l#(<;#l#)A@#j#*C#j#+C#,Es#N$#F,Fs#j$#Ik##%#k#*C#k#+C#9T.8S]WE$#S^l#,-&#l#-s#0s#q#l#.s#2s#f#l#/s#4s#Y#l#0s#6s#O#l#1s#@s#;#l#2s#Hs#B#l#3s#Ns#K#l#0s#Vs#R#l#4s#[s#X#l#/s#ds#_#l#5s#ks#h#l#.s#ss#o#l#6s#xs#u#l#-s$'s#}#l#7s$3s$,#l#8s$8s$6#l#9s$=s$;#8S6,#T/9T0$$#m#'#i#jS4T1T2T3T4SOT5T6SBSAS@S?S/SHSISESDT7SCS]T8T9T:T;SQT<S7T=T>T?T@TATBTCS5TDS^S6TES*SNS3TFSMSLTGTHSFTITJTKS1SGS2#S$S%S0S#S-S.S+OS(S'S,MKLNFEj##s$F#j##s$I#j##s$L#j##s$|#j##s%$#j##s%&#j##s%(#j##s%*#j##s%-#j##s%/#j##s%<#j##s%@#j##s%C#j##s%F#j##s%J#j##s%N#j##s%Q#j##s%S#j##s%Y#j##s%^#j##s%`#j##s%b#j##s%f#j##s%q#j##s%u#j##s%~#j##s&&#j##s&(#j##s&)#j#:s&5#j#;s&-#j#<C#j#=C#j#>C#j#?C#j#@s&5#j#ATL#j#BTM#j#CS9#j#Ds&:#j#Es&=#j#Fs&A#j#Gs&B#j#Hs&C#j#Is&D#j#Js&E#j#Ks&F#j#Ls&G#j#Ms&H#j#Ns&I#j#Os&J#j#Ps&K#j#Qs&L#j#Rs&M#j#Ss&N#j#Ts&O#j#Us&P#j#Vs&Q#j#Ws&R#j#Xs&S#j#Ys&T#j#Zs&U#j#[s&V#j#\s&W#j#]s&X#j#^s&Y#j#_s&Z#j#`s&[#j#as&\#j#bs&]#j#cs&^#j#ds&_#m##s&hXTNs&js&iF#XTOs&~s&lK#j#es&p#j#fs&r#V#FEj##s&u#j##s&{#YTPs&|s&{s&x#Ej#gs&~#j#hs'*#V#FEnS>%s',s'($##s''E#$%#i###j#gs'.#j#jTQ##"). Qed.
End HCW.
