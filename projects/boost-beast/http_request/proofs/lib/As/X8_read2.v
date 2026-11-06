(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     AXRep_fields AXRep_mbuf AXImgKit X8Kit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst
     X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4 X8_R_read X8_read_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cbn_ps := cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition al_okR (s : as_St H) (A MA R : Z) : Prop :=
  0 <= A <= MA /\ 0 <= R /\ as_Cm H MA - as_Cm H A + R <= as_AL H s.

Lemma al_okR_afford : asan_rt_hyps H -> forall s A MA R x,
  al_okR s A MA R -> 0 <= x -> A + x <= MA -> as_Cm H x <= as_AL H s.
Proof.
  intros HH s A MA R x (A0 & R0 & AL) Hx HAx. pose proof (ah_costs H HH) as (Cm0 & CmM & _ & _ & CmS & _).
  pose proof (CmS A x ltac:(lia) Hx). pose proof (CmM (A + x) MA ltac:(lia)). lia.
Qed.

Lemma al_okR_pay : asan_rt_hyps H -> forall s s' A MA R x,
  al_okR s A MA R -> 0 <= x -> A + x <= MA -> as_AL H s' >= as_AL H s - as_Cm H x -> al_okR s' (A + x) MA R.
Proof.
  intros HH s s' A MA R x (A0 & R0 & AL) Hx HAx AL'. pose proof (ah_costs H HH) as (Cm0 & CmM & _ & _ & CmS & _).
  pose proof (CmS A x ltac:(lia) Hx). split; [lia| split; [exact R0| lia]].
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma al_okR_pay_diff : asan_rt_hyps H -> forall s s' A MA R x cost,
  al_okR s A MA R -> 0 <= x -> A + x <= MA -> cost <= as_Cm H (A + x) - as_Cm H A -> as_AL H s' >= as_AL H s - cost ->
  cost <= as_AL H s /\ al_okR s' (A + x) MA R.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.asan_rt_hyps); constr:(HCEIL); constr:(H); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.as_St); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_read2.HCW.al_okR); constr:(@kc__1); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.as_Cm); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.as_AL); constr:(@Stdlib.ZArith.BinInt.Z.ge); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsCXXHeap.ah_costs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.cost_laws); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.as_Cf); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.RingMicromega.OpGe)|] [|@n; @n'; @b; @a; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__x3; @__x4; @__x5; @__x6; @__x7; @H1; @H0; @_H1; @CmS; @_H0; @_H; @CmM; @Cm0; @AL'; @HC; @HAx; @Hx; @AL; @R0; @A0; @cost; @x; @R; @MA; @A; @s'; @s; @HH|] "#(R#O$1#V#v#T#w#u###$#[#&#%#'#)$##(#{#*#J#I#+#-#H#L#.#/#K#,#2#<#?#f#;#G#O#0#5#7#@#>#D#B#C#l#~#S#1#3#4#8#6#:#=#F#k$&$%$+$,#R#U#a#b#9#A#E#m#n#q#r#t#z$$$($*$.$-$/$)#M#N$2#Z#\#Y#^#]#_#y#x#o#s#|#W#p#X$1#i#}#d#`#c#j#h$'$0#g#e=#s%#t%#u%#v%#w%#x%#y'#z*#{'#|+#}%#~'$#%$$($%&$&%$'$$('$)%$*%$+$$,&$-&$.$$/%$0&VSLS>EUSME.NMKL#JP#PM%$##JK&EM&EP'$#$#K(ER#$#%)#%+#$RM##N$S%P&E#&ES%'$##M#(ES&(ES)'#P5%#(ES*#N#$S&R.S)#S,S%%%#k##(#k##-#k##3#k##>#j##7##JM&EN'@#$#M(ES%#$#%(##JR#RN%$##JN&ER'#?$#N##>%'#&ES,'s#$#$#R##B%/#$S)S%##S&$S*S,&E#&ES*'$##S%#(ES?(ES-'#S,5%#(ES@#S&#$S?S).S-#S4S*%%#k##(#k##-#k##3#k##s###j##7#&ES&'=#$#S%##s#9#JS,&ES)'#9$#S&##8#JS&#4S4$S-S*&E#&ES-'$##S)#(ESA(ES5'#S*5%#WSNS>ES6USOE#JH&EI#J#k##%#k#$C##JI#IH%$#&EL##*k##%#k#%C#k#$C#6EI#J#k##1#k#$C#6EL##'k##.#k#%C#k#$C#&EK$#1$KL&E##%#k##8#k##9#k#&C#k#'C#6EK$#16E+#$#k##@#k##A#k#&C#k#'C#%+#%5#%;#%@#%s#)#(ESB#S-#$SCS@.S6#S5SA%%#j##(#(ES.#SC#$SDS6.S1#SPSB%%#j##/#(ES7#SD#$S8S1.S/#SES.%%#j##6#(ES9#S8#$S:S/.S;#SQS7%%#j##=#(ES'#S:#$SFS;.S2#SRS9%%#j##s#$#$S$SF#J##$S'7SG7#2C#2C%2CSG8C$#8C&#;#S<USSS0<S0$#USTS0/CLUSUC+C$I#USVCUSWCVSXCJ3S=-C#)C%Q#*'GDDF#OUSYD-CS=)C)Q#*+GDDF#OZSH,GDDFM[SI-GDDF$#9C'+)C.Q#*0GDDF#O,1GDDF&+#,2GDDF-,#VSZ3FVS[SJSKVS\HLWS]SJ#SKm$%#WS^CJIXS_HL$#l#(*)#l#)=<#l#*BA#j#+C#j#,C#j#-S3#%s#wK$LK#J#k##%#k##s#{#k#+C#k#,C#k#-S3##S#S$YH#S2S#S.S:l#.-%#m##s#</CK+Cs#1I#:S=-C#)Cs#$Q#*s#1GDDF#O,s#2GDDF#s#,#l#(#B<l#))s#5#l#*s#<s#:#j#+C#j#,C#j#/C#$HI##L$IL##Kk##%#k#+C#k#,C#k#/C#XHS$S2S#S1l#.,$#m##s#S4s#Us#T;#%s#Vs#Um#$#WS4s#YS'#&Es#Z&ES'#$#/CIZSHs#LGDDFK[SIs#MGDDFs#D#,s#NGDDF#s#Hs#El#(#s#>s#8l#)'s#Q#l#*s#Xs#V#j#+C#j#-S3#%s$TIk###s$Pk#+C#k#-S3##S+S#WH#S+S;l#.)%##JS#m#$#VS5S##&ES##J#(ES`#S2#$S+S'.S(#S#S$7s#r7#2C#2C%8C#s#q8C%#;#S<<S0#s#r/CM+Cs#pL#/CN+C#Ks#r/CP+C$N#+C'I#3s#q:#-C#3s#J-C#)C%Q#*s#yGDDF#O:s#N-C#1C)#)Cs#vQ#*s#~GDDF#O1C*&:s#~-C#9C%#)C#Qs$$*s$(GDDF#O)Cs$(Q&*s$*GDDF#O)Cs$$Qs$(*s$,GDDF#O,s$-GDDF%s$'#,s$.GDDF(s$(#,s$/GDDF/s$)#,s$0GDDF5s$*#l#(#s#|s#vl#)>s$3#l#*s#&s$8#j#+C#j#,C#j#/C#j#0C#j#1C#j#2C##PK'NP#I#'PN$#M##K#MPk##s&F#k##%#k##)#k##,#k#+C#k#,C#k#/C#k#0C#k#1C#k#2C#$S(S$&E#&ES(&ES+(ESa^H&%$S##S'LS.S/S7l#.:)#m##s#O#Js#O#s#PS#%$##JS$&Es#S's#X#$#S$(ES(#$#%(##S(S+YH#S$S(S8S9l#.s$Bs$:#m##/XHS+S$S(SEl#.s$,s$$#m##1432&#m##2;s#\S<<S0#s$n+Cs#XMs$k/CR+C#Rs$m+C%L#+Cs$oKs#Z+C$I#-Cs#Y3s#Z-C#3s#O-C#1C%#)C(Sb#*s$uGDDF#O1Cs$ss#Y)C'Q#*s$xGDDF#O1Cs$rs#\9C#s$M)C#Q-*s$|GDDF#O1Cs$vs$z9C#s$Q)C#Q3*s%$GDDF#O,s%%GDDF's${#,s%&GDDF,s$|#,s%'GDDF0s$}#l#(#s$ss$ml#):s%*#l#*As%/#j#+C#j#,C#j#/C#j#0C#j#1C#j#2C#j#3C#5Ks#S'LP#R#'LN$#M##R'KM$#P##Nk##&#k##*#k##-#k#+C#k#,C#k#/C#k#0C#k#1C#k#2C#k#3C#^HS's#Ts#Vs$CS#s#Ws#US1S.S/l#.7$#m##s#J4s#Ps#KS/#4s#Rs#Ks#B#4s$Gs$Es#V#l#4s$Ls$J#l#5s$cs$`#j#6s&'#j#7s&0#V#IHj##s&*#j##s&3#0s&4s&,s%e#Hj#5s&,#j#8s&?#V#IHj##s&/#j##s&B#0s&Cs&1s%q#Hj#5s&1#j#9s&J#V#IHj##s&4#j##s&M#0s&Ns&6s%}#Hj#5s&6#j#:s&T#V#IHj##s&9#j##s&W#0s&Xs&;s&-#Hj#5s&;#j#;s&b#V#IHj##s&>#j##s&e#0s&fs&@s&9#Hl#5s&ms&l#j#<s&o#j#=s&t#j#>s&z#j#?s&|#j#@s&~#j#As''#V#IHj##s'*#j##s'Q#0s'Rs'Fs'0#Hj#5s'K#j#Bs'R#V#IHj##s'W#j##s'}#0s'~s'vs'`#Hj#5s(&#j#CC#j#DC#j#EC#j#FC#j#GC#j#Hs(-#j#Is(.#j#Js(0##"). Qed.

Lemma al_okR_mono : asan_rt_hyps H -> forall s A A' MA R,
  al_okR s A MA R -> A <= A' <= MA -> al_okR s A' MA R.
Proof.
  intros HH s A A' MA R (A0 & R0 & AL) HA. pose proof (ah_costs H HH) as (Cm0 & CmM & _). pose proof (CmM A A' ltac:(lia)). split; [lia| split; [exact R0| lia]].
Qed.

Lemma al_okR_keep : forall s s' A MA R, al_okR s A MA R -> as_AL H s' >= as_AL H s -> al_okR s' A MA R.
Proof. intros s s' A MA R (A0 & R0 & AL) K. split; [exact A0| split; [exact R0| lia]]. Qed.

(* [comment removed for export] *)
Lemma al_okR_rebudget : asan_rt_hyps H -> forall s A MA R MA',
  al_okR s A MA R -> A <= MA' <= MA -> al_okR s A MA' (R + (as_Cm H MA - as_Cm H MA')).
Proof.
  intros HH s A MA R MA' (A0 & R0 & AL) HM. pose proof (ah_costs H HH) as (Cm0 & CmM & _). pose proof (CmM MA' MA ltac:(lia)).
  split; [lia| split; lia].
Qed.
Lemma al_okR_unbudget : forall s A MA R MA',
  al_okR s A MA' (R + (as_Cm H MA - as_Cm H MA')) -> 0 <= R -> A <= MA -> al_okR s A MA R.
Proof. intros s A MA R MA' (A0 & R0 & AL) HR HA. split; [lia| split; [exact HR| lia]]. Qed.

(* [comment removed for export] *)
Section BPUTR.
  Variables MX CX MA R : Z.
Definition bput_postR (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB0 : list block) (LF : list fframe) (P E lo B shi : Z) (pad7 pad2 : list byte) (p0 Rn : Z) (bs : list byte)
    (mb : byte) (d0 : pst) (m0 : mem) (mo0 : Model) : config -> Prop :=
  fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (d : pst) (q : Z) (E' : ecv) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (q - p0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' cf /\ as_MPRES H mo0 (cfg_model cf)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' (ps_LBn d ++ LB0) m'
    /\ rw_cells asegs m' P (ParserCoreCells (ps_c d) pad7 pad2)
    /\ rw_cells asegs m' E (ErrCodeCells E') /\ (E' = EC_clear \/ http_fail E')
    /\ rw_cells asegs m' (P + 240) [C1 (ps_rdi d)] /\ AHttpCat m' (ps_g d) /\ (AFieldTabZero m' \/ FT m')
    /\ PutU P p0 bs mb d m' /\ HdrOwnA (ps_LBn d ++ LB0) m' (ps_h d)
    /\ PutL H sp P E p0 bs LB0 (ps_L d0) (ps_es d0) (ps_h d0) d /\ PutB MX CX MA LB0 p0 Rn d q
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB0 (bv_unsigned sp) (put_X P E (ps_L d0) (ps_es d0) ++ XS) m0 m'
    /\ p0 <= q <= p0 + Z.of_nat (length bs)
    /\ (E' = EC_clear -> p0 < q \/ pc_state (ps_c d) = 11)
    /\ (pc_state (ps_c d) = 11 -> E' = EC_clear)
    /\ HdrDisjP (ps_em d) (ps_h d) /\ BodyDisjP (ps_em d) (ps_h d) (ps_es d)
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ al_okR s' (ps_A d) MA R /\ ps_A d0 <= ps_A d.

Definition bput_stmtR : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB0 : list block) (LF : list fframe) (P E lo B shi : Z) (pad7 pad2 ej : list byte) (p0 Rn : Z) (bs : list byte)
         (mb : byte) (d : pst) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_BP_PUT) fc None m (seg_rom asegs) ->
    a0 = wz P -> a1 = wz p0 -> a2 = wz (Z.of_nat (length bs)) -> a3 = wz E ->
    ps_LBn d = [] -> pc_state (ps_c d) <> 11 ->
    rw_cells asegs m P (ParserCoreCells (ps_c d) pad7 pad2) ->
    rw_cells asegs m E [CB 24 ej] ->
    rw_cells asegs m (P + 240) [C1 (ps_rdi d)] -> AHttpCat m (ps_g d) -> (AFieldTabZero m \/ FT m) ->
    PutU P p0 bs mb d m -> HdrOwnA LB0 m (ps_h d) ->
    PutL H sp P E p0 bs LB0 (ps_L d) (ps_es d) (ps_h d) d -> PutB MX CX MA LB0 p0 Rn d p0 ->
    put_static H MX CX sp tp P E lo B shi p0 Rn bs ->
    as_RHEAP H s LB0 m -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m B ->
    stk asegs m lo (bv_unsigned sp) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
    aobj LB0 LF P PARSER_SIZE -> accessible m P PARSER_SIZE ->
    aobj LB0 LF E 24 -> accessible m E 24 -> shvis m E (E + 24) ->
    aobj LB0 LF p0 (Z.of_nat (length bs)) -> accessible m p0 (Z.of_nat (length bs)) -> shvis m p0 (p0 + Z.of_nat (length bs)) ->
    as_RFS H LF m -> (length LF + 4 < AFS_MAXLIVE)%nat -> (length LF + 1 < AFS7_MAXLIVE)%nat -> ACONST m ->
    stack0 m lo shi ->
    al_okR s (ps_A d) MA R ->
    as_SR H (bput_postR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 LF P E lo B shi pad7 pad2 p0 Rn bs mb d m mo)
      (mkCfg msF mo).
End BPUTR.

(* [comment removed for export] *)
Definition rs_frames (m : mem) (sp : word) (E bs P : Z) (mw1 mw2 : cell) (t2c optc : list cell)
    (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra : word) (fr : list cell) : Prop :=
  rs_frame m sp E bs P mw1 mw2 t2c optc
  /\ rw_cells asegs m (bv_unsigned sp + -104) (rs_sv s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra)
  /\ rw_cells asegs m (bv_unsigned sp) fr /\ Z.of_nat (cells_size fr) = 128.

(* [comment removed for export] *)
Definition rs_core (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell)
    (w : rsw) (s : as_St H) (errv : word) (E : ecv) (tot : Z) (m : mem) (mw1 mw2 : cell) (t2c optc : list cell) (XS : list (Z * Z)) : Prop :=
  RWm H C w s errv E m /\ RWp H C MA w /\ al_okR s (ps_A (w_d w)) MA R
  /\ stk asegs m (c_lo C) (bv_unsigned sp + -208)
  /\ rs_frames m sp (c_E C) (c_bs C) (c_P C) mw1 mw2 t2c optc s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra fr
  /\ Forall (fs_scratch H (c_LF C)) XS
  /\ xpres H (c_LBin C) (c_SP C) (hread_X (c_P C) (c_E C) (c_fb C) (c_stb C) [] [] ++ XS) (c_m0 C) m
  /\ 0 <= tot /\ tot + zlength (w_fds w) + zlength (w_sds w) <= c_N C
  /\ w_nr w <= c_N C - zlength (w_sds w).

(* [comment removed for export] *)
Definition rs_at_put (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw)
    (cf : config) : Prop :=
  exists (t0 t1 t2 a4 a5 a6 a7 s0x s9x t3 t4 t5 t6 : word) (m : mem) (s : as_St H) (errv : word) (E : ecv) (tot : Z)
         (mw1 mw2 : cell) (t2c optc : list cell) (XS : list (Z * Z)),
    as_VIS H s (cfg_ms cf)
      = rs_ms P_A_BP_PUT (Z_to_bv 64 RS_PUTRET) sp (c_gp C) (c_tp C) t0 t1 t2 s0x (c_E C) (wz (c_P C)) (wz (fb_in (w_FB w))) (wz (fb_size (w_FB w))) (wz (c_E C))
              a4 a5 a6 a7 tot (c_fb C) (wz (c_E C + 8)) (wz (c_E C + 16)) s9x t3 t4 t5 t6 (c_F C) (c_fc C) m
    /\ 1 <= fb_size (w_FB w) /\ pc_state (ps_c (w_d w)) <> 11
    /\ as_AKREL H s cf /\ as_MPRES H (c_mo0 C) (cfg_model cf)
    /\ rs_core C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr w s errv E tot m mw1 mw2 t2c optc XS
    /\ wM (c_N C) w <= M0.

(* [comment removed for export] *)
Definition rs_at_doread (C : rsc) (MA R : Z) (sp : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z) (w : rsw)
    (cf : config) : Prop :=
  exists (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0x s9x t3 t4 t5 t6 : word) (m : mem) (s : as_St H) (errv : word) (E : ecv) (tot : Z)
         (mw1 mw2 : cell) (t2c optc : list cell) (XS : list (Z * Z)),
    as_VIS H s (cfg_ms cf)
      = rs_ms RS_DOREAD rax sp (c_gp C) (c_tp C) t0 t1 t2 s0x (c_E C) a0 a1 a2 a3 a4 a5 a6 a7 tot (c_fb C) (wz (c_E C + 8)) (wz (c_E C + 16)) s9x t3 t4 t5 t6
              (c_F C) (c_fc C) m
    /\ pc_state (ps_c (w_d w)) <> 11
    /\ as_AKREL H s cf /\ as_MPRES H (c_mo0 C) (cfg_model cf)
    /\ rs_core C MA R sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra fr w s errv E tot m mw1 mw2 t2c optc XS
    /\ wM (c_N C) w <= M0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pst_call (d : pst) : pst :=
  mkPST (ps_c d) (ps_S d) (ps_L d) (ps_ns d) (ps_ls d) (ps_em d) (ps_h d) (ps_u d) (ps_es d) (ps_insz d) (ps_g d) (ps_rdi d) [] (ps_A d).
Definition pst_ret (d'' : pst) (LBn : list block) (g : bool) : pst :=
  mkPST (ps_c d'') (ps_S d'') (ps_L d'') (ps_ns d'') (ps_ls d'') (ps_em d'') (ps_h d'') (ps_u d'') (ps_es d'') (ps_insz d'') g (ps_rdi d'')
        (ps_LBn d'' ++ LBn) (ps_A d'').

(* [comment removed for export] *)
Definition put_MX (C : rsc) (w : rsw) : Z := c_MX C - (2 * CAPMAX (c_N C) - lb_bytes (w_FBB w)).
Definition put_CX (C : rsc) (w : rsw) : Z := c_CX C - (2 - Z.of_nat (length (w_FBB w))).
Definition put_MA (C : rsc) (MA : Z) (w : rsw) : Z := MA - fb_res (c_N C) (fb_cap (w_FB w)).

(* [comment removed for export] *)
Definition w_after_put (w : rsw) (d'' : pst) (g : bool) (k : Z) : rsw :=
  mkW (pst_ret d'' (ps_LBn (w_d w)) g) (ps_LBn d'' ++ w_PB w) (w_FBB w) (fb_consume (w_FB w) k) (skipn (Z.to_nat k) (w_fds w)) (w_Fs w) (w_sds w) (w_nr w).

Lemma blk_fresh_weaken : forall LB LB' SP SP' A n,
  blk_fresh H LB SP A n -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> blk_fresh H LB' SP' A n.
Proof.
  intros LB LB' SP SP' A n F HS HL a k RR Hk. apply F; [| exact Hk].
  eapply aclient_range_LB_mono; [eapply aclient_range_SP_mono; [exact RR| exact HS]| exact HL].
Qed.

Lemma fbb_ok_facts : forall FB FBB, fbb_ok FB FBB ->
  lb_bytes FBB = fb_cap FB /\ 0 <= Z.of_nat (length FBB) <= 1
  /\ (FB <> FB_empty -> forall LB, (forall b, In b FBB -> In b LB) -> exists pf, In (pf, fb_begin FB, fb_cap FB) LB).
Proof.
  intros FB FBB [[-> ->] | (NE & pf & ->)]; cbn.
  - split; [reflexivity|]. split; [lia|]. intros K; exfalso; exact (K eq_refl).
  - unfold lb_bytes, blk_size. cbn [fold_right snd]. split; [lia|]. split; [change (Z.of_nat 1) with 1; lia|]. intros _ LB HL. exists pf. apply HL. left; reflexivity.
Qed.

Lemma fb_consume_shape : forall FB k, fb_begin (fb_consume FB k) = fb_begin FB /\ fb_end (fb_consume FB k) = fb_end FB
  /\ fb_cap (fb_consume FB k) = fb_cap FB /\ fb_last (fb_consume FB k) = fb_last FB.
Proof. intros FB k. unfold fb_consume, fb_cap. destruct (k <? fb_size FB); cbn; repeat split; reflexivity. Qed.

Lemma fbv_eq_dec : forall a b : fbv, {a = b} + {a <> b}.
Proof. intros a b. decide equality; apply Z.eq_dec. Qed.

Lemma fb_consume_empty : forall FB k, 0 <= k -> (FB <> FB_empty -> 0 < fb_begin FB) -> (fb_consume FB k = FB_empty <-> FB = FB_empty).
Proof.
  intros FB k K0 POS. split.
  - intros E. destruct (fbv_eq_dec FB FB_empty) as [EQ | NE]; [exact EQ|]. exfalso.
    pose proof (POS NE). pose proof (fb_consume_shape FB k) as (B & _). rewrite E in B. cbn in B. lia.
  - intros ->. unfold fb_consume, fb_size, FB_empty. cbn. replace (k <? 0 - 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma fbb_ok_consume : forall FB FBB k, 0 <= k -> (FB <> FB_empty -> 0 < fb_begin FB) -> fbb_ok FB FBB -> fbb_ok (fb_consume FB k) FBB.
Proof.
  intros FB FBB k K0 POS OK. pose proof (fb_consume_shape FB k) as (B & E & CP & _).
  destruct OK as [[-> ->] | (NE & pf & ->)].
  - left. split; [| reflexivity]. apply (proj2 (fb_consume_empty FB_empty k K0 ltac:(intros K; exfalso; exact (K eq_refl)))). reflexivity.
  - right. split; [intros K; apply NE; exact (proj1 (fb_consume_empty FB k K0 POS) K)|]. exists pf. rewrite B, CP. reflexivity.
Qed.

Lemma zlength_skipn : forall {A} (k : nat) (l : list A), (k <= length l)%nat -> zlength (skipn k l) = zlength l - Z.of_nat k.
Proof. intros A k l Hk. unfold zlength. rewrite length_skipn. lia. Qed.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

Lemma fb_res_nonneg : forall N C, 0 <= N < 2^26 -> 0 <= C <= CAPMAX N -> 0 <= fb_res N C.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_read_stmt.CAPMAX); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq); constr:(@kc__2); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.log2); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.EQ); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.Tauto.isBool); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.TT); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.false); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.leb_le); constr:(@Stdlib.micromega.Tauto.FF); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.ZArith.BinInt.Z.leb_gt); constr:(@Stdlib.ZArith.BinInt.Z.le_trans); constr:(@Stdlib.ZArith.BinInt.Z.log2_le_mono); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.log2_pow2); constr:(@Stdlib.ZArith.BinInt.Z.log2_nonneg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_read_stmt.fb_res)|] [|@E0; @b; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__sat4; @__sat2; @__sat1; @__sat3; @E1; @m; @n; @__sat5; @H0; @y; @x; @__p2; @z; @__x3; @L; @HC; @HN; @C; @N|] "#);#8$3#;#m#l#>#n#$#G###v#%#&#{#P$(#'#R#W#8#(#q#,#C#*#)#c#/#4#t#-#5#Z#g#f#z#+$)#2#6#J#E#U#T#a#`#_#d#e#h#i#k#w#x$$$&$'$%#0$*$+$-$0#3$/$2$1$.#.$3#7#1$4#=#K#B#L#I#r#p#N#D#|#A#j#?#<#u#}#\#M#F#O#Y#b#y$,#]#[#V#@#H#Q#S#^#X#s#o$##~H#j%#k%#l$#m%#n&#o'#p*#q%#r$#s&#t$#u+#v%#w%#x%#y&#z&#{%#|%#}$#~%$#$$$*$%&$&&$'%$(&$)%$*%$+%$,&$-%$.%$/%$0)$1$$2&#FH%S(-#+S(%#+#%#-#>(#/H#0,#US:L#H#0/#5LF?IJ5MF'I#J5S%F'I#J%5%#%#%#%#%#%#%#-#%$%#-#+A%#%#-#>s#$#$(#&,#+s#&%#+#-#&#(-:&s#-S)%2%#%#%#%#-#$)#&+#$-#-+$$#$#7$6#$A#-A4S*#*$S*&#<$#)*S*'6#*;#&#A*3&&<#$%#nI#$##C-#%#*##nI#$##CH#%#0###F#k#$s#:#j#%I#5QF'I#O@s#Os#./Fs#P#Fs#0/Fs#0k##$#k##&##Fs#UAs#Vs#5Hj##R#j#&%##Fs#7k##R#k#&(#@s#\s#W#Fs#X/Fs#Xk##$#k##2#As#as#\Hj##R#j#&0##Fs#^k##R#k#&3#VS;Fs#g?S<#m##;UH#UQ$7CS1BCs#m;C#$US=S(VS>C#8S18#8#7C#WS?C'#7C&3C$#3C,#<#S+C0#US@S#=S#$#USAS#VS2CLUSBCXS3C$H#USCCUSDCDCs$(1CF(C$S.#)&EDDS&#KYSE'EDDS&E(EDD$#USFDZS4*EDDGQ1Cs$/DCS(2C$#1Cs#],C$#(C/N#)1EDDG#K92EDDG*#1Cs#y1Cs#wFs#uGC-#,C%#2C'#1Cs#q2C#%1Cs#q2C#/,C%#1Cs#i,C$#,C#,,C+#,C1#(CAN#)s#$EDDG#K.s#%EDDG5>#.s#&EDDG@?#VSGs#'G?IOVSHJL'I#Om$%#WSICFHXSJJL$#l#'*)#l#(s#1s#0#l#)s#6s#5#j#*C#j#+C#j#,S$#5HF'I#O&s$ZH$#s$*#L#0M#&s$^L$#s$.&s$6#$s$8#$#s$-$#s$A$s$@#$s$K##F#k##,#k##1#k#*C#k#+C#k#,S$##FS,YJ#S,SKS)S/l#-9%#l#.s#bs#z#l#/s#ds#o#l#0s#ls#i#l#/s#ts#p#l#1s#ys#v#l#.s$'s#~#&s$uS*$#s$E&s$M#$s$O#$#s$D$#s$X$s$W#$s$b##F#m#,#j#$s$3#'Is$5P4S%s$G'Is$GJ4S5s$I'I#J*s$KS'&#s$c&s%+S/$#s$W&s$_#$s$a#$#s$V$#s$j$)#*S's$T6#*s$h#&#s$n*,&&s$i#$%#nI#$##CH#%#*###F#k#25#j#%I#4S)s$_'I#O4HJ'I#O#LHk##$##HJ4LH'I#Ok##%#0'##MLk##&#j##%#4ML'I#Ok##.#j###Hj##/#VSLHJYS61-)$#j#3C#j#4C#k#3C4k#4C#WJS's$xH#S's$y+s%?+#+#+#+#+#+#+#+#-#BC#8s$N8#7C#;C&#3C#s$O3Cs$X#<#S+Cs$\#=S##s$N1Cs%2(Cs$?N#)s$JEDDG#K(Cs$AS.s$I)s$LEDDS&#KYSMs$MEDDS&Es$NEDD$#(Cs$MNs$E)s$PEDDG#K2Cs$Hs$P,C#s$F(Cs$IN#)s$TEDDG#K9s$UEDDG'#:C0s$L2C#s$B2Cs$?(,Cs$A#,C#s$>,C#s$G,C'#(Cs$[N#)s$^EDDG#K.s$_EDDG,s$X#.s$`EDDG4s$Y#.s$aEDDG9s$Z#l#'#s$=s$7l#(s$es$d#l#)?s$i#j#*C#j#+C##Js%Q'Is$6P#FL&s&2M$#s%^#L#0&#*s%XM&#s%p&s&8Q$#s%d&s%l#$s%n#$#s%c$#s%w$)##F#k##-#k##3#k##5#k#*C#k#+C#YJS0S-S)S,S7l#-:$#l#5s%:s%R#l#1s%<s%G#l#/s%Ds%A#l#1s%Ls%H#l#.s%Qs%N#l#5s%[s%V#l#2s#Us#T#l#6s#Ys#W#j#2s#o#'Is#qP'Is#pP/HLk##$#/JH'Is#oPk##$#0&#/LMk##&#j##%#'Is#nPk##,#j###Hj##-#VSNHJYS6/,($#j#7C#j#8C#k#7C2k#8C#/s&+S'*S/s&,6#>s&hs&@6#@s&js&B#Fs&C/F&k##$#k##s%|#As&os&GHj##R#j#&s%z##F,k##R#k#&s%}#7Cs%b;Cs%g#3C#s%i3Cs%`#<#S+=S##s%]9s%WEDDGs%Os#aZS4s%XEDDGS%Fs&yGCs%Q#(Cs%ZSO#)s%\EDDG#K9s%]EDDG'#:Cs%Ts#tFs&\GCs%W#(C%N#)s%bEDDG#K.s%cEDDG(s%\#.s%dEDDG/s%]#.s%eEDDGs#us%^#l#'#s%As%;l#(s%is%h#l#)4s%m#j#*C#j#+C#j#,S$#j#9S$#5JF'I#P#Hs%60M#/Ms'30S%#*Ms&]##s#2k##%#k##(#k##+#k#*C#k#+C#k#,S$#k#9S$##FS0#FS-[J$#S0S-S,S7SPl#-5&#l#5s&;s#9#l#1s&=s&H#l#/s&Es&B#l#1s&Ms&I#l#.s#9s#6#l#5s#As#=##s#Fs#Dm#$#WSQs#Hs#F##Js')j#:C#(Cs%tNs%t)s&0EDDG#Kl#'#s%hs%bl#(s&5s&3#l#)s&:s&8##s'0s'0l#-$#Jl#1s&Ns&Y#l#/s&Vs&S#l#1s&^s&Z#m##'(Cs&8Ns&#)s&;EDDG#Kl#'#s%ss%ml#(s&@s&>#l#)s&Es&C#l#-#s#VJl#1s&Xs&c#l#/s&`s&]#l#1s&hs&d#m##s#ZVSRs'@#ZSSCs'A9.s#^#YSTs#as#_s'B<##s#bs'C*SUs'2USV#6$#F#+s'X%#%#%#%#%#%#%#%#%#-#BC#;C#s$u3C#s&e3Cs&p#<#S+Cs&r#=S##s&dVS2CMXS3Cs&cH#(Cs&VNs&I)s&aEDDG#KDCs()(C#S.s&a)s&dEDDS&#KEs&eEDD#s$v(Cs&dN&)s&gEDDG#K(C(Ns$t)s&iEDDG#K9s&jEDDG%#:Cs&Ts&a2C#s&W:C-s%':Cs$z#2Cs&V#,C&#(Cs&oN#)s&rEDDG#K.s&sEDDG+s&l#.s&tEDDG1s&m#.s&uEDDG6s&n#l#'#s&Qs&Kl#(:s&x#l#)=s&}#j#*C#j#+C#j#;C#'Is(6P#FQ#Qs$q0$#*s'|M&#s(&*S%s'l*s$p#&s'~#$&##F#k##*#k##.#k##s#^#k#*C#k#+C#k#;C#*S8s'w6#ZJS8SW#S5SXS-l#-7&#l#5s'Ls'd#l#1s'Ns'Y#l#/s'Vs'S#l#1s'^s'Z#l#.s'cs'`#l#5s'ms'h#l#6s#Ps#N#l#<s#Ts#S#l#2s%is$Z#l#6s$^s$\#j#2s$q#XS9s&*s$s#HU#Jl#2s(Ys&B#l#%s&DI#j#$s&F#XS9s'{s&H#HU#Jl#$s(^s(\#l#%s(`I#VSYML#F#m#%#j#=s(e#j#>s(i#j#?C#j#@C##"). Qed.

(* [comment removed for export] *)
Lemma blocks_full_sep : asan_rt_hyps H -> forall s LB m p A n pf B cap k,
  as_RHEAP H s LB m -> In (p, A, n) LB -> In (pf, B, cap) LB -> 0 < k -> (A + k <= B \/ B + cap <= A) ->
  A + n <= B \/ B + cap <= A.
Proof.
  intros HH s LB m p A n pf B cap k RH INa INb Hk SEP.
  destruct (bptr_eq_dec p pf) as [->|NE].
  - pose proof (nodup_blk_eq _ _ _ (ah_nodup H HH _ _ _ RH) INa INb eq_refl) as E. injection E as En EA.
    pose proof (ah_blocks H HH _ _ _ _ RH INa) as (_ & _ & N0 & _). cbn [blk_addr blk_size fst snd] in N0. subst. lia.
  - destruct (ah_disj H HH _ _ _ _ _ RH INa INb ltac:(cbn; exact NE)) as [D|D]; cbn [blk_addr blk_size fst snd] in D; lia.
Qed.

(* [comment removed for export] *)
Lemma RWp_put_pre : asan_rt_hyps H -> forall C MA w (spw : word) s m,
  rs_static H C -> RWp H C MA w ->
  let d := w_d w in let LB0 := ps_LBn d ++ c_LBin C in
  as_RHEAP H s LB0 m -> PutUw (c_P C) (c_mb C) d m ->
  w_FB w <> FB_empty -> fb_begin (w_FB w) <= fb_in (w_FB w) -> fb_out (w_FB w) <= fb_end (w_FB w) -> zlength (w_fds w) = fb_size (w_FB w) ->
  bv_unsigned spw <= c_SP C ->
  PutL H spw (c_P C) (c_E C) (fb_in (w_FB w)) (w_fds w) LB0 (ps_L d) (ps_es d) (ps_h d) (pst_call d)
  /\ PutB (put_MX C w) (put_CX C w) (put_MA C MA w) LB0 (fb_in (w_FB w)) (zlength (w_fds w) + zlength (w_sds w)) (pst_call d) (fb_in (w_FB w))
  /\ put_MX C w <= as_LIVE_MAX H /\ put_CX C w <= as_LIVE_CNT_MAX H.
Proof.
  intros HH C MA w spw s0 m0 STC RP. cbv zeta. intros RH UW NE BI OE SZ SPW.
  destruct C as [bs fb P E ioc N lo B shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m00 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L ns ls em h u es insz g rdi LBn Ag]. unfold pst_call, RWp, rs_static in *. cbn_w_all.
  destruct STC as (AOP & AOE & P8 & E8 & BS8 & FB8 & SEPPE & SEPBF & CEIL & NR & IOC & INS & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL).
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62
                  & AOWN & PERM & FOK & FRL & FRB & FRT & FRM & FRF & DJL & DJB & DJT & DJM & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & A0 & AL).
  destruct (fbb_ok_facts _ _ FOK) as (FBBb & FBBn & FBBin). unfold fb_size, fb_cap in *.
  unfold CAPMAX in *. pose proof SZ as SZ'. unfold zlength in SZ'.
  (* [comment removed for export] *)
  destruct (FBBin NE (LBn ++ LBin)) as [pf INf].
  { intros b Hb. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. exact Hb. }
  unfold PutUw in UW. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in UW. destruct UW as (FC & _ & _ & MB & _). pose proof FC as (_ & _ & _ & _ & _ & _ & _ & DOM & _).
  pose proof MB as (_ & _ & _ & SZE & _).
  split; [| split; [| unfold put_MX, put_CX, CAPMAX; cbn_w; split; [clear - MXL FBBb CPM NR; lia| clear - CXL FBBn; lia]]].
  - unfold PutL. cbn_ps. cbn [app].
    split; [exact PCOK|]. split; [exact OWN|]. split; [exact MOWN|].
    split; [intros e He; left; exact He|]. split; [intros x s IN; left; exact IN|].
    split; [exact OFFP|]. split; [exact OFFE|].
    split. { unfold ps_off. cbn_ps. split; [| split].
             - intros e d' He. destruct (OWN e d' He) as (pe & INe & _). pose proof (esize_ge d') as EG.
               assert (INL : e ∈ L) by (apply (proj2 (DOM e)); rewrite He; eexists; reflexivity).
               destruct (blocks_full_sep HH _ _ _ _ _ _ _ _ _ 48 RH INe INf ltac:(clear; lia) ltac:(destruct (DJL NE e INL); [left| right]; lia)); lia.
             - intros x s IN. destruct (MOWN x s IN) as (px & INx).
               pose proof (proj1 (Forall_forall _ _) SZE _ IN) as SZ0. cbn [snd] in SZ0. pose proof (mb_block_size_range s ltac:(clear - SZ0; lia)) as [BR _].
               destruct (blocks_full_sep HH _ _ _ _ _ _ _ _ _ (24 + s) RH INx INf ltac:(clear - SZ0; lia) ltac:(destruct (DJB NE x s IN); [left| right]; lia)); lia.
             - split; [intros TL; destruct (DJT NE TL); lia| intros ML; destruct (DJM NE ML); lia]. }
    split. { intros e He. destruct (DJL NE e He); lia. }
    split; [exact DFB|]. split; [exact HST|]. split; [exact U01|]. split; [exact CAP|]. split; [exact LES|]. split; [exact INZ|].
    split; [exact LEN1|]. split; [exact HDJ|]. split; [left; reflexivity|]. split; [exact HL8|]. split; [exact SK62|].
    split; [intros b []|]. split; [intros e He; exact He |]. split; [intros x s IN; exact IN|]. exact A0.
  - unfold PutB, put_MX, put_CX, put_MA, CAPMAX in *. cbn_w. cbn_ps. cbn [app length]. rewrite Z.sub_diag, Z.sub_0_r.
    split; [| split; [| split; [exact IZ|]]].
    + clear - BY FBBb FBBn CPM. lia.
    + clear - CN FBBn. lia.
    + unfold fb_cap. clear - AL. lia.
Qed.

(* [comment removed for export] *)
Lemma RWp_put_post : asan_rt_hyps H -> forall C MA w (spw : word) (d'' : pst) (q : Z) (g : bool),
  rs_static H C -> RWp H C MA w ->
  (w_FB w <> FB_empty -> 0 < fb_begin (w_FB w) /\ 0 < fb_cap (w_FB w)) -> fb_begin (w_FB w) <= fb_in (w_FB w) -> fb_out (w_FB w) <= fb_end (w_FB w) ->
  zlength (w_fds w) = fb_size (w_FB w) ->
  bv_unsigned spw <= c_SP C ->
  let d := w_d w in let LB0 := ps_LBn d ++ c_LBin C in let p0 := fb_in (w_FB w) in
  PutL H spw (c_P C) (c_E C) p0 (w_fds w) LB0 (ps_L d) (ps_es d) (ps_h d) d'' ->
  PutB (put_MX C w) (put_CX C w) (put_MA C MA w) LB0 p0 (zlength (w_fds w) + zlength (w_sds w)) d'' q ->
  p0 <= q <= p0 + zlength (w_fds w) ->
  RWp H C MA (w_after_put w d'' g (q - p0)).
Proof.
  intros HH C MA w spw d'' q g' STC RP POS BI OE SZ SPW. cbv zeta. intros L B QR.
  destruct C as [bs fb P E ioc N lo B0 shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m00 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB1 FBB FB fds Fs sds nr]. destruct d as [c S L1 ns ls em h u es insz g rdi LBn Ag].
  destruct d'' as [c2 S2 L2 ns2 ls2 em2 h2 u2 es2 insz2 g2 rdi2 LBn2 A2]. unfold w_after_put, pst_ret, RWp, rs_static in *. cbn_w_all.
  destruct STC as (AOP & AOE & P8 & E8 & BS8 & FB8 & SEPPE & SEPBF & CEIL & NR & IOC & INS & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL).
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62
                  & AOWN & PERM & FOK & FRL & FRB & FRT & FRM & FRF & DJL & DJB & DJT & DJM & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & AG0 & AL).
  destruct L as (PCOK2 & OWN2 & MOWN2 & NEW2 & NEWB2 & OFFP2 & OFFE2 & OFFW2 & WINL2 & DFB2 & HST2 & U012 & CAP2 & LES2 & INZ2 & LEN12 & HDJ2 & HNEW2 & HL82 & SK622
                 & AOWN2 & LS2 & ESS2 & A02).
  destruct B as (B1 & B2 & B3 & B4). unfold PutL, PutB in *. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct (fbb_ok_facts _ _ FOK) as (FBBb & FBBn & FBBin).
  pose proof (fb_consume_shape FB (q - fb_in FB)) as (CB_ & CE & CCP & CL). unfold fb_size, fb_cap in *.
  assert (ZSK : zlength (skipn (Z.to_nat (q - fb_in FB)) fds) = zlength fds - (q - fb_in FB)).
  { rewrite zlength_skipn; [lia|]. unfold zlength in SZ, QR. lia. }
  assert (SUB : forall b, In b LBin -> In b (LBn ++ LBin)) by (intros b Hb; apply in_or_app; right; exact Hb).
  assert (FW : forall A0 n0, (forall a k, aclient_range H (LBn ++ LBin) (bv_unsigned spw) a k -> 0 < k -> a + k <= A0 \/ A0 + n0 <= a) -> blk_fresh H LBin SP A0 n0).
  { intros A0 n0 F0. eapply blk_fresh_weaken; [exact F0 | exact SPW | exact SUB]. }
  (* [comment removed for export] *)
  assert (FBLK : FB <> FB_empty -> forall A0 n0, (forall a k, aclient_range H (LBn ++ LBin) (bv_unsigned spw) a k -> 0 < k -> a + k <= A0 \/ A0 + n0 <= a) ->
                 fb_end FB <= A0 \/ A0 + n0 <= fb_begin FB).
  { intros NE A0 n0 F0.
    destruct (FBBin NE (LBn ++ LBin)) as [pf INf].
    { intros b Hb. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. exact Hb. }
    destruct (F0 (fb_begin FB) (fb_end FB - fb_begin FB) ltac:(right; right; left; exists (pf, fb_begin FB, fb_end FB - fb_begin FB); split; [exact INf | cbn; lia])
                 ltac:(exact (proj2 (POS NE)))); lia. }
  rewrite <- !app_assoc.
  split; [exact PCOK2|]. split; [exact OWN2|]. split; [exact MOWN2|]. split; [exact DFB2|].
  split; [exact HST2|]. split; [exact U012|]. split; [exact CAP2|]. split; [exact LES2|]. split; [exact INZ2|]. split; [exact LEN12|]. split; [exact HDJ2|].
  split; [exact HL82|]. split; [exact SK622|].
  split.
  { (* [comment removed for export] *)
    intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [exact (AOWN2 b Hb)|].
    destruct (AOWN b Hb) as [[K1 K2] | [K | [K | K]]].
    - left. split; [apply LS2; exact K1 | exact K2].
    - right; left. destruct HNEW2 as [-> | [HE _]]; [exact K|]. exfalso. destruct K as [K _]. destruct HE as (_ & ML & _). lia.
    - right; right; left. destruct HNEW2 as [-> | [HE _]]; [exact K|]. exfalso. destruct K as [K _]. destruct HE as (_ & _ & _ & TL & _). lia.
    - right; right; right. destruct K as [s0 [IN EQ]]. exists s0. split; [apply ESS2; exact IN | exact EQ]. }
  split. { apply Permutation_app_head. exact PERM. }
  split. { apply fbb_ok_consume; [lia | intros NE; exact (proj1 (POS NE)) | exact FOK]. }
  split. { intros e He. destruct (NEW2 e He) as [old | fresh]; [exact (FRL e old) | exact (FW _ _ fresh)]. }
  split. { intros x s0 IN. destruct (NEWB2 x s0 IN) as [old | fresh]; [exact (FRB x s0 old) |].
           apply FW. intros a k RR Hk. destruct (fresh a k RR Hk); [left| right]; lia. }
  split. { intros TL. destruct HNEW2 as [-> | (HE & FT2 & FM2)]; [exact (FRT TL) | exact (FW _ _ (FT2 TL))]. }
  split. { intros ML. destruct HNEW2 as [-> | (HE & FT2 & FM2)]; [exact (FRM ML) | exact (FW _ _ (FM2 ML))]. }
  assert (POS1 : FB <> FB_empty -> 0 < fb_begin FB) by (intros NE; exact (proj1 (POS NE))).
  split. { rewrite CCP, CB_. intros NE. apply FRF. intros K. apply NE. apply (proj2 (fb_consume_empty FB (q - fb_in FB) ltac:(lia) POS1)). exact K. }
  assert (NE' : fb_consume FB (q - fb_in FB) <> FB_empty -> FB <> FB_empty).
  { intros NE K. apply NE. apply (proj2 (fb_consume_empty FB (q - fb_in FB) ltac:(lia) POS1)). exact K. }
  rewrite CB_, CE.
  split. { intros NE e He. destruct (NEW2 e He) as [old | fresh]; [exact (DJL (NE' NE) e old) | destruct (FBLK (NE' NE) _ _ fresh); lia]. }
  split. { intros NE x s0 IN. destruct (NEWB2 x s0 IN) as [old | fresh]; [exact (DJB (NE' NE) x s0 old) |].
           destruct (FBLK (NE' NE) x (24 + s0) ltac:(intros a k RR Hk; destruct (fresh a k RR Hk); [left| right]; lia)); lia. }
  split. { intros NE TL. destruct HNEW2 as [-> | (HE & FT2 & FM2)]; [exact (DJT (NE' NE) TL) | destruct (FBLK (NE' NE) _ _ (FT2 TL)); lia]. }
  split. { intros NE ML. destruct HNEW2 as [-> | (HE & FT2 & FM2)]; [exact (DJM (NE' NE) ML) | destruct (FBLK (NE' NE) _ _ (FM2 ML)); lia]. }
  split; [exact OFFP2|]. split; [exact OFFE2|].
  split; [exact STRM|].
  rewrite ZSK, ?CCP.
  split; [clear - SZS QR; lia|]. split; [exact NRK|]. split; [exact CPM|].
  unfold put_MX, put_CX, put_MA, CAPMAX in *. cbn_w_all. rewrite <- ?app_assoc in B1, B2.
  set (s34 := if pc_state c2 <=? 9 then 34 else 0) in *. set (s8 := if pc_state c2 <=? 1 then 8 else 0) in *. set (s2 := if pc_state c2 <=? 9 then 2 else 0) in *.
  split; [clear - B1 QR SZ; replace (zlength fds - (q - fb_in FB) + zlength sds) with (zlength fds + zlength sds - (q - fb_in FB)) by lia; lia|].
  split; [clear - B2; lia|].
  split; [clear - B3 QR SZ; lia|].
  split; [exact A02|].
  unfold fb_cap in *. clear - B4 QR SZ. replace (zlength fds - (q - fb_in FB) + zlength sds) with (zlength fds + zlength sds - (q - fb_in FB)) by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fb_res_step : forall N C sz, 0 <= N < 2^26 -> 0 <= sz <= C -> sz <= N -> C <= CAPMAX N -> C - sz < 512 ->
  let C' := Z.max (2 * sz) (sz + 512) in
  (if C =? 0 then C' else C' + C + AWILDB) + fb_res N C' <= fb_res N C /\ C' <= CAPMAX N /\ C < C' /\ 0 < C'.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_read_stmt.CAPMAX); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface8.AWILDB); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_read_stmt.fb_res); constr:(@Stdlib.ZArith.BinInt.Z.eqb_spec); constr:(@Corelib.Init.Datatypes.reflect); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_read_stmt.FBU); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_read_stmt.PHI2MAX); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_read_stmt.fb_res2); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Corelib.Init.Datatypes.false); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.eqb_neq); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.BinInt.Z.leb_spec); constr:(@Corelib.Init.Datatypes.BoolSpec); constr:(@Stdlib.ZArith.BinInt.Z.mul_le_mono_nonneg_r); constr:(@Stdlib.ZArith.BinInt.Z.log2_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.log2); constr:(@Stdlib.micromega.Tauto.TT); constr:(@Stdlib.micromega.RingMicromega.PsatzSquare); constr:(@Stdlib.micromega.EnvRing.Pinj); constr:(@Stdlib.micromega.EnvRing.PX); constr:(@Stdlib.ZArith.BinInt.Z.leb_gt); constr:(@Stdlib.ZArith.BinInt.Z.succ); constr:(@Stdlib.ZArith.BinInt.Z.log2_le_mono); constr:(@Stdlib.ZArith.BinInt.Z.log2_double)|] [|@Ha; @__ff; @__varmap; @__wit; @__arith; @__sat4; @__sat2; @__sat1; @__sat3; @z0; @H0; @heq_C'; @__x1; @__x2; @__x3; @__p1; @z1; @H1; @__p2; @__p3; @__p4; @C'; @C'R; @HG; @HC; @HS; @C; @E'; @C0; @y; @x; @b; @__x4; @__x5; @K; @C'S; @__x6; @__x7; @__sat5; @z3; @H3; @K2; @L0; @b0; @CS; @z; @__x8; @L; @r; @e; @n; @W0; @HSN; @HN; @sz; @N|] "#<_#E$R#H#h#i#g#o#E###K#$#%#'#r#l#*#(#&#)#+#a$-#.$:#1#v#,#-$%#0#6#3#8$2#/#:#2#7#9$A#5#4#<#=#A#>#P#@#;#B#?#\$H#C#s$E#M#[#]#n#m#}$$$9$>$B$D$@$G$I$N$M#D$Q#_#^#`#b#c#d#f#p#t#u#q$0$8$C$J$L$O$P$R$S#V#J#I#U#X#j#e#z$(#L#S$4$*#O$&$.#x$/#N#Q#y#T#Z#{$K#|$=#W$1$5#Y$<#k$+#R#~$,$)$6$;$'#w$3$#$7$?$FU$#%$$%$%%$&%$'&$('$)*$*&$++$,%$-%$.&$/*$0$$1'$2&$3&$4&$5$$6$$7%$8%$9%$:%$;$$<$$=%$>%$?&$@%$A%$B%$C%$D)$E$$F&$G%$H*$I%$J$$K%$L'$M%$N%$O%#)%$P$#)'$Q)#))$JL0S?5#6S?0#6#0#5#VSI(#,L#%,#$JK$KL%$#$LMEQ$M#-QM030#0#0#0#0#0#0#5#,,#&<Q#Q%8$#&?S##S#(8$#>C#'CI$m#$#&s#%P#P.A$#,%$8&%'C#&%%#$()'C&*%$#9&#&s#0S$#S$98$#6s#40#0#5#VSJs#7#,Js#8$J%VSIs#:&,J#k##%#k##'#$Js#>WSKs#?+Kj##SD#j#$%#$J*k##SD#k#$(#VSJs#Es#@$Js#A,Js#Ak##$#k##3#WSKs#Js#EKj##SD#j#$0#$Js#Gk##SD#k#$3#VS[Js#P>S\#m##<UK#UM$US]S%US^S%US_CUS`CUSaCCCJCCs#[USLs#)WSMC$#(C&O#)(FDDE#GVSb)E>NSGVScIL'N#SGm$%#WSdCJKXSeIL$#l#%*)#l#&32#l#'65#l#(#s#*Il#)9s#1#l#*;s#&#l#+s##@#l#*s#+s#'#l#,s#0s#-#l#)s#;s#5#l#-s#AC#l#.s#Ms#E#l#/s#Qs#R#m##s#4$JS*m#$#,S$s#P$s#`s#Q&s#yS+##s#b$s#T##s#Ns#d$s#V#%%#%)#<SN<#<#:C#USOS?NC#:C'FC$#:C*:CSN*C$#*C&#*C+#7#S-7%S-3S%#s#<3S%%#KCR1C#Ls#=1C#Ks#>Ds#=FDDEQGCs$:GCs$*CCs$#2C$#(C&S&#)s#CFDDE#G/s#DFDDE)#4Cs#C((C'O#)s#GFDDE#G(C,S&%)s#IFDDE#G/s#JFDDE%#Hs#KFDDE)#USfDGCS??C#1(C#S21)s#PFDDE#G(C&S25)s#RFDDE#G+s#SFDDE%)#+s#TFDDE+*#l#%#s#Ns#Hl#&<s#W#l#'@s#Z#j#0C#j#1C#j#2C#j#3H##Ls$?'CK#%R#&s$ZL$&#'CK$%$#9'#-KR,#s$H,LRk##$#k##'#k#0C#k#1C#k#2C#k#3H#&s$hS.#S.s$Q,$#T#S.MS)QS$l#(8'#l#,s#xs$'#l#*s$$s#}#l#,s$,s$(#l#4s$@C#l#5s$Ls$D#m##s#Y*Cs#Js#H<s#P:C#*Cs#K#7#S-M'#3S%#s#HKCL1Cs$&K#Ds$%FDDEMGCs$|2C#s#E(Cs#9S&#)s$)FDDE#G/s$*FDDE'#4Cs$)'(C'O#)s$-FDDE#G(Cs#?S&%)s$/FDDE#G/s$0FDDE%#Hs$1FDDE)#(Cs$1O.)s$3FDDE#G/s$4FDDE#s#U(Cs#SOs#F)s$6FDDE#G+s$7FDDE%s#I#+s$8FDDE)s#J#l#%#s$2s$,l#&8s$;#l#';s$>#j#0C#j#1C#j#3H#j#6H##Ks%#'CI#%L#&s%>K$&#'CI$%$#9'#%s%EM$s%,Lk##$#k##&#k#0C#k#1C#k#3H#k#6H#$S.S)T#s#@S.MQS'l#(5%#l#,s$Ys$d#l#*s$as$^#l#,s$is$e#l#4s$}C#l#5s%-s%%#m##s$9*Cs$/s$)*Cs$*s$07#S-M%#*Cs$0s$,*Cs$4#7#S-3S%#s$d3S%'#1Cs#AKs$*/s$cFDDEs$(s#<Ds$dFDDES#/s$eFDDE#s#8Hs$fFDDE%#(Cs#COs$+)s$hFDDE#G(Cs$hOs$-)s$jFDDE#GDs$kFDDEP/s$lFDDE$#4Cs$ks$12C#s$0(Cs$$O#)s$pFDDE#G+s$qFDDE's$'#+s$rFDDE,s$(#+s$sFDDE/s$)#l#%#s$ms$gl#&5s$v#l#'7s$y#j#0C#j#1C#j#2C#j#3H#j#6H#j#7H#'CIs$#%R#'CIs#~%M#9%#$RL$JR%#P&s&$M##s%i$R#k##&#k##)#k##+#k#0C#k#1C#k#2C#k#3H#k#6H#k#7H#,S5s&*$s$&s$']I$#s$&S.S5MQS,S3l#(:&#l#,s%?s%J#l#*s%Gs%D#l#,s%Os%K#l#4s%cC#l#5s%os%g#m##s$x*Cs$ks$n7#S-Ms#F#@Cs&=.C#s$p*C#s$p*Cs$t#*Cs$x#7#S-3S%#s%L3S%*#(Cs$[S&s$g)s%KFDDE#G/s%LFDDEs$m#(Cs$^S&s$f)s%NFDDE#G/s%OFDDEs#I#Hs%PFDDE&#(Cs%POs$p)s%RFDDE#G(Cs$rOs$s)s%TFDDE#G/s%UFDDE%#+s%VFDDE#s$hs#D+s%WFDDE)s$i#l#%#s%Qs%Kl#&s${s%Z#l#'3s%]#j#0C#j#1C#j#2C#j#3H#j#6H#%s#;s#<&s&\R##s&E$L#k##&#k##s#B#k#0C#k#1C#k#2C#k#3H#k#6H#[Is#7s$ZS.S)MQS'l#(/$#l#,s%ss%~#l#*s%{s%x#l#,s&'s&##l#4s&;C#l#5s&Gs&?#m##s%NLs%Qs%Os#7#m##s%OLs%Vs%Ps#{#m##s%PLs%Ys%Qs$^#%s%Zs%Rm#$#,S$K$s&^K$Ks%[$Ks%Z%$#%&#%(#IS+J#LS+##S*nN#$##C%#%#L##OS,L#$#OS,S+$$#ES,$L#,S+L,JL%$#%&#VSgS+J'CS+JVSP#2IS,J'CS'J#S#S.##S*nN#$##CK#%#S###IS#J&s&{S(JS)#$##s&~#0s'$5#BS##-$S#&#S(##*-S#'=S)#nN#$##C(#%#%##nN#$##C0#%#,###2#BS.,--S.&#S(##3-S.0=S)#nN#$##C(#%#%##nN#$##CK#%#5##$+#'CS3J&s'PS3#S3s'9A$#,%$8&%'C#&%%#$()'C&*%$#9&#8s%Qs%P<s%F<#:C#.Cs$$#:C&FCs&:#.Cs$'s%K*C#s&;*C%#*C(#7#S-*Cs%Ps&;*C*#7#S-3S%#s&s3S%'#1Cs&9Rs&s1C#Ks%QHs&sFDDEs$ns%E(Cs&7S&s&s)s&uFDDE#G2Cs&3s&8(Cs&,O#)s&xFDDE#G/s&yFDDEs$l#/s&zFDDEs%F#/s&{FDDEs$u#Ds&|FDDES$(Cs%YOs&@)s&~FDDE#G/s'#FDDE%#(Cs&5S&s&B)s'%FDDE#G+s'&FDDE%s&8#+s''FDDE*s&9#+s'(FDDE1s&:#+s')FDDE4s&;#l#%#s'#s&yl#&7s',#l#':s'/#j#0C#j#1C#j#2C#j#3H#j#6H#j#7H#j#8H#%Rs%Q9#s%M'CRJ$Ls$k%P#%s%N#%S##$MQ%S+#'CMs'|k##$#k##'#k##,#k##.#k#0C#k#1C#k#2C#k#3H#k#6H#k#7H#k#8H#$JS9&s(ES6##s(.$M#,S/M&s(IS9#S9s(2,$#_I*'&#S/S9MQS#S,S0l#(A,#l#,s'Ys'd#l#*s'as'^#l#,s'is'e#l#4s#TC#l#5s#^s#V#'Cs#]s(;m#$#'CS#s(=IIJJS0#s$###s(A#BIs#|-s#}I&#S(##(-Is$$=S0#nN#$##C(#%#%##nN#$##C-#%#*###I#$#,j#9C#$JS)$S)I%$#ES:$K#-LS0,#s(S,RS'$s(US'&s(nS/##s(W$S'#$S's$r%$#%(#%*#Is(]JJS6#s$B##s(`#Bs(as$?-s$@s(b&#S(##(-s(es$C=S6#nN#$##C(#%#%##nN#$##C-#%#*###s(i#$#,k#:1#k#;;#k#<>#k#=A#j#>C#$JS.$S.J%$#ES0$J#-JS5,#s(v,JS,$s(xS,#s#Js(y$S,#&s)7J##s(|$S,#%&#%)#%+#&s)=S:#S:s)&8$#>C#'CS'$m#$#As#Xs#W8s#Ys#X'C#s#Y%s#Y#$s#[s#\'C&s#]%$#9&##S/s)38s#<#1Cs'1Ks(TCCs$p?C#s'r0s$s5#CC#2C#s'i4C'#2C#s'z2Cs'y#4Cs'z&2C#s'}2Cs'|#(C&O#)s(`FDDE#Gl#%#s(Zs(Tl#&2s(c#l#'s(gs(f#j#0C#j#1C##2I&s#F###K#s)L#&s)M&##K#s)O#$&#k#0C#k#1C#JS<P#S*l#(/%#l#,s(ys)(#l#*s)%s(~#l#,s)-s))#l#4s#'C#l#5s#1s#*#l#/s#3s#4##s#%S*&s#Y#JS/#$##s)`#&s)a'##&#s)c#$&#m#,##s#a*#s)g##s%K,#s)i#$%#m#(#=S/s#enN#$##CSG#%#)###s)n#$#(m#'#nN#$##Cs#n#%#-#'nN#$##Cs#s#%#+###s)s#$#-m#'#j#:s#T#j#;s#_#j#<s#b#j#=s#e#^SQCJs#i#S)KS'S+S$QZSQCs){s$1#PIl#?s$Bs$A#j#@s%H#U#IQs%JIKI'N#S8'CLKQ#k##%#'CKIQ#ILK'N#S8k##%#%(#IRL'N#S8k##,#j##&#j##$Ij##.#VShKIYSR0+&$#j#AC#j#BC#k#AC.k#BC#>Cs%V'CPs%Wm#$#&s*VS)#S)s*?A$#,%$8&%'C#&%%#$()'C&*%$#9&#&s*aS5#S5s*J8$#KCKDs)jFDDER/s)kFDDEs(7s(H/s)lFDDE$#(Cs(~S&s)l)s)nFDDE#GZSSs)oFDDE#+s)pFDDE&s)&#l#%#s)js)dl#&+s)s#l#'s)ws)v#j#0C#j#3H#j#6H#$s*ZI%#L%K#'CKJk###SHk##%#k#0C#k#3H#k#6H#&s*{S7##s*d$S)#&s*~S1##s*g$S)#%&#,S1S)R$#S)S3l#(5,#l#,s*4s*?#l#*s*<s*9#l#,s*Ds*@#l#4s#'C#l#5s#3s#+#l#/s#7s#8#'CPJQ#m#%#WIPJ#l#.s#As#?#XSTNs&\S8#'NS8s&]#S$S5##S*BS$s&Z-s&[S$&#S(##s%B-S$s&^=S0#nN#$##C(#%#%##nN#$##CI#%#s%D###+#BS5s&c-s&dS5&#S(##s%K-S5s&g=S0#nN#$##C(#%#%##$*#j#CN#VSUS)s&l$S)s&m,s&nS)BS)s&oWSE%$#$S0s&q,s&rS0#S'S9##S*BS's&u-s&vS'&#S(##s$>-S's&y=S/#nN#$##C(#%#%###*#-s&}S9&#S(##s$E-S9s'$=S/#nN#$##CK#%#%##$)#$S:s'(VSUS's')$S's'*,s'+S'WSE$#5BS3s'-$S.s'.,s'/S.#S5S7##S*JS4#s#,#=S4s#+nN#$##CK#%#$###'#-s'7S7&#S(##)$&#5S?-S5S7#S1s+_8s#X#>C#'CS5$m#$##S7s+dAs#`#,s#a$8s#b%'C#&%%#$(s#e'C&s#f%$#9&#&s,*S4#S4s+o8$#(Cs+1Os*C)s+3FDDE#G(Cs+3Os%:)s+5FDDE#G+s+6FDDE%s*H#l#%#s+0s+*l#&s$-s+9#l#'s+=s+<#j#0C#$JI#s%DK$J#k##%#k#0C#PS*S1l#()$#l#,s+Hs+S#l#*s+Ps+M#l#,s+Xs+T#l#46C#l#5B:#l#/s#%s#&#$Js%-m#$#$JS(m#$#(Cs*lS2s*])s+MFDDE#G/s+NFDDE#s*+CCs#3?Cs*as*p(C$O#)s+RFDDE#G+s+SFDDE's*e#l#%#s+Ms+Gl#&s%as+V#l#'s+Zs+Y#j#0C#j#1C#j#3H#,KI%#L-KL$s#A#k##%#k#0C#k#1C#k#3H#$s,ES7&s,^S=##s,G$S7#&s,aS@##s,J$S7#%&#%*#R#S@S7S6l#(5-#l#,s+ss+~#l#*s+{s+x#l#,s,'s,##l#4s#AC#l#5s#Ms#E#l#/s#Ps#Q#$s#Ws#Vm#$#m##$YSVs#Zs#YS(s#-#&s#[S(&s#[S($$#>Cs#T'CS0s#Um#$#As#Ps#O,s#Qs#P'Cs#Ps#Q%$#$s#Ss#T'Cs#Ss#U%$#9&#&s-$SA#SAs,i8$#.Cs)Hs+[*C#s+X*Cs+`#7#S-3S%#s,4KCQ1C#Ms,41C#Ls,51C#Ks+XGCs,{(Cs+GS&#)s,7FDDE#G2Cs&?s*p4Cs#H#4Cs#H$(C$O#)s,<FDDE#G(Cs+NOs&H)s,>FDDE#G/s,?FDDEs#Ps*22Cs+Qs+`2C#s*y?Cs&Ms+S4C#-2C#s+c2C&#?Cs&Qs+f4C#12C#s+g(C&O#)s,JFDDE#G+s,KFDDE.s+]#+s,LFDDE0s+^#+s,MFDDE3s+_#+s,NFDDE9s+`#l#%#s,Hs,Bl#&>s,Q#l#'s##s,T#j#0C#j#1C#j#2C#j#DC#j#EC#j#3H#'CIM#s&aR&s$>#&s#]$$$#$Ls(z,MR%#S$#MQ##S#-s)#M#s&kS#&$###P#'#-s)(Q&#'##P$&#k##.#k##1#k##3#k##8#k#0C#k#1C#k#2C#k#DC#k#EC#k#3H#$s-XS4&s-qSB##s-Z$S4#$S4s#s%$#%(#JSB^I$M#S*S=S4S#PS$S1l#(s#),#l#,s-)s-4#l#*s-1s-.#l#,s-9s-5#l#4s#YC#l#5s#ds#]#l#/s#fs#g##S0S4##S*-s)HS0&#s&mJSA#$##'#-s)MS4&#s&r##'$&#m#.#&,S(##+#/#&*S(##.$%#m#)#l#Fs$$s#}#j#Gs%K#U#IUSis%S;s%T$J#<s)><#<#<#<#<#:C#:C(.Cs,|#.C%#.C&s,x@Cs'U.C'(.C$#*C&#*C(#7#S-:C/.C#,.C$s-%.C/%.C,#*C%#*C'#7#S-3S%#s-_3S%$#3S%-#3S%.#KCP1C#Ms-b1C#Ls-cKCS#1Cs$4R#1C%K#(Cs-dOs-c)s-fFDDE#GYSjs-gFDDEUSLs._WSMCs-g#(Cs-iO#)s-kFDDE#G+s-lFDDE's,~#+s-mFDDE)s-##(Cs-+S2s-/)s-oFDDE#G(Cs$=S&s-1)s-qFDDE#G/s-rFDDE%#Ds-sFDDES+(Cs$AS&s-1)s-uFDDE#G/s-vFDDE%#Hs-wFDDE'#6s.rGC#(C#S&s$G)s-{FDDE#G(Cs(+S2%)s-}FDDE#GGCs.H(C#S&s-~)s.$FDDE#GZSSs.%FDDE#Ds.&FDDES,Ds.'FDDES'2Cs,[s-F(C.O#)s.*FDDE#G4Cs.)+2C#s-J(C2O#)s..FDDE#G/s./FDDE'#/s.0FDDE+#/s.1FDDE-#(Cs-QOs,j)s.3FDDE#GDs.4FDDES3(Cs,mS2s#*)s.6FDDE#G/s.7FDDE%#2Cs(?s-X4Cs-J#(Cs.9O#)s.;FDDE#G+s.<FDDE's-N#+s.=FDDE,s-O#+s.>FDDEs,2s-P#+s.?FDDE0s-Q#+s.@FDDE=s-R#+s.AFDDEBs-S#+s.BFDDEs%ms-T#+s.CFDDEs#&s-U#+s.DFDDEs#+s-V#+s.EFDDEs#6s-W#l#%#s.?s.9l#&s#As.H#l#'s#Hs.K#j#0C#j#1C#j#2C#j#DC#j#EC#j#HC#j#IC#j#3H#j#6H#j#7H#j#8H#k##s.os._#Ms/8,s,/#'CP$%$#'CPs,2%S$#9%#'CPS$,s*zS+k##s+,SH$S's.<&s/[S,##s/D$S'#%&#%S5#%S)#$JS$$S'S,,S's/]%S/##s(rS'&S,#$J#k##&#k##)#k##+#k##-#k##5#k##7#k##s,N#k##:#k##<#k##s#$#k#0C#k#1C#k#2C#k#DC#k#EC#k#HC#k#IC#k#3H#k#6H#k#7H#k#8H#$JSB,S=S4#S@s/g$#s%}-S4s+G;#i#8I(s$q'%MS4S=S@SBS*#LQS#PS$S:S1S7S<SCl#(s#8*#l#,s/4s/?#l#*s/<s/9#l#,s/Ds/@#l#4s%dC#l#5s%os%h#l#/s%qs%r#-S0s+Q;#&#S($J#m#'#>Cs&f'CS:s&gm#$#As%qs%p,s%rs%q'Cs%qs%r%$#$s%ts%u'Cs%ts%v%$#9&#&s0?S;#S;s0(8$#<s$^<#:C#.Cs$_s..*C#s./.C%#.C&s$b.Cs$_#.C(s.{@Cs+m.Cs.5*.C$#*C&#*C(#*C+#7#S-0s)`0#0#0#0#0#0#0#0#0#0#0#0#5#@C#FCs/:s$|FCs/;s$r*C#s+c*C%#.C##.C(#5,@C#NCs'RNCJXSkC$S?#WSWCs0k#VSXC#:Cs%0*Cs%##*Cs%/#.C&#.C,#:Cs#3.C)#.C/#0:5#@C#WSWCs0z0VSXC#.C#-.C&#.C%,.C(#6s#*6#6#6#6#6#6#6#0#5#@C#.Cs#H<.C$#6s$w6#6#6#6#6#5#@C#.Cs#Rs/o.C$#0B5#@C#.Cs#(s/o.C$#*C(#*C3#*CA#*Cs#$#*Cs#,#*Cs#0#*Cs#=#7#S-.Cs/xs/y.C.#FCs/~s#4*Cs#Gs,J*C$#.C#s/~.Cs#3#6s195#@C#.Cs#ks0'.C$#:Cs%r.C#s,R*C#s,S.Cs#F#.C=#0@0#0#0#0#0#0#0#0#0#5#@C#.Cs#T;.C$#*Cs&%s&$*Cs#R#.Cs#X#.C(#*C'#*C6#*C<#*Cs#7#*Cs$&#*Cs#$#*Cs#*#7#S-Ms#`#.Cs#^s$/.Cs#_s&2.Cs&/#.Cs#as0K.Cs/`s#b.Cs$/#*C%#*C'#*C*#7#S-3S%#s1*3S%.#3S%s#;#3S%s$1#KCM1C#Ls'X1Cs&(S#s1.1C#Rs1/1C%K#6s1vGC#(C#S&s0N)s12FDDE#G/s13FDDEs%~#(C&S&s0M)s15FDDE#G/s16FDDEs,t#Hs17FDDE&#GCs21(C#S&+)s1:FDDE#G(Cs+FS2%)s1<FDDE#G(Cs0[O')s1>FDDE#G(C)Os%u)s1@FDDE#G4Cs1?s0R2C#s0`(C-O#)s1DFDDE#G/s1EFDDE'#/s1FFDDE*#/s1GFDDEs&2#(Cs0gOs0Y)s1IFDDE#G/s1JFDDEs&&#/s1KFDDEs&&s%s4Cs'hs%r(Cs1LO#)s1NFDDE#G+s1OFDDE&s0a#+s1PFDDE(s0b#+s1QFDDEs%|s0c#+s1RFDDEs/Fs0d#+s1SFDDE.s0e#+s1TFDDEs*Cs0f#+s1UFDDEs'us0g#+s1VFDDE<s0h#+s1WFDDE?s0i#+s1XFDDEs##s0j#+s1YFDDEs&Js0k#l#%#s1Ss1Ml#&s#/s1\#l#'s#5s1_#j#0C#j#1C#j#2C#j#DC#j#EC#j#HC#j#3H#j#6H#j#7H#j#8H#'CS#s%p%s%p#'CS#s/B%P#9%#'CS#P,s..P$Ms./'CQJk###SH$S,s1N#s2Ps2U$S,#%%#%s,>#%S.#$S3S+%S:#,S3s2n%S/##s,'S3&s*%#$J#k##&#k##)#k##s%w#k##s%y#k##.#k##5#k##8#k##:#k##<#k##>#k##s&6#k#0C#k#1C#k#2C#k#DC#k#EC#k#HC#k#3H#k#6H#k#7H#k#8H#$JSF$JS=,SBSA#S=s2y$#s)6i#8I'&%#MSAS=SFS*SBLQS#S+S.S9S7S4S>SCS@l#(s#5)#l#,s2Ds2O#l#*s2Ls2I#l#,s2Ts2P#l#4s%YC#l#5s%ds%]#l#/s%fs%g#-s.aSA&#S($J#m#&#>Cs({'CS9s(|m#$#As%es%d,s%fs%e'Cs%es%f%$#$s%hs%i'Cs%hs%j%$#9&#&s3NS<#S<s378$#5s3P@C#.C#s2.*Cs2,s2)*C$#*Cs1?#*Cs.U#7#S-3S%#s2b1Cs'[Ms2a1C#Ls2b1Cs)2Rs2c1C$K#(Cs2bOs(z)s2dFDDE#G4Cs2(s)/(Cs2eO#)s2gFDDE#G(Cs,sS2s1y)s2iFDDE#G(Cs2.Os,u)s2kFDDE#G/s2lFDDEs)}s.N0s'S6#5#CC#?C#s244C#s)<5s3^CC#?Cs2*s-$?Cs'V#4C%#2C(#2Cs):#4C,s)D4C)s'[2C$#5s&(CC#2C%#2C#s1\2Cs)<#(C+O#)s3'FDDE#G+s3(FDDE:s2:#+s3)FDDE<s2;#+s3*FDDE?s2<#+s3+FDDEBs2=#+s3,FDDEs#&s2>#+s3-FDDEs)Ts2?#l#%#s3's2}l#&s#+s30#l#'s#0s33#j#0C#j#1C#j#2C#j#DC#j#EC#j#HC#j#3H#'CIQ-s/VL&#s)?$J##s-DM&Q#$J#,s/\R$Qs/],S#Q%#S'#S#P##S$-s#4S+#s-NS$&$#-S,s/`&s#4##%##)#-s/iP&#)&s#=*&s#:S,#$###s#2##S$#(#$+#k##5#k##8#k##:#k##<#k##@#k##s#$#k#0C#k#1C#k#2C#k#DC#k#EC#k#HC#k#3H#$s4ES;&s4^SY##s4G$S;#&s4aSF##s4J$S;#%&#%*#ESY-S;s0-;#aI&M%#S*SFS;S#PS$S,S)S4l#(s#:0#l#Js3vs4%#l#)s3~s3{#l#Js4*s4&#l#Ks#|C#l#Ls$+s$$#l#/s$-s$.##S9S;##S*;s+s-s#h#&#s-_ES<-#s+w&s#h##&##*#-s0AS;&#s-f&s#qs-g&s#n*#$###s#f##S*#(#$+#m#6#&3S(##0#7#&/S(&s#}S(##.##s#q##S*#'#$)#m#-#l#Ms$Ps$Q#l#Fs'`s'a#l#Ns)Zs)X##s,*s,'$#s,#m#%#j#Gs,L#U#InSE%s,2s,1%#C##s,&K#%$##s)a$###l#Os,4N#l#Cs,9s,6#j#Ps,;#U#I,s0cS:BKI'N#S8,KLk##$#,IKBLK'N#S8k##%#%'#BRL'N#S8k##+#j##&#j##$Ij##-#VSlKIYSR/+&$#j#AC#j#BC#k#AC.k#BC#>Cs.q'CS3s.rm#$#As/Js.m,s/Ks.n'Cs.ns.o%$#$s.qs/N'Cs.qs/O%$#9&##S6s5J8s/|#7s2jS-3S%#s4n1Cs3JRs4m1Cs4nRs441C$K#(Cs4#S&s)S)s4oFDDE#G(Cs.{S2s43)s4qFDDE#G(Cs45S2s4')s4sFDDE#G/s4tFDDE#s49+s4uFDDE#s4+s$j+s4vFDDE's4,#+s4wFDDE*s4-#l#%#s4qs4kl#&.s4z#l#'2s4}#j#0C#j#1C#j#2C#j#3H#'CIL,s1AL,RL%#Qk###s$Fk##&#k##(#k#0C#k#1C#k#2C#k#3H#$s5mS/&s6*S>##s5o$S/##s%=s5q$S/#%%#%)#[I#MS<S/S#S$S:l#(7,#l#,s5>s5I#l#*s5Fs5C#l#,s5Ns5J#l#4s#1C#l#5s#;s#4#l#/s#=s#>#,s1[S3m#$#WIS3s1]#l#.s#Fs#D#XSTNs-HS8#'NS8s-I#S.S6##S*JS1#s1X#=S1s1WnN#$##CI#%#$###'#-S6s1h=S1#$%#j#CN#2Cs4`s,^(C#S&#)s5QFDDE#Gl#%#s5Ks5El#&s.Hs5T#l#'s5Xs5W#j#0C##Is-:'C##k#0C#-S<s1v;#UI#l#()&#l#,s5cs5n#l#*s5ks5h#l#,s5ss5o#l#4s#VC#l#5s#`s#Y#l#/s#bs#c#-S/s2$;#USZ##$s-J'C$#m#(#;@USZ#-S)s2,;#$I#j#QC#&s6js#&;#>Cs/~'CS.s0#m#$#As1,s#k,s1-s#l'Cs#ls#m%$#$s#os10'Cs#os11%$#9&#FCs5Ps4`FCs5Qs5S*C#s5N*C%#M#s3B*Cs,Ws5Q*Cs5X#*Cs4g#*Cs1}#7#S-3S%#s6.3S%)#1Cs6.Ms'`1Cs5PK#(Cs*oS&s5K)s6/FDDE#G/s60FDDEs*{#(Cs*rS&s5J)s62FDDE#G/s63FDDEs4-#Hs64FDDE&#(Cs5US&s*v)s66FDDE#G/s67FDDEs5Cs4*4Cs66s%}?Cs5Ys0D(C$O#)s6;FDDE#G+s6<FDDEs5Js5N#+s6=FDDE(s5O#+s6>FDDE*s5P#+s6?FDDE-s5Q#l#%#s69s63l#&6s6B#l#'9s6E#j#0C#j#1C#j#2C#j#DC#j#3H#j#6H#,s5Hs5K'CRs5L%$#'CRs5K%M#9%#'CLM%s5HP-RQ,#s75-Ms2p&s7O#-Qs2r$$#k##'#k##*#k##,#k##.#k#0C#k#1C#k#2C#k#DC#k#3H#k#6H#$s7DS6&s7]SC##s7F$S6#$S6s$7%$#%(#$s&rs&s^I$#MS<S6S>QS#S9S1l#(s#$,#l#,s6qs6|#l#*s6ys6v#l#,s7%s6}#l#4s.OC#l#5s#Ys#R#l#/s#[s#\#$s#`s3$m#$#WSms#bs3&#(Cs6sS2s&])s6uFDDE#G+s6vFDDEs&ks6,#l#%#s6ps6jl#&s/ms6y#l#'s6}s6|#j#0C#,s3<I-Ks3=,J#k##%#k#0C#PS>S+l#()$#l#,s7,s77#l#*s74s71#l#,s7<s78#l#4s.fC#l#5s#ps#i#l#/s#rs#s#,Js$?m#$#VSns$A#SCs#ys#{:s$###s$%s.pSCs$%s#}$#Il#.s$(s$)#-S3s3P;#$s$-#;s3E-#s$,PS*S/l#(s.]s.X#l#,s7@s7K#l#*s7Hs7E#l#,s7Ps7L#l#4s.zC#l#5s$(s#}#l#/s$*s$+#m##s.Vm##s.U2Cs6bs.Q(C#Os6T)s7DFDDE#G+s7EFDDE#s6Ws.Ql#%#s7?s79l#&s1Ss7H#l#'s7Ls7K#j#0C#j#1C##Ks//$#Ik###s.Nk#0C#k#1C#-S>s3m;#WI#s$GPl#(+&#l#,s7Zs7e#l#*s7bs7_#l#,s7js7f#l#4s/8C#l#5s$Bs$;#l#/s$Ds$E#$s/>s#%m#$#m##$YSVs/As#(S(>#&s#)S($s.F#>Cs%V'CS)s%Wm#$#As0>s/E,s0?s/F'Cs/Fs/G%$#$s/Is0B'Cs/Is0C%$#9&#USOs8eNC#FC#s3hFC$s3g5s8h@C#.C#s7B*C#s7B*Cs7I#*Cs6X#*C)#*C+#7#S-:Cs-8*Cs7Os7L*Cs3s#*Cs3v#*C&#7#S-3S%#s8&3S%*#1Cs,~Ls,|KCS$1C#Qs8(1C#Rs8)1C&K#4Cs8's.R2Cs.Ss7H(C$S2#)s8,FDDE#G(Cs)[S&%)s8.FDDE#G/s8/FDDE%#(Cs)^S&))s81FDDE#G/s82FDDEs,j#Hs83FDDE&#(Cs7ES&s)b)s85FDDE#G?Cs7Us)\4C#s.](Cs.]O#)s89FDDE#G(Cs2ES2s7Z)s8;FDDE#G/s8<FDDEs/Ms,s?Cs7]s.f(C#S2s7\)s8?FDDE#G?Cs(.s)f4C#s.g?Cs,~s$g4Cs(-#2C%#(Cs(*O#)s8FFDDE#G+s8GFDDE*s7Y#+s8HFDDE.s7Z#+s8IFDDE0s7[#+s8JFDDE3s7\#+s8KFDDE8s7]#+s8LFDDE;s7^#l#%#s8Fs8@l#&s#(s8O#l#'s#.s8R#j#0C#j#1C#j#2C#j#DC#j#EC#j#HC#j#IC#j#RC#j#3H#j#6H#,s98s97'CPs98%$#'CPs9;%S$#9%#'CKS$&s0Es('-QP&#s()$%#,s5&M,QM%#S.-S#S',#s9L-s(YS'&#s('-Ps5--S,#&s(Y##&#$s('#k##*#k##-#k##0#k##2#k##7#k##9#k#0C#k#1C#k#2C#k#DC#k#EC#k#HC#k#IC#k#RC#k#3H#k#6H#$s9dS1$S1s/y$S1s$~%$#%&##S>s9i$#s&Z-SCs5I;#ES@-S1s5L;#dI*(MS>&%#S*SCS1QS#PS,S/S7l#(s#70#l#,s99s9D#l#*s9As9>#l#,s9Is9E#l#4s0lC#l#5s$2s$+#l#/s$4s$5##S)S1##S*-s)*s&-&#s2}ES7-#s&1&s)*##&##)#-s)14&#s3(-)7&s)0##%#$(#m#2#&0S(##-#3#&,S(##*$%#m#)#l#Fs$Qs$O#l#Ss$}s$z##S3S/##S*=S6s%##$#=S6s&Q$$#m#)#SNS8s&i#s1KIl#.s&vs&u#j#Ps's#U#InSE%s1gs1f%#C##s1UK#%$##s'v$###l#Os1vN#l#Cs1ns1j#IPJSNS8s1q$#Il#.s2+s2*#j#@s3%#U#InSP$s60%#C#Ts5pK#%$#Us3($#V#l#Cs62N#l#Ts66s64#m##s6>5s,l#s-h#$L#>Cs:7'CLs:8m#$##S+s:RAs9P#,s9Q$8s9R%'C#&%%#$(s9U'C&s9V%$#9&##S,s:\8s-x#/s9{FDDEs7is7u/s9|FDDEs9A#/s9}FDDEs8Z#CC72Cs7p#(Cs95O#)s:%FDDE#G+s:&FDDE's98#l#%#s9|s9vl#&s44s:)#l#'s:-s:,#j#0C#j#1C#j#3H#j#6H#j#7H##s8Js:n$I#%#M%R#%L##s93s#)$K#k##%#k#0C#k#1C#k#3H#k#6H#k#7H#&s;7S0##s:|$S+#$s:~S+,S0S+T%$#S:S+Pl#(6)#l#,s:Is:T#l#*s:Qs:N#l#,s:Ys:U#l#4s#*C#l#5s#5s#-#l#/s#8s#9#m##s#</s:JFDDEs9Vs9'+s:KFDDE#s9]s9Wl#%#s:Es:?l#&s4Ys:N#l#'s:Rs:Q#j#0C#j#1C#j#3H#%s(eLk###s(hk#0C#k#1C#k#3H##s4ss;:$S+#%#=%=#R#S+S0Pl#(-(#l#,s:cs:n#l#*s:ks:h#l#,s:ss:o#l#4s#DC#l#5s#Os#G#l#/s#Rs#S#m##s76(Cs:cS2s9u)s:eFDDE#G+s:fFDDEs3Xs9x#l#%#s:`s:Zl#&s3]s:i#l#'s:ms:l#j#0C#j#3H#j#6H#,JKk##s3S#k#0C#k#3H#k#6H#R;s#4S+Pl#()$#l#,s:zs;)#l#*s;&s;##l#,s;.s;*#l#4s#[C#l#5s#fs#^#l#/s#is#j#m##s7LLs7Ns7M:#m##s7MLs#ps7Ns#6#%s#qs7Om#$#m##s7PLs7Ws7Qs#w#l#:s7gs7`#l#Ws:fs:g#l#9s;cC##IP##S*nN#$##Cs$)#%#I##OS$I#$#OS$P$$#ES$$I#,PI,JI%$#%&#%)#l#9s;rC#m#2#j#;s;w#j#<s<'#j#Xs<*#j#=s<,#j#Ys<0#j#ZC#j#>C#j#[C##"). Qed.
End HCW.
