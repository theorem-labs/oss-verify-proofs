(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up invariant over the run's input with its mmap base; the reserved list split into the image's segments and a bounded rest; the main entry's fresh-variable constants renumbered to the hand-off states the start-up run computes, and those states' digest checked by computation; open_facts and PM_open re-proved as text over the whole input). *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanInitL BothImages BothPlanImages AsHSTab BoStartupHSF BoStartupCerts AsMainVM BoMainState.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsMainSyms.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* LPS 727298f3: the main entry's hand-off states are computed in the build ([BoStartupHSF]), whose
   fresh variables are the recorded ones moved by [vsh_main] ([K_map] below). *)
Definition K_TID : nat := 49.
Definition K_B04 : nat := 99.   Definition K_B05 : nat := 228.  Definition K_B06 : nat := 229.  Definition K_R06 : nat := 230.
Definition K_B08 : nat := 247.  Definition K_B09 : nat := 248.  Definition K_B10 : nat := 249.  Definition K_B11 : nat := 266.
Definition K_B12 : nat := 333.  Definition K_B13 : nat := 334.  Definition K_B16 : nat := 399.
Definition K_META : nat := 416.
Definition K_B20 (g : bool) : nat := if g then 416 else 417.
(* [comment removed for export] *)
Definition K_B21 (g : bool) : nat := 450.
Definition K_B22 (g : bool) : nat := 451.
Definition K_B23 (g : bool) : nat := 468.
Definition K_X (g : bool) : nat := 6597.
(* [comment removed for export] *)
(* each constant is the recorded one under [vsh_main] *)
Lemma K_map :
  K_TID = vsh_main 44 /\ K_B04 = vsh_main 94 /\ K_B05 = vsh_main 223 /\ K_B06 = vsh_main 224 /\ K_R06 = vsh_main 225
  /\ K_B08 = vsh_main 242 /\ K_B09 = vsh_main 243 /\ K_B10 = vsh_main 244 /\ K_B11 = vsh_main 261
  /\ K_B12 = vsh_main 326 /\ K_B13 = vsh_main 327 /\ K_B16 = vsh_main 392 /\ K_META = vsh_main 409
  /\ (forall g, K_B20 g = vsh_main (if g then 409 else 410)) /\ (forall g, K_B21 g = vsh_main 443)
  /\ (forall g, K_B22 g = vsh_main 444) /\ (forall g, K_B23 g = vsh_main 461) /\ (forall g, K_X g = vsh_main 6590).
Proof. repeat split; try (intros []); vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hole_granted (h : nat) : bool := match h with 0 | 1 | 4 => true | _ => false end%nat.
(* [comment removed for export] *)
Definition hole_class (h : nat) : nat := match h with 0 | 1 | 2 | 3 => 0 | _ => 1 end%nat.

(* [comment removed for export] *)
Definition vE (E : env) (k : nat) : Z := bv_unsigned (ev E k).
Lemma uE_var : forall E k, uE E (EVar k) = vE E k.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition Xof (g : bool) (E : env) : pm_syms :=
  PMS (vE E K_TID) g
      (4096 * vE E K_B04) (4096 * vE E K_B05) (4096 * vE E K_B06) (4096 * vE E K_B08) (4096 * vE E K_B09) (4096 * vE E K_B10)
      (4096 * vE E K_B11) (4096 * vE E K_B12) (4096 * vE E K_B13) (4096 * vE E K_B16) (4096 * vE E (K_B20 g)) (4096 * vE E (K_B21 g))
      (4096 * vE E (K_B22 g)) (4096 * vE E (K_B23 g))
      (if g then 0 else 4096 * vE E K_META).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* #38: the Section is over the run's input [inp]; [argv envp uid hw fs] are its projections,
   [Local Notation]s so that statements and by-name references read as before.  The invariant
   is [SINV0L] (the mmap base bound inside), [apc] the Both image's entry. *)
Section Generic.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Local Notation argv := (in_argv inp).
  Local Notation envp := (in_envp inp).
  Local Notation uid := (in_uid inp).
  Local Notation hw := (in_hwcap inp).
  Local Notation fs := (in_fs inp).
  Hypothesis HC : cs_ok BSEGS2 BOTH_H AsanInit.LIMIT
                        (SINV0L BPH2 OSSVerify.boost_beast.http_request.images.AsanUbsan.M.init_pc sp0 rdraw brk0 inp)
                        (argH0 sp0 rdraw inp) fs E ch R FULL model.
  (** the valuation's first [NX0] variables are [E0]'s: [SINV0L]'s first conjunct reads no base *)
  Ltac hev := pose proof (SINV0L_ev _ _ _ _ _ _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as HE.

  (* [comment removed for export] *)
  Lemma cs_reg_lin : forall r : Z, 0 < r < 32 ->
    getr R (Z_to_bv 5 r) = Z_to_bv 64 (lden E (lin_of (nth (Z.to_nat r) (s_regs (a_ss ch)) (ELit 0)))).
  Proof.
    intros r Hr. rewrite (co_regs _ _ _ _ _ _ _ _ _ _ _ HC (Z_to_bv 5 r)).
    rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E _)). apply eqm_Z_to_bv. apply eqm_sym.
    unfold sr_get, ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (cbn; lia).
    destruct (bv_eqb (Z_to_bv 5 r) 0) eqn:B.
    - apply bv_eqb_eq in B. apply (f_equal bv_unsigned) in B. rewrite Z_to_bv_unsigned in B.
      unfold bv_wrap, bv_modulus in B. rewrite Z.mod_small in B by (cbn; lia). exfalso. clear -B Hr. vm_compute in B. lia.
    - apply lin_of_sound.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hbrk : valid_brk BSEGS2 brk0.
  Lemma cs_v0 : vE E 0 = bv_unsigned sp0 / 32768.
  Proof.
    hev. unfold vE. rewrite (HE 0%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. pose proof (u64_range sp0). apply u_of_Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma cs_v6 : vE E 6 = (bv_unsigned sp0 mod 32768) / 4096.
  Proof.
    hev. unfold vE. rewrite (HE 6%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. pose proof (Z.mod_pos_bound (bv_unsigned sp0) 32768). apply u_of_Z.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
  Lemma cs_v10 : vE E 10 = (bv_unsigned sp0 mod 4096) / 16.
  Proof.
    hev. unfold vE. rewrite (HE 10%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. pose proof (Z.mod_pos_bound (bv_unsigned sp0) 4096 ltac:(lia)). apply u_of_Z.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma cs_v1 : vE E 1 = Z.of_nat (length argv).
  Proof.
    hev. unfold vE. rewrite (HE 1%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. apply u_of_Z. destruct Hva as [? _]. lia.
  Qed.
  Lemma cs_v2 : vE E 2 = Z.of_nat (length envp).
  Proof.
    hev. unfold vE. rewrite (HE 2%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. apply u_of_Z. destruct Hve as [? _]. lia.
  Qed.
  Lemma cs_v5 : vE E 5 = bv_unsigned brk0 / 4096.
  Proof.
    hev. unfold vE. rewrite (HE 5%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. pose proof (u64_range brk0). apply u_of_Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma cs_v8 : vE E 8 = bv_unsigned uid.
  Proof.
    hev. unfold vE. rewrite (HE 8%nat) by (unfold NX0; lia). reflexivity.
  Qed.
  Lemma cs_v9 : vE E 9 = bv_unsigned hw.
  Proof.
    hev. unfold vE. rewrite (HE 9%nat) by (unfold NX0; lia). reflexivity.
  Qed.
  (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp0.
  Lemma cs_sp0 : 32768 * vE E 0 + 4096 * vE E 6 + 16 * vE E 10 = bv_unsigned sp0.
  Proof.
    ltac2:(KReplay.runc [|constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(sp0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.vE); constr:(E); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(Hsp); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.sp_window_lo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.sp_window_hi); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.Znumtheory.Zmod_div_mod); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.Generic.cs_v10); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.Generic.cs_v6); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.Generic.cs_v0)|] [|@z; @__ff; @__varmap; @__wit; @__arith; @__x1; @__x2; @__x3; @__x4; @__x5; @__x6; @__x7; @__x8; @__sat4; @__sat5; @__sat6; @__sat7; @__sat8; @__sat9; @__sat10; @__sat11; @H3; @H2; @H1; @H0; @H; @Hal; @_H0; @_H; @v|] "#&}#1#|#5#U#V#J#T###[#Z#N#,#*#+#:#$#(#C#A#%#c#f#)#v#F#_#`#h#e#d#&#l#r#'#-#K#8#7#;#H#I#M#O#P#Q#S#\#a#b#]#p#o#y#.#/#0#E#|#}#~#=#?#9#G#>#X#W#B#m#w#u#q#<#D#j#n#s#z#Y#^#k#t#6#@#R#L#g#i#x#{#4B#]&#^%#_$#`%#a%#b'#c*#d$#e&#f%#g+#h%#i$#j%#k%#l&#m'#n&#o%#p%#q&#r%#s%#t%#u)#v&#w%#x%#y$#z&#{)%O%#%#%#%#%#US5#VS6#S7%%%#%#%#%#%#%#%#%#/#9-#$$H/)*R*#*#*#*#*#:S##$*#',#/=*'*#*#*#:S##$(#'*##C#Aj#$C#0s##99#7$;:$9H'$#'#+#C#s#)j#$C#0s#+>9#5$@+'+#$8H'$##C#s#1j#$C#&S8s#3&s#4S90s#5>#C#FVS)%#VS)'#$B/'.##C#s#;j##&#j##($US:KUS;KUS<CUS=CUS>C5Cs#95CF(C$J#)&GDDE#I;'GDDE#VS?(E6S*S+VS@HS$#S*#S+m$%#WSACFPXSBHS$$#l#%*)#l#&21#l#'54##Cs#HFk###S%l#(%#H<s#Us#K#'s#3s#5#Cs#W#5Cs#K(C#J7):GDDE#I;;GDDE#l#%#60l#&?>#l#'BA##Cs#RFk###S%l#(%#H<s#As#U#0s#Bs#V's#9##Cs#D#5Cs#O(C#Js#%)s#(GDDE#I;s#)GDDE#l#%#s#$>l#&s#-s#,#l#'s#0s#/##Cs#VFk###S%l#(%#H<s#Gs#Y#0s#Hs#Z's#;##Cs#J##CHFj#$C#(Cs#4S&2)s#7GDDE#Il#%#s#2s#,l#&s#;s#:#l#'s#>s#=#=Fs#dl#($#H(Cs#;S&s#')s#>GDDE#Il#%#s#9s#3l#&s#Bs#A#l#'s#Es#D#=Fs#ul#($#H$Hs#m#Cs#x#j#$C#/s$)$#s#q6C#XS,C&%#ZS-s#ts#~s$/1*#ZS.Cs#Y9S/=##C>F#CHs#ej#$C#6Cs#g(Cs#OS&s#P)s#RGDDE#Il#%#s#Ms#Gl#&s#Vs#U#l#'s#Ys#X#=Fs$0l#($#H$Hs$/#Cs$3#j#$C#/s$D$#s$36C#XS,C&%#ZS-s$6s$9s$C>*#ZS.Cs#w32s#?##Cs#@s#x>s#ys$/&Fs#z&Fs$1&Fs#{k##$#k##&#1s$+s$?&Fs$,&Fs$A&Fs#Jk##$#k##&#1s$Rs$;&Fs$S&Fs#}k##/#k##%#1s$Ws$M&Fs$Nk###.k##)#>s$:s$N&Fs$:k##1#k##3#>s$_s$U&Fs$Uk##+#k##1#1s$:s$L&Fs#Qk##?#k##A#1s$gs$Zk##<s##k##8#USCOVSDC#.Cs$Z2C$#.Cs$]2C&#.Cs$`2C(#.Cs$c2C*#.Cs$f2C,#.CR+C$#+C'#+C*#+C-#+C0#VS0#S1+C+)+C.#+C1#+C4#+C7#VS0#S17K)s$G7K$#7K%#7K,#8CM3C#S2s$J8CQ3C$S$#8CN3C#Ns$N8CS'3C$S/#3C'P#?O%#,C#(Cs$QS(#)s$TGDDE#IUSED(Cs$TS(s$@)s$WGDDE#I?*,C#(Cs$XS(#)s$[GDDE#I-s$\GDDE')#-s$]GDDE+*#,Cs%G(C(J#)s$`GDDE#I?s%K,C#(C#Js$a)s$dGDDE#I,C7@Cs$B#4C#'(C,J#)s$iGDDE#I,Cs%U@Cs$U#4C#5(C=J#)s$nGDDE#I,Cs%Y,CO@Cs$p#4C#B(C&J#)s$tGDDE#I4C&,4C#2(C#J*)s$xGDDE#I-s$yGDDE's#&#-s$zGDDE.s#'#-s${GDDE4s#(#-s$|GDDE:s#)#-s$}GDDE?s#*#-s$~GDDEs##s#+#l#%#s$ys$sl#&s#3s%%#l#'s#=s%(#j#)C#j#*C#j#+C#j#,C#j#-C#j#.C#j#/C#j#0C#&FS2&FMk##s$$#k##%##CS'M#CLF$s%]Q'#S3#CL#$s%jQ'#L#CN#$s%pQ'#L#CN#$s%sS'$s%qM'$#$s%iN'$##C#Lk##)#k##-#k##1#k##5#k##7#k##9#k#)C#k#*C#k#+C#k#,C#k#-C#k#.C#k#/C#k#0C#bHs$~s%hs%0s%ps&5s%gs%os&*MLS3SFSGSHl#(s#'$#l#1s$.s$,#l#2s$3s$0#l#3s$8s$5#l#4s$=s$:#l#5s$Bs$?#l#6s$Hs$D#l#7s$Os$J#l#8s$Vs$Q#l#9s$Ys$X#l#:s$ns$m#l#;s%/s%,#l#<s%>s%;#l#=s%Ls%J#j#>s%l#j#?s%o#V#PHj##s%o#j##s%r#YS4s%ss%qs%j#Hj#=s%q#j#@s%v#V#PHj##s%t#j##s%y#YS4s%zs%vs%q#Hl#ASIs%v#ACs&'s%}#s&5SJACs&0s&*#s&>SK:S#RACs&Is&4$#SL#"). Qed.
  (* [comment removed for export] *)
  Lemma cs_sp0_mod : 16 * vE E 10 = bv_unsigned sp0 mod 4096.
  Proof.
    ltac2:(KReplay.runc [|constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(sp0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(Hsp); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.sp_window_lo); constr:(@LinuxProcessSemantics.LinuxProcessSem.State.sp_window_hi); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Stdlib.ZArith.Znumtheory.Zmod_div_mod); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.vE); constr:(E); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.Generic.cs_v10)|] [|@z; @__ff; @__varmap; @__wit; @__arith; @__x1; @__x2; @__x3; @__sat1; @__sat2; @__sat3; @__sat4; @H0; @H; @Hal; @_H0; @_H; @v|] "#%%#*#p#.#I#>###J#H#O#%#$#B#N#4#&#:#R#S#T#X#[#\#e#a#f#g#`#j#l#?#2#1#5#/#<#=#A#C#D#E#G#F#P#U#V#Q#W#@#]#Z#Y#^#i#h#k#n#p#o#(#)#9#q#r#-#s#3#7#d#;#8#L#K#b#6#0#M#_#c#m1#b$#c&#d$#e%#f%#g'#h*#i&#j$#k%#l%#m%#n%#o%#N##########US/#VS0#S1#%##########+#,*#+/VS2$#'$F$C#&j#$C#&S30&1S4,2)$C#EVP%#VP'#'-,$C#/j##%#j##'$US5LUS6LUS7CUS8CUS9C-C6-CE(C$M#)&HDDG#IZS:'HDDG#VS;(GVQRS#VS<FJ$R#S#m$%#WS=CEKXS>FJ$#l#%*)#l#&21#l#'54#$Cs#%Ek###S?l#(%#FWS@s#)s#(#,s#*s#)VS$?#$Cs#,#$CFEj#$C#(C9S%:)<HDDG#Il#%#71l#&@?#l#'s##B#VS&Es#3l#($#F-Cs#7(CAS%#)s#$HDDG#Il#%#?9l#&s#(s#'#l#'s#+s#*#VS&Es#=l#($#F'Fs#=$Cs#@#j#$C#+s#G'#s#AVQC#XSAC&%#ZSBs#Ds#Fs#M2*#ZSCCs#>:K>#$C?EVSDs#Hs#G&Es#I&Es#I&Es#Ik##$#k##&#.s#Vs#O&Es#W&Es#Qk###*k##%#.s#[s#R&Es#Lk##-#k##)#.s#Ws#V&Es#0k##1#k##3#%S'%#/C#/C%/CS'*C$#*C&#VS(#S)USENVSFC#WS*C#*WS*C$**C#**C%#VS(#S)WS+L#s#ZWS+L+#VSGCOXS,C#Js#[XS,C#Ks#\0Cs#}(C#Ms#Z)s#]HDDG#IUSHD0Cs$&0CNWSICs#`#WSJC#)(C&M#)s#dHDDG#I(C&M()s#fHDDG#I\S-s#gHDDG%+#\S-s#hHDDG-,#l#%#s#cs#]l#&2s#k#l#'6s#n#j#)C#j#*C#j#+C#$CJE's$'KVS$#O$CJ#'s$*J$C#Ok##%#k##)#k#)C#k#*C#k#+C#YFs#fs$2s$0SKSLl#(/$#l#,s#;s#8#l#-s#@s#=#l#.s#Fs#B#l#/s#Ms#H#l#0s#Ps#O#l#1s#ns#k#j#2s$1#j#3s$4#V#KFj##s$4#j##s$7#YS.s$8s$6s$0#Fj#1s$6#j#4s$;#V#KFj##s$9#j##s$>#YS.s$?s$;s$7#Fl#5SMs$;#%s#I%#%#%#%#%#%#%#VSNSO#ZSPCs$Ns$K,#SQ#"). Qed.
  Lemma cs_brk0 : 4096 * vE E 5 = bv_unsigned brk0.
  Proof.
    rewrite cs_v5. destruct Hbrk as (_ & _ & Hal). unfold page_size in Hal.
    pose proof (Z.div_mod (bv_unsigned brk0) 4096 ltac:(lia)). lia.
  Qed.

  #[local] Notation MR := (Mr BOTH_H (argH0 sp0 rdraw inp) E ch model FULL).

  (* [comment removed for export] *)
  Lemma cs_fact : forall K, existsb (kentry_eqb K) (kn ch) = true -> kentry_ok BSEGS2 E MR K.
  Proof.
    intros K H. apply existsb_exists in H as [K' [Hin Heq]]. apply kentry_eqb_eq in Heq. subst K'.
    exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K Hin).
  Qed.
  (* [comment removed for export] *)
  Lemma cs_range : forall e lo hi, existsb (kentry_eqb (KRange e lo hi)) (kn ch) = true -> lo <= uE E e <= hi.
  Proof. intros e lo hi H. pose proof (cs_fact _ H) as K. cbn [kentry_ok] in K. unfold uE. lia. Qed.
  (* [comment removed for export] *)
  Lemma cs_disj : forall b1 o1 n1 b2 o2 n2, existsb (kentry_eqb (KDisj (SA b1 o1) n1 (SA b2 o2) n2)) (kn ch) = true ->
    uE E b1 + o1 + uE E n1 <= uE E b2 + o2 \/ uE E b2 + o2 + uE E n2 <= uE E b1 + o1.
  Proof. intros b1 o1 n1 b2 o2 n2 H. pose proof (cs_fact _ H) as K. cbn [kentry_ok estart a_base a_off] in K. unfold uE. exact K. Qed.

  (* [comment removed for export] *)
  Lemma maps_match_nofog : forall ms l, no_fog ms = true -> maps_match E ms l -> l = map (amap_den E) ms.
  Proof.
    induction ms as [|m ms IH]; intros l Hnf H; cbn [maps_match] in H.
    - exact H.
    - cbn [no_fog forallb] in Hnf. apply andb_prop in Hnf as [H1 H2]. apply negb_true_iff in H1. rewrite H1 in H.
      destruct H as [l' [-> H]]. cbn [map]. f_equal. exact (IH l' H2 H).
  Qed.
  Definition lin_iv (E : env) (m : amap) : word * word :=
    (Z_to_bv 64 (lden E (lin_of (am_base m))), Z_to_bv 64 (lden E (lin_of (am_len m)))).
  Lemma amap_den_lin : forall m, amap_den E m = lin_iv E m.
  Proof.
    intros m. unfold amap_den, lin_iv. f_equal.
    - rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E _)). apply eqm_Z_to_bv. apply eqm_sym. apply lin_of_sound.
    - rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E _)). apply eqm_Z_to_bv. apply eqm_sym. apply lin_of_sound.
  Qed.
  Lemma cs_maps : no_fog (a_maps ch) = true -> vm_maps (m_vmmaps model) = map (lin_iv E) (a_maps ch).
  Proof.
    intros Hnf. rewrite (maps_match_nofog _ _ Hnf (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)).
    apply map_ext. intros m. apply amap_den_lin.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_noacc_lazy : forall N L, cs_ledgers ch = Some (N, L) ->
    vm_noaccess (m_vmmaps model) = sivs_den E N /\ m_vm_lazy model = sivs_den E L.
  Proof. intros N L H. destruct (cs_ledgers_sound _ _ _ _ _ _ _ _ _ _ _ N L HC H) as (A & B & _). split; assumption. Qed.

  (* [comment removed for export] *)
  Lemma cs_brk : vm_brk (m_vmmaps model) = Z_to_bv 64 (lden E (lin_of (a_brk ch))).
  Proof.
    rewrite (co_brk _ _ _ _ _ _ _ _ _ _ _ HC). rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E _)).
    apply eqm_Z_to_bv. apply eqm_sym. apply lin_of_sound.
  Qed.
  Lemma cs_fds : a_fd ch = FdStd -> m_fds model = fds_std.
  Proof. intros H. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as F. rewrite H in F. exact F. Qed.
  Lemma cs_fs : m_fs model = fs.
  Proof. exact (co_fs _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma cs_halted : m_halted model = None.
  Proof. exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma cs_limit : vm_limit (m_vmmaps model) = target_alloc_limit.
  Proof. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  (** #38 (RESERVED-CEILING-CLASS): [co_res] no longer equates the reserved list with the
      image's segments -- [As/AsanPlanSound.v:333-341] gives the segment part PLUS the
      launch's extra intervals, the vDSO/vvar pair among them.  This re-exports the
      producer's own projection [co_resx] verbatim: nothing weaker, nothing invented. *)
  Lemma cs_reserved : exists rx : list (word * word),
    vm_reserved (m_vmmaps model) = segments_reserved BSEGS2 ++ rx
    /\ Forall (resx_entry_ok BOTH_H) rx /\ (length rx <= n_resx BOTH_H)%nat /\ sum_sizes rx <= resx_bytes BOTH_H.
  Proof. exact (co_resx _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma cs_eager : eager_used model <= a_eager ch.
  Proof. exact (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
End Generic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record digest : Type := DG {
  dg_pc : Z; dg_regs : list lin; dg_maps : list (lin * lin * mkind); dg_nofog : bool;
  dg_ledgers : option (list siv * list siv); dg_brk : lin; dg_fd : afd; dg_tidset : bool; dg_eager : Z;
  dg_vis : list (lin * lin); dg_ghost : list (lin * lin); dg_cls : nat; dg_kfacts : bool }.
(* [comment removed for export] *)
Definition has_fact (k : list kentry) (K : kentry) : bool := existsb (kentry_eqb K) k.
Definition e_rel06 : expr :=
  EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar K_R06)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar K_B06)) (ELit 65535)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qlo (cls : nat) : Z := match cls with 0%nat => 0 | _ => 0 end.
Definition qhi (cls : nat) : Z := match cls with 0%nat => 7 | _ => 7 end.
Definition wlo (cls : nat) : Z := match cls with 0%nat => 0 | _ => 11 end.
Definition whi (cls : nat) : Z := match cls with 0%nat => 10 | _ => 255 end.
Definition kn_cls (k : list kentry) : nat :=
  if has_fact k (KRange (EVar 10) 0 10) then 0%nat else 1%nat.
Definition kn_facts (k : list kentry) (cls : nat) : bool :=
  has_fact k (KRange (EVar K_R06) 0 15) && has_fact k (KRange (EVar K_B06) 4295491576 34326181871) && has_fact k (KRange e_rel06 0 0)
  && has_fact k (KRange (EVar 6) (qlo cls) (qhi cls)) && has_fact k (KRange (EVar 10) (wlo cls) (whi cls))
  && has_fact k (KRange (EVar K_TID) 1 4194303)
  && has_fact k (KRange (EVar 0) 4294901760 4294967295).
Definition hs_digest (ch : acs) : digest :=
  DG (pc ch) (map lin_of (s_regs (a_ss ch)))
     (map (fun m => (lin_of (am_base m), lin_of (am_len m), am_kind m)) (a_maps ch)) (no_fog (a_maps ch))
     (cs_ledgers ch) (lin_of (a_brk ch)) (a_fd ch) (a_tidset ch) (a_eager ch)
     (map (fun p => (lin_of (fst p), lin_of (snd p))) (a_vis ch)) (map (fun p => (lin_of (fst p), lin_of (snd p))) (a_ghost ch))
     (kn_cls (kn ch)) (kn_facts (kn ch) (kn_cls (kn ch))).

Definition pg (k : nat) : lin := (0, [(4096, EVar k)]).            (* [comment removed for export] *)
Definition pgo (c : Z) (k : nat) : lin := (c, [(4096, EVar k)]).   (* [comment removed for export] *)
Definition lRI : lin := (137439019008, [(4096, EVar K_B06); (-4096, EVar K_R06)]).      (* [comment removed for export] *)
Definition lRI' : lin := (137439023104, [(4096, EVar K_B06); (-4096, EVar K_R06)]).    (* [comment removed for export] *)
Definition lSP (c : Z) : lin := (c, [(32768, EVar 0); (4096, EVar 6); (16, EVar 10)]).               (* [comment removed for export] *)
Definition lENVP : lin := (16, [(32768, EVar 0); (8, EVar 1); (4096, EVar 6); (16, EVar 10)]).        (* [comment removed for export] *)
Definition lv (k : nat) : lin := (0, [(1, EVar k)]).

Definition lvx (g : bool) (i : nat) : lin := lv (K_X g + i).   (* [comment removed for export] *)
Definition DG_regs (g : bool) : list lin :=
  [(0, []); (1060584, []); lSP (-48); (67584, []); (6690800, []); lvx g 0; lvx g 1; lvx g 2;
   lSP 8; lv 1; lv 1; lSP 8; lENVP; lvx g 3; lvx g 4; lvx g 5; lvx g 6; lvx g 7; (671644, []); lENVP;
   (0, []); (0, []); (0, []); (0, []); (0, []); (0, []); (0, []); (0, []); lvx g 8; lvx g 9; lvx g 10; lvx g 11].
(* [comment removed for export] *)
Definition lMETA (g : bool) : lin := if g then pg 5 else pg K_META.
Definition DG_maps (g : bool) : list (lin * lin * mkind) :=
  [(pg (K_B23 g), (4096, []), KRW); (pg (K_B22 g), (8388608, []), KRWLAZY); (pg (K_B21 g), (1048576, []), KRW);
   (pg (K_B20 g), (4096, []), KRW); (lMETA g, (8192, []), KRW); (pg K_B16, (11571200, []), KRW); (pg K_B12, (4096, []), KRW);
   (pg K_B11, (4096, []), KRW); (pg K_B10, (65536, []), KRW); (pg K_B09, (4096, []), KRW); (pg K_B08, (8388608, []), KNONELAZY);
   (pg K_B06, (137439023104, []), KRW); (pg K_B05, (3727360, []), KRW); (pg K_B04, (65536, []), KRW);
   ((2201439137792, []), (15392894357504, []), KRWLAZY); ((2415882240, []), (2199023255552, []), KNONELAZY); ((2147446784, []), (268435456, []), KRWLAZY)].
Definition DG_noacc (g : bool) : list siv :=
  [(lMETA g, lcat (lconst 4096) (lMETA g)); (pg K_B08, pgo 8388608 K_B08); (pg K_B06, lRI); (lRI', pgo 137439023104 K_B06); ((2415882240, []), (2201439137792, []))].
(* [comment removed for export] *)
Definition DG_lazy (g : bool) : list siv :=
  [(pg (K_B22 g), pgo 8388608 (K_B22 g)); (pg K_B08, pgo 8388608 K_B08); (pg K_B06, lRI); (lRI', pgo 137439023104 K_B06);
   ((2201439137792, []), (17594333495296, [])); ((2415882240, []), (2201439137792, [])); ((2147446784, []), (2415882240, []))].
Definition DG_vis (g : bool) : list (lin * lin) :=
  [(pg (K_B23 g), (4096, [])); (pg (K_B22 g), (8388608, [])); (pg (K_B21 g), (1048576, []));
   (pg (K_B20 g), (4096, [])); ((if g then pg 5 else pgo 4096 K_META), (if g then (8192, []) else (4096, []))); (pg K_B16, (11571200, [])); (pg K_B12, (4096, []));
   (pg K_B11, (4096, [])); (pg K_B10, (65536, [])); (pg K_B09, (4096, [])); (lRI, (4096, [])); (pg K_B05, (3727360, []));
   (pg K_B04, (65536, [])); ((65536, []), (6766592, [])); ((-8388608, [(32768, EVar 0); (4096, EVar 6)]), (140737496743936, [(-32768, EVar 0); (-4096, EVar 6)]))].
Definition DGX (g : bool) (cls : nat) : digest :=
  DG 671644 (DG_regs g) (DG_maps g) true (Some (DG_noacc g, DG_lazy g)) (if g then pgo 8192 5 else pg 5) FdStd true
     (if g then 16515072 else 16510976) (DG_vis g) [(pg K_B13, (4096, []))] cls true.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.False Sort Prop.

Lemma HS_digest : forall h ch, HSF_both h = Some ch -> hs_digest ch = DGX (hole_granted h) (hole_class h).
Proof.
  (* LPS 727298f3: the recorded proof fixed the digest of the recorded hand-off states; the six
     states are now computed in the build ([BoStartupHSF]), so the digest of each is checked by
     computation against [DGX] (whose constants [K_map] moves by [vsh_main]), walking the
     table as [BoMainCells.HS_some_lt] does. *)
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSF_both_table fold_right fst snd] in Hh.
  do 6 (destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|]).
  destruct Hh.
Qed.

Lemma hole_class_le : forall h ch, HSF_both h = Some ch -> (hole_class h <= 1)%nat.
Proof. intros h ch H. unfold hole_class. destruct h as [|[|[|[|]]]]; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zz2ww (l : list (Z * Z)) : list (word * word) := map (fun p => (Z_to_bv 64 (fst p), Z_to_bv 64 (snd p))) l.

Section LedgersZ.
  Variables (sp0z brk0z : Z) (X : pm_syms).
  Let G : Z := pm_meta_map brk0z X.
  Let RI : Z := pm_region_info X.
  Let PEND : Z := ps_b06 X + 0x2000011000.
  (* [comment removed for export] *)
  Definition PM_REM : list (Z * Z) := if RI + 0x1000 <? PEND then [(RI + 0x1000, PEND - (RI + 0x1000))] else [].
  Definition PM_MAPS : list (Z * Z) :=
    [((ps_b23 X), 0x1000); ((ps_b22 X), 0x800000); ((ps_b21 X), 0x100000); ((ps_b20 X), 0x1000);
     (G, 0x2000); ((ps_b16 X), 0xb09000); ((ps_b12 X), 0x1000); ((ps_b11 X), 0x1000); ((ps_b10 X), 0x10000); ((ps_b09 X), 0x1000);
     ((ps_b08 X), 0x800000); ((ps_b06 X), 0x2000011000); ((ps_b05 X), 0x38e000); ((ps_b04 X), 0x10000);
     (0x2008fff7000, 0xdfff0001000); (0x8fff7000, 0x20000000000); (0x7fff7000, 0x10000000)].
  Definition PM_NOACC : list (Z * Z) :=
    [(G, 0x1000); ((ps_b08 X), 0x800000); ((ps_b06 X), RI - (ps_b06 X))] ++ PM_REM ++ [(0x8fff7000, 0x20000000000)].
End LedgersZ.
(* [comment removed for export] *)
Definition PM_LAZY (sp0z : Z) (X : pm_syms) : list (Z * Z) :=
  [((ps_b22 X), 0x800000); ((ps_b08 X), 0x800000); ((ps_b06 X), pm_region_info X - (ps_b06 X))]
  ++ PM_REM X ++
  [(0x2008fff7000, 0xdfff0001000); (0x8fff7000, 0x20000000000); (0x7fff7000, 0x10000000)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac elim_div x d :=
  let q := fresh "q" in let r := fresh "rm" in
  pose proof (Z.div_mod x d ltac:(lia)); pose proof (Z.mod_pos_bound x d ltac:(lia));
  set (q := x / d) in *; set (r := x mod d) in *; clearbody q r.

(* [comment removed for export] *)
Lemma stack_top_cls : forall sp0z v0 q w cls,
  sp0z = 32768 * v0 + 4096 * q + 16 * w -> qlo cls <= q <= qhi cls -> wlo cls <= w <= whi cls -> (cls <= 1)%nat ->
  pm_stack_top sp0z = 32768 * v0 + 4096 * q + (if Z.leb 11 w then 4096 else 0).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.qlo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.qhi); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.wlo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.whi); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.leb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.bool); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@kc__2); constr:(@Stdlib.ZArith.BinInt.Z.leb_spec); constr:(@Corelib.Init.Datatypes.BoolSpec); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.pm_stack_top)|] [|@sp0z; @y; @x; @__ff; @__varmap; @__wit; @__x1; @__arith; @cstr; @Hc0; @Hc; @Hw; @Hq; @cls; @__p1; @__p2; @rm; @q0; @H1; @H0; @H; @__x2; @__x3; @__x4; @__x5; @b; @b0; @Hcls; @Hsp; @w; @q; @v0|] "#)Z#;$8#>#i#j#h###T#$#'#?#p#&#%#(#N#;#)#U#,#.#*#+#8#n#X#b#s#E#L#G#-#0$2#@#_#1#/#{#4#5$'#:#9#O#v#3#6#\#[#Y#`#a#c#e#g#q#r#t#w#x#u#V#z#2#~$#$$#}$&#7$5$4$3$7#y$9#B#A#D#l#k#F#f#R$/#C#m#Q#|$,#P$-$6#M#S#Z#o$($)$8#H#I#J#K#W#]$.$+#^#d$%$*$1$0M#n%#o%#?%#C&#p$#q'#r*#s%#t+#u$#v&#w$#x%#y%#z%#{%#|%#}%#~&$#$#>%$$%#:$$%/$&%$''$(*$)&$*$$+$$,$$-$$.%$/%$0%$1&$2'$3%$4%$5)$6%$7&'S-'#'#'#'#'#'#'#'#'#'#'#'#'#'#.###M.(##N$%#.3##I$%#&CJ#?I%#M@I%M#*%#AN%#MBN%M#*%#6P7M##7S&#6R$$##5O$$#,s#+'#'#'#'#'#.#0G#,S-,#,#,#,#,#,#,#,#,#,#.#$/#3#s#/##s#0#s#3S'#s#2S&$$#,<.#8#RnS##$##C##%#s#7#H$'#&C+#j#$C#&KJP&KJs#+C$#9J&C#H.S-&C%#C%#US3KUS3C9I9G&C$#&KIGVSAIGWSB%$#j#%K#j#&K#DC1DCH:KC.S*-%J3$PH#DC2:KC0S*/'J5&s#@3#ZSC9853%#7Js#B%86:KCS.S*S/S4J9*s#D7'G%$#GUSDO9O%H#USES+USFS+HCIUSGCUSHC/CH;CS-(C$S)#)&FDDE#LUSID/Cs#&(C'S)#)*FDDE#L(C)S,*),FDDE#L(C+S,').FDDE#L[SJ/FDDE%#+0FDDE(+#+1FDDE-,#VSK2EDS#S>VSLGN&S##S>m$%#WSMCHIXSNGN$#l#'*)#l#(<;#l#)?>#j#*C#%HG%Is#<&CNH&CNs#>C$#k##&#k##(#k#*C#9S&WG#INl#+-%#l#,s#/s#-#l#-s#1s#3#XSOs#Ks#Fs#6#&KOP&KOs#wC$##s$0S$#s$/S'$$##s$.S&$$#0#s#q$#s#e3#s$5##s$68s#`S&nS##$##C##%#s$8#H$+#&C&#j##0#&KRP?G%#S0@G%S0#*%#AI%#S0BI%S0#*%#7Ns$6#s$JS5#s$IS1$$##s$HS6$$#0#s$/$#s$#3#s$O##s$P8s#zS6nS##$##C##%#s$R#H$+#&C&#k#.0#k#/2#k#08#j#1K#?P%#S$@P%S$#*%#AP%#S$BP%S$#*%#7Ps$RVSPs$1S%%s$2S%1S%s$38s$4S%WS7%$#%s$6S11S1s$7#s$mS8#s$lS?$$##s$kSQ$$#0#s$R$#s$F3#s$r##s$snS##$##CI#%#s$t#H$*#&C%#%s$DS5USRC/Cs$y(C#S,s#y)s#{FDDE#LZSSs#|FDDE#l#'#s#ms#gl#((s$##l#)s$'s$&#&Cs%$Hk###STl#+%#GWSU4s%'##s%(4I6s%)$$#&C8##s%.S9#s%-S8$$##s%,S?$$#0#s$o$#s$c(Cs$2S:8)s$4FDDE#Ll#'#s$%s#{l#(<s$7#l#)s$;s$:#1Hs%8l#+$#GWSV*s%:#I+s%;%H#1$s%=*$##s%AS@#s%@S9$$##s%?S8$$#0#s%&$#s$v3#s%F#s%ISW#s%HS@$$##s%GS9$$#0#s%.$#s$~I#s%N%Hs$m:KCS.S*S/S4PHs$`s%?s$ns$^Gs#L$#S'<Cs$TIs#8<C#Is#9/Cs$};Cs%e(C$S)#)s$WFDDE#LJs$XFDDEM.s%@/C#(C(S)#)s$\FDDE#L=s$]FDDE'#Js$^FDDEJ+s$_FDDE$s$Z#+s$`FDDE+s$[#l#'#s$Qs$Kl#(1s$c#l#)s$gs$f#j#*C#j#2Q#j#3Q#%s%4G%I1*N#k###Jk##&#k#*C#k#2Q#k#3Q##Ms%o#s%rS;#s%qS<$$#$#s%s&C'#%HS(YG$#S(RS%l#+3+#l#-s#)s#+#l#4s#-C#l#5s#6C#l#6s#Cs#?#l#7s#Ws#S#j#8s#d#U#G1S5s%L4CPKCs&%LC#$6s%r6#6#6#4C#4C%KCs&*4C)LC$#-C&#-C(#-C.#E#S222#USXS-VSYC#4C1WSZC$#-C0#4Cs&).s&EKC#LC#;-C#4-C'#E#S22)#2+#FS+#s%GFS+2#HCJ<C#Ns$,HCO<C#Ms$.<C%I#;Cs&2(Cs%JS)#)s%LFDDE#L(C%S:s$2)s%NFDDE#L=s%OFDDE%#/Cs&R;Cs&b>C$#;Cs&3>Cs$9#5C%#/Cs&S>C#s#`5C%#/Cs&;WS[C$#/Cs&05C$#>Cs$Bs%[5C#6(C%S,#)s%`FDDE#L(Cs#jS:s#k)s%bFDDE#L(Cs%bS)s#l)s%dFDDE#LJs%eFDDES&=s%fFDDE$#>Cs%es$L5C5s%g(C$S,#)s%jFDDE#L+s%kFDDE's%f#+s%lFDDE,s%g#+s%mFDDE/s%h#+s%nFDDEAs%i#l#'#s%_s%Yl#(s#)s%q#l#)s#/s%t#j#*C#j#9C#j#:C#j#;C#j#<C#j#2Q#%HJ1Js&y*$##s&}N#s&|M$$##s&{J$$#0#s&b$#s&V#s'&I$#O&C%#1Os&R%HR*#S'#Js',#s'/O$#s&v$#H&C&#k##(#k##+#k##-#k##8#k#*C#k#9C#k#:C#k#;C#k#<C#k#2Q#%S(s$@^G#NS(S<S;MJORS%l#+s#$%#l#-s$Ks$M#l#4s$OC#l#5s$XC#l#6s$es$a#l#7s$ys$u#j#8s#~#U#GnS7%s%:s%9%#=##s%-I#%$##s$%$###l#>s%SS##l#=s%As%=##s'JS1#s'IS6$$##s'HS%$$#0#s'/$#s'#3#s'O##s'PnS##$##Cs%H#%#s'Q#H$*#&C%#m#/#j#.s%P#j#/s%R#j#0s%X#]S=KPs%^#S&GOJMj#8s%{#U#Gj##s&2#&KRs'K?s'L%#S$@s'N%S$#*%#As'Q%#S$Bs'S%S$#*%#7s'Vs'V%s'*s'*:KCS.S*S/S4s'Xs'+s&ws'Xs'+s&wG%$#S'-Cs$6s$>-Cs$B#-Cs$5s$KE#S22s$7#2&#-Cs$6s$<-Cs$:#E#S22s$<#2s$>#FS+#s&zFS+)#.s'R/C#(Cs%'S)#)s&{FDDE#L=s&|FDDEs#u#5Cs$*s%b(Cs#uS,#)s'#FDDE#L+s'$FDDE&s&{#+s'%FDDEs%,s&|#+s'&FDDEs$$s&}#+s''FDDEs$6s&~#l#'#s&ts&nl#(s$>s'*#l#)1s'-#j#*C#j#9C#j#:C#j#;C#j#<C#j#2Q#%s'ZO%R8*S'#$s#ds(4&Cs#g#k##%#k##(#k##s#n#k##s#y#k#*C#k#9C#k#:C#k#;C#k#<C#k#2Q#%s'iS(^G#NS(S<S;MJORS%l#+4%#l#-s#7s#9#l#4s%TC#l#5s%]C#l#6s%js%f#l#7s%~s%z#j#8s&/#U#G=s'JFDDEs%Qs%P+s'KFDDE#s'Fs%K+s'LFDDEs$Hs'G#l#'#s'=s'7l#(s%Ys'O#l#)s'Ss'R#j#*C#j#2Q#j#3Q#1Gs'|%s'}I*#Nk###Jk##&#k#*C#k#2Q#k#3Q#$s%GH&Cs%K#%S(s#CYG$#S(RS%l#+/'#l#-s#Ts#V#l#4s%qC#l#5s%zC#l#6s&+s&'#l#7s&?s&;#j#8s%D#U#GnS7%s&\s&[%#=##s&OI#%$##@$###l#>s&uS##l#=s&cs&_#m##s#uj#.s#b#j#/s#d#j#0s#j#]S=Ks(]s&t#S&GOJMj#8s#q#U#Gj##s'G#ZS\s'Is'Hs'9s#u#Gl#?s'Ks(8#ZS=Cs(]s(<#S'MUS]S'8s(COnS##$##C##%#s(w#H$s(c#&C&#m#(#j#.s(i#j#/s(l#j#0s(r#j#@s(x#j#1K#j#AC#j#BC#j#CC#j#$C##"). Qed.

(* [comment removed for export] *)
Lemma RI_lin : forall X b06 r, ps_b06 X = b06 -> b06 mod 65536 = 4096 * r ->
  pm_region_info X = 137439019008 + b06 - 4096 * r.
Proof.
  intros X b06 r H1 H2. unfold pm_region_info, pm_space_beg. rewrite H1.
  pose proof (Z.div_mod b06 65536 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma rel06_sound : forall E, uE E e_rel06 = 0 -> 0 <= vE E K_R06 <= 15 -> 0 <= vE E K_B06 <= 2^50 ->
  (4096 * vE E K_B06) mod 65536 = 4096 * vE E K_R06.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.env); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.uE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.e_rel06); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.vE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_R06); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B06); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Init.Logic.eq_ind); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@LinuxProcessSemantics.Riscv.Sem.alu64); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_ADD); constr:(@LinuxProcessSemantics.Riscv.Sem.mul_div); constr:(@LinuxProcessSemantics.Riscv.Instr.M_MUL); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.ev); constr:(@LinuxProcessSemantics.Riscv.Instr.ALU_AND); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.u_add64); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.u_mul64); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.u_and64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.u_lit64a); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.ones); constr:(@Stdlib.ZArith.BinInt.Z.land_ones); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.mod_small); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Corelib.Init.Datatypes.S); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEsub)|] [|@z; @__ff; @__varmap; @__wit; @__arith; @Ha; @__x1; @__x2; @__x3; @__p1; @__sat0; @__sat1; @__sat2; @__sat3; @__sat4; @__sat5; @__sat6; @__sat7; @__sat8; @__sat9; @__x4; @__x5; @__x6; @__x7; @__x8; @rm1; @q1; @H5; @H4; @rm0; @q0; @H3; @H2; @rm; @q; @H1; @H0; @H; @HB; @HR; @E|] "#3M#G$F#L#z#O#{#y###W#S$##$#(#%#~#&#*#s$F#`#'#)#+$.#V#-$7$C#d#,#/#.#1#0#3#4#\#i#2$&$'#6#7#9#:#=#?$3$@#G#<$E$G#F#M#N#^#g#k#n#p#r#t#u#v#x$$$($)$%#q#5#8$?$B$*#;$M#D#J#Y#U#e#h$5#K#f#R#Q$8$J#[$6$2#|#w#T$1#c#j$9$<#P$-#Z$>#b$=#_#}$;$:$H$K$0$A#]#m$+$4$L#X#a#l#o$,$/$D$IT#q$#r$#s%#t%#u&#v&#w%#x%#y%#z&#{&#|%#}$#~%$#'$$*$%$$&%$'%$(%$)%$*+$+%$,%$-)$.%$/$$0&$1'$2%$3%$4'$5%$6%$7&$8*$9&$:%$;%$<%$=&$>%$?%$@$$A)$B%$C&$D&$E&VSGHSH(C#E*LJ+E#$S)$#$#3#+(#9(#*NI+E##S)3##,##$###3#L(#+,#9,##,########US5##$##########=#M*#5PJ?,S$$#3'M.#5PI?0S$$#$s#&$#$#$#$#$#$#$#$#$#$#$#3#M>#GS-1#GSI6#.A#(CHEj#$C#.s#$:.s#%()$#3s#(Ls#6#%%#VSJ@-;C,*N$#(C%E5S%J?s#.S$s#&#.s#/#5MI?s#1S$s#%#GS-#6.s#3#)H#%#/(C#Ej#$C#.s#8s#0.s#9.&$#%#5VS6s#41;C0(H$#5S%I?s#?S$s#3#GS-#s#$.s#A#))#%#=(C#E5S&J.s#F#&1#%#B)#H%#s#$(C#Ej#$C#.s#M>.s#Ns#26$#VSKAs#4;C@'H$#5MJ.s#S#&>#%#s#/)#)%#s#1(C#E5S&I?s#ZS$s#N#.s#[#5QJ.s#]#&s#(#%#s#96H4)$#%#s#<(C#Ej#$C#.s#es#Y.s#f/&$#%#s#BVS6s#]2;C1(H$#6%?)s#&#%#s#G(C#E5S'J.s#p#&H#%#s#L5S'I.s#t#&2#%#s#P6#s#+)(#%#s#S(C#Ej#$C#%s#us#VNs#v;Cs#H%H$#&%s#$%#s#Z5QI.s$&#&@#%#s#^6#s#9)(#%#s#a(C#E5S.J.s$.#&1#%#s#f5S.I.s$2#&H#%#s#j6#s#E)(#%#s#m(C#Ej#$C#%s$/s#pNs$0;Cs#5%H$#&?s#+%#s#t&'s#)%#s#v6#s#Q)&#%#s#y(C#E5S*J.s$F#&s#)#%#s#~5S*I.s$J#&3#%#s$&6#H)(#%#s$)(C#Ej#$C#%s$7s$,Ns$8;Cs#d%H$#&=s#%%#s$06#')s#*#%#s$3(C#EHCs#=VSLs$6s$Q(C#s#?*S/J&H#%#s$:*S/I&s#*#%#s$=6#4)'#%#s$@(C#Ej#$C#OCs#K#L/H*S0J&1#%#s$F*S0I&s#6#%#s$I6#@)'#%#s$L(C#EHCs#<(Cs$js#=*S1J&=#%#s$R*S1I&H#%#s$U6#s#,)'#%#s$X(C#Ej#$C#OCs#I#Ls$vH*S2J&s#)#%#s$^*S2I&s${#%#s$a6#s#8)'#%#s$d(C#EHCs#<3s%4USM#(C#s#?*S3J&s#7#%#s$l*S3I&s%-#%#s$o6#H)'#%#s$r(C#Ej#$C#OCs#K#L/H*S7J&s#C#%#s$x*S7I&s%9#%#s${6#6)'#%#s$~(C#E63:*S4J&s#N#%#s%')#H%#s%)(C#Ej#$C#Ls%`s##%<#USNRUSORUSPCUSQCUSRC@CE@Cs#+1C$O#2&GDDF#KVSS'FHS8S9VSTHN(S8#S9m$%#WSUCELXSVHN$#l#%*)#l#&10#l#'43#+Es#8l#($#HWSWs#2s#:#;CB;H9#)s#7:%#s%F(C#E*S4I&s%d#%#s%J*SXJ&s#t#%#s%M%Hs#$)$#%#s%P(C#Ej#$C#I,s%S+E-+Es%U*S:I&s%r#%#s%X+E#k##'#k##)#Ps&4s&/:Es&5+Es&1:Es&1k##$#k##&#+Es&:Qs&;s&6Lj##S(#j#)%#+Es&8k##S(#k#)(#*S;J&s$6#%#s%k*S;I&s&,#%#s%n%#s#E)'#I#s%q+E$*S<J&s$@#%#s%u*S<I&s&6#%#s%x%#s#O)'#%#s%{+E#k##s#*#k##.#*SYJ&s$L#I#s&%+E$*S=J&s$P#%#s&)+E#k##s#4#k##(#Ps&as&.+Es&/:Es&/k##$#k##s#2#Qs&fs&3Lj##S(#j#)s#0#k##S(s#>k#)s#2#Ps&ks$.:Es#jk##s#V#k##s#;#Qs&os$2Lj##S(#j#)s#9#+Es#pk##S(#k#)s#<#*S>I&s&]#%#s&CI#s#v+E$*S?I&s&b#%#s&H%#s#{+E#k##/#k##)#0CS@/S@/#/#/#0C#'C(#J#S+4*#7Cs&q0C*,C$#'C#.J#S+ER(s$/ER$#ER*#ACPBC#Ps$1ACNBC$L#@Cs&}<CS)>C$#1Cs$4O#2s$6GDDF#KUSZD@Cs'@WSAC#s'31Cs$9O#2s$;GDDF#K<Cs';1Cs$<O#2s$>GDDF#K8s$?GDDF&*#8s$@GDDF,+#1Cs$@O02s$BGDDF#KUS5s'GWSAC.#1C4O#2s$FGDDF#KFs$GGDDF'#<Cs'Y1Cs$HO#2s$JGDDF#KZS[s$KGDDFMFs$LGDDF$#1C;S,62s$NGDDF#KFs$OGDDF;#8s$PGDDF&;#8s$QGDDF,<#8s$RGDDF4=#l#%#s$Ns$Hl#&s#%s$U#l#'s#*s$X#j#*C#j#+C#j#,C#j#-SB#&s'IH+E#+ES%k##s$:#k##%#+EL+Ls'b9$#+EP9#M&s'SP+E#:$s':9$#k##'#k##*#k##.#k#*C#k#+C#k#,C#k#-SB#*S?J+#s'~[H#s#[$s#]S*SCS>l#(;&#l#.s#as#Y#l#/s#is#f#l#0s#ps#m#l#1s#ts#r#l#2s#|s#x#l#3s$)s#~#l#4s$:s$-#l#5s$Gs$D#l#6s$Qs$L#l#7s$[s$S#WS\s$fs'Q#;Cs$fs$^Hs$g#%s$hs%))s%/#%#s'U(C#E1Cs#LS#s%&2s%(GDDF#KZSDs%)GDDF#l#%#s%%s${l#&s%-s%,#l#'s%0s%/#(Cs']Ek###SEl#(%#Hl#.s$.s$,#l#/s$6s$2#Rs$ts'b#Cs$us'c&s'd#)#s$v(Cs$x#*S:J&s&4#1Cs%8S,s#^2s%:GDDF#Kl#%#s%6s%0l#&s%>s%=#l#'s%As%@#l#(#s$AHl#.s$=s$;#l#/s$Es$A#S+s'q#%,s'r+E#:$s't9$#Cs$js'v%s$Us'w#s(<######3#@C#1C#S#s%M2s%OGDDF#KZSDs%PGDDF#l#%#s%Ls%Fl#&s%Ts%S#l#'s%Ws%V#(C*Ek###SEl#(%#HRs$n-#Cs$o.&/#%s$q0)$#(Cs$s#*S=I&s(M#1Cs%^S,42s%`GDDF#Kl#%#s%\s%Vl#&s%ds%c#l#'s%gs%f#:E:l#($#HS*<#%+=+E#:$?9$#*S]I&s([#C#s##*SCI&s(^#%#s#&)S%HR#s(Fs#CC$s(G&s(H#%&s(I)$#(C(#)MLS#s(Ms#;%$s(N+E#:$s(P9$#)S&NC#s(S)QP%#s(U/s$c0C#'C#s$i7Cs#;,C#s$k=s)(DC#/)/#/#/#0C#-C(#0C(-C*#-C+0-C,s$m'C$#'C&#'C)#'C2#$s(w$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#################################################################################################################################3#7C#,C#s&*3s#F7C#/s#v0C#,C%#,C&s#x,C's#w3s#A7C#,C#s&/0Cs&2,C,#'C%#'C)#'C+#'C-#'C3#J#S+4s#|#4s$3#'Cs$)s$5,C/s&@#s*@$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#########################$#=#DC#-C#s$d-C$s$c-C%s$p-C&s&q'Cs#J#'C%#'C'#'C)#'Cs#B##s+P$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$#########################3#7C#,C#s'c$s+~####$#####$###############################################################################$#$###$#$###$#$###$#$#=#DC#/s$t0C#-C%#0Cs&4-C'#0Cs&7-C)#-C*s(E'C$#'C'#'C*#'Cs#I#$s,q$#####$#$#$#$#####$#$#$#$#####$#$#$#$#####$#$#$#$#####$#$#$#$#####$#$#$#$#####$#$#$#$#####$#$###################3#7C#,C#s).$s#6######$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$#$###$###$#####$#$#$#$###$#3#7C#/s#|/#0C#,C&#,C's&9,C(s'R,C)s'Q'C$#'C&#'C(#'Cs#?#=S)DC#0C/-C$#'C#s$*/1/#/#0C#-Cs'f#-Cs'g5-Cs'h+'C#s'c'C%#'C'#'Cs'n#3s'<7C#/-0C#,C%#0C2,C'#,C(B,C)s&X'C$#'C&#'C)#'Cs&J#$s%'########$#$#########$#$#########$#$#########$#$#########$#$#########$#$#########$#$###$###########################3#7C#,C#s*d$s%a########$#$#########$#$#########$#$#########$#$#########$#$#########$#$#########$#$###$#=#DC#/s#y/#0C#-C&#-C's$+0Cs$.-C)#-C*s$4'C$#'C'#'C)#'Cs#=#,Cs+@s+I3s/H7C#/0/#0C#,C&#0C5,C(#,C)s$1,C*s$0'C$#'C&#'C)#'C0#3s(i7C#,C#s+Z$s0###$#$#$#######$#####$#$#####$###$###############$#$###$#$#$#$###$#$#$###$#####$###$#$#####################3#7C#,C#s,2#s'-$#$#$#$#$#$###$###$#######$#$#$###$#$#####$#$###$###$#$#$#$#$#$#$#####$###########$#$#####$#$###$#$#=#DC#/s#~/#0C#-C&#0Cs$'-C(#-C)s$6-C*s%^'C$#'C&#'C)#'Cs#C#'Cs#}#J#S+4s,{#4s$'#4s,}#4s$8#4s-##4s%V#4s%d#4s%p#4s-'#4s%w#4s-)#4s':#4s-+#4s(f#4s)L#ER#s.MERs)O#ACS'BC#S%s.NACS&BC$N#ACMACQBC$P#BC&L#<Cs1ZKC#s-#<Cs1S>Cs,{#KC#s,m1C&S##2s.YGDDF#K1Cs-)S,s+k2s.[GDDF#KFs.\GDDFs,x#>Cs--s-#<Cs1n>Cs+p#KC#s-/1C&S##2s.bGDDF#KWS^Cs-,s-3<Cs1m>C$#<Cs$N>Cs-0#KC#71C&S##2s.jGDDF#K1Cs.jO)2s.lGDDF#K@Cs1{1C,O#2s.oGDDF#KFs.pGDDF&#1Cs-+S#s.p2s.rGDDF#K>Cs-C11Cs-CS##2s.uGDDF#K8s.vGDDF&s-A#8s.wGDDF)s-B#8s.xGDDF0s-C#8s.yGDDF9s-D#8s.zGDDF@s-E#8s.{GDDFs#$s-F#l#%#s.ws.ql#&s#-s.~#l#'s#6s/%#j#*C#j#+C#j#,C#j#8C#j#9C#j#:C#j#;C#j#<C#)MH&s1\Q)#N(C%#:Ls,A9s-/#&s1|M&s,DS')#N(C%#&s01S%),S'(C$#+EM+Ms2G9$#(CQE&s2+Q(CS&#k##%#k##'#k##+#k##/#k##4#k##7#k#*C#k#+C#k#,C#k#8C#k#9C#k#:C#k#;C#k#<C#*SFI*SFJbHS&S*S2S1$M#S.S'S0S/S3S_S4l#(s#'&#l#4s.Ns.L#l#5s.Vs.R#l#6s.{s.x#l#7s/)s/$#l#=s,1C#l#>s,4C#l#?s,;s,7#l#@s,Cs,>#l#As,FC#l#Bs,JC#l#Cs,Rs,N#l#Ds,bs,]#l#Es,sC#l#Fs,uC#l#Gs,{s,w#l#Hs-/s-+#l#Is-@s-<#l#Is/Os/L#l#Is/{s/q#l#Hs0/s0,#l#Is0;s01#l#Hs0Is0H#l#Is0Us0K#l#Hs0ds0b#l#Is0ls0f#l#Is1)s0}#l#Is1Ds1:#l#Is1Ys1U#l#Is1ss1l#l#Is2,s2%#l#Is2?s2>#j#Js2o#j#Ks2|#j#Is3)#j#LS`##"). Qed.

(* [comment removed for export] *)
Ltac zzcrush := repeat (lazymatch goal with
  | |- @eq Z _ _ => unfold lMETA; unfold lcat, lconst; unfold pg, pgo, lRI, lRI'; unfold lden; cbn [fst snd tden app]; rewrite ?uE_var; lia
  | |- _ => first [reflexivity | progress f_equal] end).

Section Dens.
  Variable E : env.
  Let b06 := 4096 * vE E K_B06.
  Let r06 := vE E K_R06.
Scheme kc__4 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

  Lemma DG_noacc_den : forall g brk0z,
    0 <= r06 <= 15 -> b06 mod 65536 = 4096 * r06 -> (g = true -> 4096 * vE E 5 = brk0z) ->
    sivs_den E (DG_noacc g) = zz2ww (PM_NOACC brk0z (Xof g E)).
  Proof.
    ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(r06); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(b06); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Datatypes.true); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.vE); constr:(E); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.sivs_den); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.DG_noacc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.zz2ww); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.pm_meta_map); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.Xof); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b08); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b06); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.lden); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.lMETA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.lcat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.lconst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.siv_den); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.pg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B08); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.pgo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B06); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.lRI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.lRI'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@Corelib.Lists.ListDef.map); constr:(@Stdlib.ZArith.BinInt.Z.eq_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@Corelib.Init.Logic.not); constr:(@kc__4); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__5); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_R06); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.siv_den_empty); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.uE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EVar); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.uE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.uE_var); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.tden); constr:(@stdpp.tactics.f_equal_help); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.siv_den_full); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_META); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_granted); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.PMS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_TID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B04); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B05); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B09); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B10); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B11); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B12); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B13); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B20); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B21); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B22); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B23); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b19r); constr:(@Stdlib.Lists.List.map_app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.pm_region_info); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.RI_lin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.PM_NOACC)|] [|@z; @l; @p; @s; @C; @b; @m; @n; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__sat07; @heq_b06; @heq_r06; @H; @__sat1; @Z0; @e; @__sat0; @y; @x; @__p2; @NZ; @g; @BRK; @__sat5; @H4; @REL; @HR; @brk0z|] "#4E#2$\#6#E#^$(##$)$'#9#5#$$2#%#(#'#C#)$4#2#:#@#&#w#j#|$1$:#e#g$?#=$K#O#V#U#u#y#}$/$0#S#T$H#?#G#P#W#X#f#h#i#r#v#x$#$5#,$<#[$E$G#*$^#N#M#a#l#n#m#t#~$$$&$3$6$8$9$7$;$D$F$I#1#o$M$L#+$P$Q$R$S$T$U$V$W$X$Y$Z$[$\$O$N$]$_$`$a#>#A#J#I#\#R#]#b#<$C#H#s#B$B#8$+$*#D$,#k#p$%#;$.#Z#`$-#7#L#_#c#{#z#F#Y#Q$>$@$A$J#K#d#q$=U$0&$1$#K'$2%#J&$3%$4%$5&#\%$6&$7&$8$$9+$:)$;%$<%$=%$>%$?'$@*$A%$B&$C'$D%$E+#J%#K&$F$$G%$H%$I%$J&#'$$K%$L%$M$$N%$O&$P%$Q$$R$$S$$T$$U%$V%$W&$X$$Y$$Z'$[%4JS%.S0.#.#>#4S%#D(#$S0$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#>#VS=S&#>)2#S%#C%##KS'QJS>J#J#J#J#7D#2,##C#S'k##+#$2$#$#$#.#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#>#&#S&(#s#%USQs#4USR#E##Q#US?OVS2D#ECCVS3ODVS4P#%CC#s#0US@%$B$#$#>#%CC'#USA+(G#%CC$#K/'0$#'1(#'2/#Q3&Gs#?.s#,$#$#$#$#$#$#$#$#$#$#$#$#>#&9#@2#($3%CC4#'s#'#:nK#$##7&#%###;.s#d.#.#.#.#.#.#.#.#.#.#.#$#.#.#.#$#$#$#$#$#$#$#$#$#$#$#$#>#$s#?$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#>#%CC6#'s#Z#s#M*s#[s#5#*s#\s#L#L##s#as#_#j#$C#FPUSSs$0A#$%EE%#,EE#)D#+s#l#-EE&)D#(#&+s#p#%s#ps#p'#Ks#p's#q$#RS-VSBs#gS-%EE$#GD#RS.%EE#SCGD#VSBs#US.%EESD#GD#ECS)Q#EC#K%%C%s#9#.s$V$#$#$#.#.#.#.#.#.#.#.#.#.#.#.#$#.#.#.#$#$#$#$#$#$#$#$#$#$#$#$#>#%Cs#'#s#%%s#'s#'s#%#GD#*s$I#s#7*s$Js#-#*s$Ks#1#*s$Ls#5#*s$MG#7DS-2s$v#%CC#s$D7DS.2s$y#(s$V#%CC$#'s$Q#s$D's$R(#'s$Ss$P#&s$[s%#&)s$5@$#($%%CC&#'s$Y#s$LnK#$##s$I&#%###s$M*s$[#s#_*s$\+#L##s$a7#j#%s$b#,EEs#N)D#+s$h#-EEs#Q)D#(#&+s$l#%s$ls$l'#'s$l#s#ZFOAs#g#%EE$#,EE#)D#+s$t#-EE&)D#(#&+s$x#%s$xs$x'#'s$x#s#f*s$yGs#0*s$z$##s$z#<j#%s${#,EEs#d)D#+s%%#-EEs#g)D#(#&+s%)#%s%)s%)'#'s%)#s#s*s%*Gs#>*s%+=#*s%,2##s%,#s#*j#%s%-#%s#kEs#is#G,EE#)D#+s%4#-EE&)D#(#&+s%8#%s%8s%8'#'s%8#s$&*s%9Gs$'*s%:s#y#*s%;4#*s%<s#.#*s%=s####s%=#s#;j#%s%>#,CCG+s%C#-CCG+s%E#%s%Es%E%#j#&s%A#VS3PDVS4S'#%CC#s%o's%E#s#Q9s%Fs%J'#9s%Gs%K(s#J*s%L$#*s%M7s$;*s%Ns$1#*s%Os#(#*s%Ps#B#*s%Qs#7##s%Q#Gj#%s%R#9s%Ps%T1s#T9s%Qs%U2s$U*s%V$#9s%Ss%W4s#^*s%X#G#s%X*#j#%s%Y#VSTS%J#CS%JUSU#VSV$#&S&s%;@s#f#($s#g%CCs#h#'s%_#s%RnK#$##s%O&#%###s%S9s%as%eB##s%es$I#j#'+##s%gG%j#%s%h#:KG#K-GnK#$##s%WL#%#+#s%[9s%is%ms#*##s%ms$\#k#(&#j#)K##K3Q@LG#K#Q1NLk##$#1LG@NL#K#Qk##%#D'#1S'Nk##&#j##%#@S'N#K#Qk##.#j###Lj##/#VSWLGYSE1-)$#j#*C#j#+C#k#*C4k#+C#WGs$3s#,L1s$4s#-7DS5:C##CS%$m#$#:Cs$?#CS&s$@m#$#VSFS&s&_4JS&4Js&a4Js&ak##$#k##&#VS6Cs&_VS6CS>HC#$I#S*VSG&#KS('S($#QS(USXCVSHCNXS7C#N$XS7C%L#USYCUSZC?Cs&O.s'(VS8C#8C%#?Cs&uVS8CS0WS9C$#BC&#8C#&?Cs&/8C*#5C%S+#6/IFFH#MUS[F?CJ5C,S##63IFFH#MZSI4IFFHP;5IFFH$'#;6IFFH)(#VS\7H:KQVS]GN#K#Qm$%#WS^CJLXS_GN$#l#,*)#l#-A@#l#.s#'s#&#j#/C#j#0C#j#1S$#&s&pL2s'7G($#&#s'9&Ls&K1$##CLJk###Pk##%#k#/C#k#0C#k#1S$#9s&ss&ws$4s#r#s&ws%f#YG#S&S%PSJl#22&#l#3s#Gs#B#l#4s#Is#J#l#5s#Ms#N#l#(s#Ss#R#l#6s#Ws#U#j#(s#m##Ks$#S,9s&~s'&s$?s&q:s'&#j#(%#Ss#s'#LU#Gl#(s#{s#z#l#)s$*K#&?J&s&f#USKs']MS5TD#2%#&#J&s#&#&s&m#4*#j#$C#&s%DJ&s&q#2-G&#J&s%H#&s&u#4'#j#$C#VSFs%Ls'i4Js%MVS=s%Ns'k4J#k##s#j#k##&#VS6Cs'hHCs#h#I#S*VSGs#j#'S(#s#gXS7Cs#dLs#eVS8Cs()5C#S#s#S6s#cIFFH#M8Cs#]s#U8Cs#[#?Cs#$WS9C#(8C#s#Y8Cs#b#8Cs#`#5C(S/#6s#lIFFH#M;s#mIFFH,s#_#l#,#s#Ys#Sl#-1s#p#l#.3s#v#j#/C#j#0C#2s()L&#J&s'<#2s#4N&#J&'#&s'@#4'#k##s#S#k#/C#k#0C#WGs$<s%vNl#2/$#l#7s#-s#(#NDs#>ODS50Cs$As#1%$#MS.ND#ODS.0Cs&#s#=&$#%CS)s(>&%CS)s#Gs#F's&W#s&T's&X%#%Cs&Xs'S#'s&Z's&W%Cs&Zs'U#%EE%#-EE#,Cs&]#-Cs&^$3D#&%#,EE(,Cs&b#-Cs&c$3D#&%#4(#m#6#-EEs&k)D#,EEs&m)D#4%#m#(#WS`Ds&q#0s(1s&|s%'s#ds&q#j#8s%5#U#Gj#9s%7#+s(8*(-++s(:#%s(:s(:%#'s(:#s'(#s(:#s%,k#(s%/#j#)K#)DSD+s(A#)Ds'%(#%+s(D#%s(Ds(D&#<s(D#&s(Js&Q2s(ms$u($#&#s(o+s(K#(s&O$+s(M#%s(Ms(M%#<s(M#k##s(Ms(MUS:s(Ok##s(P$:#$=s(Ss(S5=s(Ts(T,k##s(Us(TVS;s(Vs(Vk##s(W$:#$USLs(Zk##Cs(Z:#$#Cs$(5j#$C##Cs#~7j#$C#8Cs$ss$mWS9Cs$ps#rBC$#8C#s$r5Cs#lS##6s$yIFFH#Ml#,#s$es$_l#-s#ys$|#l#.s%(s%&#j#/C#j#0C#2s$=L&#J&s$^#&s(I#&s(ss$`(#s#o&#s);#C&#k#/C#k#0C#VGs%Gs'%l#2.$#l#:s$8s$3#0Cs%J;#s#is#h0Cs')>#s#fs#e,Cs'Zs#`-Cs'[s#a3D#&%##C#s#7m#(#)Ds#f#C#s#:m#%##Cs#Fs#<m#$#m##$m##%/Cs)+s#0s#0s#Js#@s#.#/s),s#5s#4s#4s#Js#@s#2#(s$\s$U#C#s#Aj#$C#(s$Ts$P#C#s#Dj#$C#BCs$@s$;8Cs%As%>BC#s#05C%S##6s%KIFFH#Ml#,#s%7s%1l#-s$Ks%N#l#.s%Vs%T#j#/C#j#0C#(s$ls#-&s%/s(u(#s#,#C%#k#/C#k#0C#l#2)#s#,l#:s$as$\#0Cs%s5#s$6s$50Cs'R9#s$3s$2,Cs('s$+-Cs((s$,3D#&%#(#s#,#C#s#_m#)#)Ds$2(#s#-#C#s#cm#&##Cs#ns#em#$#m##$m##%/Cs)Vs#[s#[s#rs#is#Y#/s)Ws)Vs#bs#as#rs#is#-#/s)Ws#gs#fs#fs#rs#is#d#:s)Ws(F/s)Xs)Xs#ss#js(Gs(G$##s)Ys#~s%Am#$#j#(s&I##Ks&IS,4LNk##$#4GL#Ks&HS,k##$#D&#4NS'k##&#j##%##Ks&GS,k##,#j###Lj##-#VSaLGYSE/,($#j#;C#j#<C#k#;C2k#<C#4s&ps'wVSbCs*=WSMC#s&9HCs%0#I#S*'S(#s&75Cs&%S/s&'6s&1IFFH#MZSNs&2IFFHs%}5Cs&$S/s&-6s&4IFFH#M[S<s&5IFFH#s&#ZSIs&6IFFHO;s&7IFFH$s&)#;s&8IFFH(s&*#;s&9IFFH*s&+#l#,#s&%s%{l#-s&=s&<#l#./s&B#j#/C#j#0C#j#1S$#j#=S$#4s%ws%xk##s%vSc4JND#Pk###Rk##&#k##(#k#/C#k#0C#k#1S$#k#=S$##s*6s$[s%o[G#s*sS&S%PSJSdl#20%#l#3s&bs&]#l#4s&ds&e#l#5s&hs&i#l#(s&ns#*#l#6s#.s#,#j#(s%x#Ss$as#B#LU#Gl#(s'6s'5#l#)s'AK#1s%ms%tj#$C#1s%gs%kj#$C#WSMCs#4s%`HC#s&jI#S*'S(#s&hZSNs&aIFFHs%\5Cs&SS/s%_6s&cIFFH#M[S<s&dIFFH#s&R5Cs%YS+s%^6s&fIFFH#M;s&gIFFH%s&Y#;s&hIFFH)s&Z#l#,#s&Ts&Nl#-s%hs&k#l#.-s&q#j#/C#j#0C#j#1S$#Ds#.S'2s+&N2s&/S'&#J&%#&s*;#&'J&s*=#1%#k##+#k##s#9#k#/C#k#0C#k#1S$#4s';s+HYG#s'<s(vNSOl#23%#l#:s&-s&(#0Cs'?s#'#s%^s%]0Cs(zs#*#s%[s%Z1s%Hs%Mm#$#1s%Ds%Fm#$#PDs)V#0s*rs%;s'hs#2s)V#j#>s'u#U#Gj#+s'w#ZSes'ys'xs'ns%D#Gl#'s'{s'x#FRAs)s#%EE$#,EE#)D#+s+$#-EE&)D#(#&+s+(#%s+(s+('#'s+(#s)r*s+)Gs(:*s+*s(_#*s++s(y#*s+,&#VS3RDVS4O#%CC#s+V's+,#s)89s+-s+1s(J#*s+2#s(:#s+2)#j#%s+3##KGQ#Cs+SRk##$#FL)D#+s+<#As*4%)D#(#&+s+@#%s+@s+@'#)Ds*,+s+C#)Ds*-(#%+s+F#%s+Fs+F&#)Ds*.+s+I#)DSC(#%+s+L#%s+Ls+L&#)Ds**+s+O#)Ds)f(#%+s+R#%s+Rs+R&#'s+R#s*@*s+Ss(L#'s+T+#'s+U2#'s+V9#7DS12s,##nK#$#?CL#%#J##nK#$##CL#%#R##+s+]#+s+^s,'%s+^s+^$#+s+`s)m+s+as+S%s+as+a$#+s+cs)m+s+ds)m%s+ds+d$#+s+fs*y+s+gs*g%s+gs+g$#'s+g#s*U*s+hs(r#'s+i(#'s+j,#'s+k0##s+k8#k#@s#8#j#)K##KQQ#Cs,1Ok##$#Cs'qFQ)D#+s+w#As*o%)D#(#&+s+{#%s+{s+{'#<s+{#+s+~R%s+~s+~#s##<s+~#@s&9s*(%CCs&:s&8's+}#s+pnK#$##s+m%#%###s+q9s,#s,'s)@#*s,(#s#4's,)s#<#'s,*s#C#(s&Bs*7+s,.#%s,.s,.s#*#*s,.)s#%'s,/$#'s,0s#.#=s,2s,2:=s,3s,34&Js'd#C#SOj#$C#USKS0VSfC#WSgC#s(ZHC#s(ZI#S*'S(#s(X5Cs(JS#s'N6s(RIFFH#M8Cs(Ds'M5C#S#s'Q6s(UIFFH#M;s(VIFFH&s(H#l#,#s(Bs(<l#-s'Vs(Y#l#.+s(_#j#/C#j#0C##Cs(9L&Js'G#C#Nk##%#k#/C#k#0C#WGShs,kNl#2*$#l#As'ms'h#Ms,oND#ODs,q0Cs,q@&$#%CS)s,{&'s+7#s+4%Cs+7J#,Cs+8#-Cs+9$3D#&%##C#Rm#+#)D)#C#Rm#%#Rs-#)D##C#Rm#&#m##$#Cs#ORm#$#/Cs,hs&ms&ms#QRs&k#/s,is&rs&qs&qs#Qs#Js&o#&s-4J&#s(?(#s#:#C#s-7j#$C#VSHCL8Cs)#s(u8C#s(#BC#s#55C#S#s)&6s),IFFH#Ml#,#s(ts(nl#-)s)/#l#.s)7s)5#j#/C#k#/C.Cs-;l#2%$#l#As(=s(8#0Cs->1#s#-s#,%Cs+^s-Hs+\,Cs+_#&#s#*-Cs+a%*s+c#s#+%Cs+c%#,Cs+d#-Cs+e$3D#&%#(#s#/#C#s-Sm#/#)D*(#s#0#C#s-Wm#&#,Cs+os#0&3#-Cs+qs#2*s+s3#%Cs+s%#)D#(#s#5#C#s-`m#+#As,4s#9)D#(#s#:#C#s-em#'##Cs$&s-gm#$#/Cs-Cs'Hs'Hs$(s-is'F#/s-Ds-Cs#ps#os$(s$Es#9#/s-Ds'Ts'Ss'Ss$(s$%s'Q#<s-Es$^<s-Fs$D=s-Hs-Hs$d=s-Is-Is$H#Cs#ts+Xj#$C#5Cs#kS#s)Y6s)aIFFH#Ml#,#s)Ms)Gl#-s#>s)d#l#.s)ls)j#j#/C##Cs#|s)Ck#/C#Cs+cl#2&$#l#As(ss(n#MS-ND#ODS-0Cs+i1&$#%CS)s.%&'s,=#s,:%Cs,=J#,Cs,>#-Cs,?$3D#&%##C#s+pm#+#)D)#C#s+sm#%##Cs%(s+um#$#m##$m##%/Cs-ks'ps'ps%,s+ys'n#/s-ls'us'ts'ts%,s$ks'r#&s-`s)A(#s$<#C#s-bj#$C#?Cs-d8C#s)$BC#s$65C#S#%6s*-IFFH#Ml#,#s)us)ol#-s#fs*0#l#.s*8s*6#j#/C#k#/C-l#2$#s#)l#As)=s)8#0Cs,0/#s#'s#&%Cs,^s-qs#$,Cs,_#-Cs,`$3D#&%#(#s#$#C#s-wm#*#)D*(#s#%#C#s-{m#&##Cs%Hs-}m#$#m##$m##%/Cs.2s(7s(7s%Ls.%s(5#/s.3s.2s#Is#Hs%Ls%1s#%#/s.3s(Cs(Bs(Bs%Ls%1s(@#<s.4s%G<s.5s$f=s.7s.7s%M=s.8s.8s%4#Cs$cs,Dj#$C#Cs,Gl#2s#Is#G#l#As)Zs)U#0Cs,J&#s)+s)*%Cs,{Js)$,Cs,|#-Cs,}$3D#&%##C#s,Om#)#)D)#C#s,Rm#%##Cs%`s,Tm#$#m##$m##%/Cs.Ms(Rs(Rs%ds,Xs(P#/s.Ns(Ws(Vs(Vs%ds%Js(T#&s.Ss)x(#s$z#C#s%'j#$C#&s.Ws)t&Js)y($##C#s%,j#$C#8Cs*ks)aBC#s$xBCs(Vs*g5C$S##6s*pIFFH#Ml#,#s*\s*Vl#-s)ps*s#l#.s*{s*y#j#/C#j#0C#&s.fs(S(#s%1(s(Rs*U#C$#k#/C#k#0C#l#2)#s(Ql#As**s*%#0Cs+<5#s)[s)Z0Cs,w;#s)Xs)W%Cs-Ls.ps)S,Cs-M#-Cs-N$3D#&%#(#s#0#C#s%Hm#*#)D*(#s#1#C#s%Lm#&##Cs&0s%Nm#$#m##$m##%/Cs.|s)%s)%s&4s%Rs)##/s.}s.|s#Hs#Gs&4s%Rs#1#/s.}s)1s)0s)0s&4s%Rs).#:s.}s%R/s.~s.~s#Ms#Ls%Ys%S$#/s/#s/#s$=s$<s%Ys%Ss#O#/s/$s/$s%ds%as%Ys%Ss$?#l#@s%ns%p#j#@s%p##KS,Qk###s%sFS,)D#+s/.#As.&%)D#(#&+s/2#%s/2s/2'#<s/2#+s/5s&9%s/5s/5#s&6<s/5#=s/7s/7,=s/8s/8&#Cs%cs&>j#$C#Cs&Al#2s$Is$G#l#As*Zs*U#MS1ND#ODS10Cs&G)&$#%CS)s/h&'s.$#s-}%Cs.$J#,Cs.%#-Cs.&$3D#&%##C#s&Nm#+#)D)#C#s&Qm#%#RS1)D##C#s&Um#&#m##$#Cs#)s&Xm#$#/Cs/Us)Zs)Zs#+s&Zs)X#/s/Vs)_s)^s)^s#+s#$s)\#l#2s%=s%<>l#As*us*p#0Cs&_s%I#<;&s%97*s.<s%87%Cs.<$#,Cs.=#-Cs.>$3D#&%#(#;#C#s0,m#,#)D*(#<#C#s00m#&#,Cs.H<&s%H#-Cs.J>*s.Ls%H#%Cs.L%#)D#(#A#C#s09m#+#As.is#%)D#(#s#&#C#s0>m#'##Cs#Hs0@m#$#/Cs/xs)}s)}s#Js0Bs){#/s/ys/xs#Ds#Cs#Js&zs#%#/s/ys*-s*,s*,s#Js#Gs**#/s/ys/ys#Js#Gs&Rs&L#s#Xj#@s#T#Ss&ls#W#OU#L)Ds-o+s0%#)Ds-p(#%+s0(#%s0(s0(&#'s0(#s'17DSi7DSj2s0R#7DSk2s0T#7DSl2s0V#7DSm2s0X#7DSn2s0Z#7DSo2s0\#7DSp2s0^#7DSq2s0`#USrO7D#2s0c#USsO7D#2s0f#UStO7D#2s0i#USuO7D#2s0l#nK#$#?CO#%#J#s'LeSv@O><s.Ss.V:86420-*'$#USw#USx$nK#$##C$#%#P##+s0M#%s0Ms0M#s'N's0M#s'A#s0Ms#(#m#s#0#+s0Rs0J%s0Rs0R#s'S's0R#s'F#s0Rs#-#m#'#*s0Us-Ns-f*s0Vs./#*s0Ws.I#*s0Xs.>#*s0Ys-`s-a#s0Y$#m#)#0s0[s-Us(*#s/?Gl#Bs(Cs-U#YSPs0Zs0^s-ws.^s/^0s0^s-gs-c$s-r#*s0\s-us._9s0]s0as-z#YSPs0^s0bs-{s-ws.a0s0bs-us-n&$#*s0ds/Qs-rL'#s0e$#m#&#GDs.;?Cs/~8C#s,p?Cs/(8C#s,r5C%S+#6s-'IFFH#Ml#,#s,os,il#-s-.s-*#l#.s-2s-0#&s0+J&s/0J1$#l#2&#G,Cs/Ws.H-Cs/Xs.I3D#&%#,Cs/[s.I-Cs/\s.J3D#&%#1'#m#,#1s.Qs.Nm#$#PDs.U#0s1&s.Ms.F>=#1s'Ss%8j#$C#1s%5s%6j#$C#HCs)ss-MI#S*'S(#s-K?Cs1k5Cs,BS/#6s-FIFFH#M[S<s-GIFFHs-5#5Cs'SS+s%:6s-IIFFH#M;s-JIFFH%s-<#l#,#s-6s-0l#-s,Js-M#l#.,s-S#j#/C#j#0C#j#1S$#4Ls1xDN#&s1Cs,91s'U#k##%#k#/C#k#0C#k#1S$#4Js-sXG#s-ts/RPl#2-%#l#:s,es,`#0Cs-w?#s,:s,90Cs/VB#s,7s,6%EEs%js%=,EE#,Cs0-#-Cs0.$3D#&%#-EE(,Cs02#-Cs03$3D#&%#1(#m#/#1s/7s/4m#$#PDs0@#0s1Ys/3s/.s#5s0@#5Cs'{S+s&H6s-qIFFH#Ml#,#s-]s-Wl#-s'Ns-t#l#.s-|s-z#j#/C#1s(0s&Sk#/C#TDs&kC#l#2'%#l#3s.2s.-#l#4s.4s.5#l#5s.8s.9#%EEs&ks&J,EE#,Cs0L#-Cs0M$3D#&%#-EE(,Cs0Q#-Cs0R$3D#&%#1(#m#/#1s/os/lm#$#PDs0b#0s1xs/ks/[As0b#GDs0qk##s)Hs(i%EEs)Fs)C,EE#)D#-EE%)D#1%#k#@)#j#)K##Cs2EPk##s(t#5Cs(JS+s't6s.@IFFH#Ml#,#s.,s.&l#-s'ys.C#l#.s.Ks.I#j#/C#1s([s($k#/C#TDs(@C#l#2'%#l#3s.]s.X#l#4s._s.`#l#5s.cs.d#%EEs(@s'p,EE#,Cs0w#-Cs0x$3D#&%#-EE(,Cs0|#-Cs0}$3D#&%#1(#m#/#%EEs)0s)-,EE#)D#-EE%)D#1%#m#)#j#@s#%#k##s&'s#'TDs%oC#l#2s##A#l#3s.ys.t#l#4s.{s.|#l#5s/#s/$#%EEs%os%W,EE#,Cs17#-Cs18$3D#&%#-EE(,Cs1<#-Cs1=$3D#&%#1(#m#/#%EEs&9s&6,EE#)D#-EE%)D#1%#m#)#j#@=#Ss#D?#PU#GPDs1b#0s2ks1Ys0gs#Qs#P#EEEEs1Ns1NK#'$s1+#'&s1U#''s1Y#'(s1]#')s1k#VS2D##s2u#s$om#-#US?PVS2D##s2y#s$sm#&#US@s08%CC#s2qUSAs0:(s3&#%CC$#'s2}#s2p's2~'#'s3#s0=#&(s2`@s1/#($s10%CCs11#'s3(#s2wnK#$##s2t&#%###s2x*s3*#s2.*s3+*#L##s306#m#5#USys0K:C4YSzs0MS&S%#L0Cs39s21&%#VS{S's0OL##s38>#m#&#j#@s3V#j#Cs3a#j#Ds3w#j#EC#j#?K##"). Qed.

  Lemma DG_lazy_den : forall g sp0z,
    0 <= r06 <= 15 -> b06 mod 65536 = 4096 * r06 ->
    sivs_den E (DG_lazy g) = zz2ww (PM_LAZY sp0z (Xof g E)).
  Proof.
    ltac2:(KReplay.runc [|constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(r06); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(b06); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.sivs_den); constr:(E); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.DG_lazy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.zz2ww); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b22); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.Xof); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b08); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.ps_b06); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.lden); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.lin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.pg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B22); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.pgo); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.siv_den); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B08); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_B06); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.lRI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.lRI'); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.expr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.vE); constr:(@Corelib.Lists.ListDef.map); constr:(@Stdlib.ZArith.BinInt.Z.eq_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@Corelib.Init.Logic.not); constr:(@kc__4); constr:(@Corelib.Init.Logic.eq_refl); constr:(@kc__5); constr:(@Corelib.Init.Datatypes.true); constr:(@kc__1); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.ltb_lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.K_R06); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.false); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.siv_den_empty); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.uE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3.AX2.EVar); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPlanSound.APS.uE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.uE_var); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AxSymExec3Sound.AX2S.tden); constr:(@stdpp.tactics.f_equal_help); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainVM.siv_den_full); constr:(@Stdlib.Lists.List.map_app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.pm_region_info); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.RI_lin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.PM_LAZY)|] [|@z; @l; @p; @s; @C; @b; @m; @n; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__arith; @__sat07; @heq_b06; @heq_r06; @H; @__sat1; @Z0; @e; @__sat0; @y; @x; @__p2; @NZ; @H4; @REL; @HR; @sp0z; @g|] "#3k#1$F#5#J#Y$%##$&$$#8#$#4$/#%#1#9#?#&#'#r$.$1#c#l#_#`#y$<$7#<#p$-$:#N#O$E#)#>#K#Q#P#R#S#a#b#m#q#u#v#s#|#z$2#,#k#V$B$D#($H#H#G#f#h#g#o#{#}$#$0$3$5$6$4$9$8$A$C$F#0#i#*$I$J$K#@#;#=#D#M#C#W#X#]#n#B$@$?#7$($'$)#A#:#e#j$+#^#~#U#d$*$G#6#F$;#T#L#[#Z#\#x#w#E$=$>#I#t$,U#v$#w$#C'#x&#y%#z&#B&#X%#{%#|%#}&#~&$#%$$)$%+$&%$'%$('$)*$*&$+%$,$$-'$.%$/%$0%$1+$2%#B%#C&$3%$4&$5&$6%$7%$8$$9$$:$$;$$<$$=%$>&$?%#'$$@$$A%$B%$C%$D%$E%3JP$S.$#$#8#3P#D(##S.##############################8#VS6Q#8)7#P&C%##(######$#################################8#'#Q+#;USMs#*USN#E##O#US7S#RD#ECCVS8S#DUS9##@####8#%CC'#US:)%CC#%US;++G#%CC$#G/)0$#)1(#)2+#O3'Gs#5$s#,########################8#'9#>2#+$3%CC4#)s#'#:nL#$##7&#%###;$s#T######$#$#$#$#$#$#$#$#$#$#$#$###$#$#$#########################8##s$'$#$#$#$#$#$#$#$#$#$#$#$#$###############################$#########################8#%CCs#.#$s$K$#$#$#$#$#$#$#$#$#$#$###$#$#$#########################8##s$2##################################8#%CC6#$s%&$#$#$#$#$#$#$#$#$#$###$#$#$#########################8#8s#.%CC$#)s$i#s$\)s$jB#)s$ks#T#(s$ls$F#(s$ms$]#H#&s$rs$p#j#$C#IRJ#Ks$m$%EE$#-EE#,D#*s$}#.EE&,D#+#&*s%%#%s%%s%%'#Gs%%)s%&$#JS)Ks$zS)%EE$#<D#JS*%EE#S<<D#Ks$fS*%EES=#<D#ECS'O#EC#G%%C%s$F#$s%Y$#$#$#$#$#$#$#$#$#$#$#$#$#$#$###############################8#%Cs#&#s#$%s#&s#&s#$#<D#%Cs#)s#}s#'%s#)s#)#s#'<D#%Cs#,s#Ps#*%s#,s#,#&<D#(s%_#s#<(s%`'#(s%a+#(s%bs#4#(s%cs#8#(s%ds#<#(s%eG#IS#AD#7s&)#%CC#s%_ADS)7s&,#%CC#s%bADS*7s&/#+s%r#%CC$#)s%m#s%`)s%n(#)s%o,#'s%ws&5')s%Q>$#+$%%CC&#)s%u#s%hnL#$##s%e&#%###s%i(s%w#s#j(s%x+#H#&s%};#j#%s%~#-EEs#Y,D#*s&(#.EEs#\,D#+#&*s&,#%s&,s&,'#)s&,#s#eJs#%Ks&$s#&%EE$#-EE#,D#*s&4#.EE&,D#+#&*s&8#%s&8s&8'#)s&8#s#q(s&9Gs#4(s&:$#&s&:#<j#%s&;#-EEs#o,D#*s&A#.EEs#r,D#+#&*s&E#%s&Es&E'#)s&E#s#~(s&FGs#B(s&G=#(s&H2#&s&H#s#*j#%s&I#%s#vEs#Ps#t-EE#,D#*s&P#.EE&,D#+#&*s&T#%s&Ts&T'#)s&T#s$1(s&UGs#T(s&Vs#\#(s&Ws$)#(s&X5#(s&Ys#/#(s&Zs#$#&s&Z#s#<j#%s&[#%s$,Es$*s#e-EE#,D#*s&b#.EE&,D#+#&*s&f#%s&fs&f'#)s&f#s$C(s&g5s#f(s&hG#(s&is$;#(s&js#'#(s&ks#A#(s&ls#6#&s&l#s#Nj#%s&m#%s$>Es#qs#t-EE#,D#*s&t#.EE&,D#+#&*s&x#%s&xs&x'#)s&x#s$U(s&yGs$V(s&zs#(#(s&{7#(s&|s$N#(s&}s#:#(s&~s#T#(s'#s#I#&s'##s#aj#%s'$#-CCG*s')#.CCG*s'+#%s'+s'+%#j#&s''#ADs$q7s'J#%CC#s'$)s'+#s#w9s',s'0'#9s'-s'1(s#p(s'2$#(s'39s$l(s'4s#>#(s'5s#-#(s'6s$d#(s'7s#P#(s'8s#j#(s'9s#_#&s'9#Gj#%s':#9s'8s'<3s#|9s'9s'=4s%,(s'>$#9s';s'?6s$*(s'@#G&s'@*#j#%s'A#VSOPJ&CPJUSP#VSQ$#'Qs'#>s$2#+$s$3%CCs$4#)s'G#s':nL#$##s'7&#%###s';9s'Is'Ms#$#&s'Ms$|#j#'+#&s'OG%j#%s'P#:LG&L-GnL#$##s'?K#%#+#s'C9s'Qs'Us#,#&s'Us%3#k#(&#j#)L#&L3S(>KG&L#S(/NKk##$#/KG>NK&L#S(k##%#D'#/RNk##&#j##%#>RN&L#S(k##.#j###Kj##/#VSRKGYS>1-)$#j#*C#j#+C#k#*C4k#+C#WGs$[s#,K/s$\s#-ADS/:C#&CP$m#$#:Cs$g&CQs$hm#$#VS?Qs(=3JQ3Js(?3Js(?k##$#k##&#US@SASC#SCSALC#$M#S+VSB&#GS$)S$$#OS$USSCVSCCNXSDC$K#USTCUSUC;Cs(7TCs(h6C$#;Cs(RTCS.WS0C$#BC&#6C#&;Cs'r6C*#4C%S%#5.IFFH#MUSVF;CJ4C,S&#52IFFH#MZSE3IFFHS#=4IFFH$'#=5IFFH)(#VSW6H:LS(VSXGN&L#S(m$%#WSYCJKXSZGN$#l#,*)#l#-@?#l#.s#%s#$#j#/C#j#0C#j#1O#'s(WK7s(pG+$#'#s(r'Ks(2/$#&CKJk###S#k##%#k#/C#k#0C#k#1O#9s(Zs(^s$5s#q&s(^s&<#YG#QPS#SFl#22&#l#3s#Fs#A#l#4s#Hs#I#l#5s#Ls#M#l#(s#Rs#Q#l#6s#Vs#T#j#(s#l#&Ls#~S-9s(es(is$@s(X:s(i#j#(%#XSGs#r'#KU#Gl#(s#zs#y#l#)s$)L#'?J's(M#US[s):FS/VS1D#7%#'#J's#&#'s(T#3*#j#$C#'s%kJ's(X#7-G'#J's%o#'s(\#3'#j#$C#VS?s%ss)F3Js%tVS6s%us)H3J#k##s#i#k##&#US@s#gSC#LCs#g#M#S+VSBs#i#)S$#s#fXSDCs#cKs#dTCs)c4C#S&s#T5s#cIFFH#M6Cs#^s#V6Cs#\#;Cs#%WS0C#(6C#s#Z6Cs#c#6Cs#a#4C(S,#5s#lIFFH#M=s#mIFFH,s#`#l#,#s#Zs#Tl#-1s#p#l#.3s#u#j#/C#j#0C#7s)cK'#J's)$#7s#5N'#J''#'s)(#3'#k##s#T#k#/C#k#0C#WGs$<s&BNl#2/$#l#7s#.s#)#PDs#?QDS/0Cs$As#2%$#FS*PD#QDS*0Cs&Ks#>&$#%CS's)x&%CS's#Hs#G)s'.#s'+)s'/%#%Cs'/s);#)s'1's'.%Cs'1s)=#%EE%#.EE#-Cs'4#.Cs'5$2D#'%#-EE(-Cs'9#.Cs':$2D#'%#3(#m#6#.EEs'B,D#-EEs'D,D#3%#m#(#WS\Ds'H#0s)us'Ss%'s#es'H#j#8s%5#U#Gj#9s%7#*s)|*+-+*s)~#%s)~s)~%#)s)~#s'[&s)~#s%,k#(s%/#j#)L#,DS=*s*)#,Ds'X+#%*s*,#%s*,s*,&#?s*,#'s*2s&y7s*Ks$u+$#'#s*M*s*3#+s&w$*s*5#%s*5s*5%#?s*5#k##s*5s*5US2s*7k##s*8$:#$@s*;s*;5@s*<s*<,k##s*=s*<VS3s*>s*>k##s*?$:#$USHs*Bk##Cs*B:#$&Cs$)5j#$C#&Cs$#7j#$C#6Cs$ss$nWS0Cs$qs#rBC$#6C#s$s4Cs#lS&#5s$yIFFH#Ml#,#s$fs$`l#-s#ys$|#l#.s%'s%%#j#/C#j#0C#7s$>K'#J's$_#'s*1#'s*[s$a+#s#o'#s*u&C&#k#/C#k#0C#VGs%Gs'Ml#2.$#l#:s$9s$4#0Cs%J;#s#is#h0Cs'Q>#s#fs#e-Cs(1s#`.Cs(2s#a2D#'%#&C#s#7m#(#,Ds#f&C#s#:m#%#&Cs#Fs#<m#$#m##$m##%1Cs*os#0s#0s#Js#@s#.#1s*ps#5s#4s#4s#Js#@s#2#+s$]s$V&C#s#Aj#$C#+s$Us$Q&C#s#Dj#$C#BCs$@s$;6Cs%Bs%?BC#s#04C%S&#5s%KIFFH#Ml#,#s%8s%2l#-s$Ks%N#l#.s%Us%S#j#/C#j#0C#+s$ms#-'s%0s*]+#s#,&C%#k#/C#k#0C#l#2)#s#,l#:s$bs$]#0Cs%s5#s$6s$50Cs'z9#s$3s$2-Cs(Zs$+.Cs([s$,2D#'%#+#s#,&C#s#_m#)#,Ds$2+#s#-&C#s#cm#&#&Cs#ns#em#$#m##$m##%1Cs+>s#[s#[s#rs#is#Y#1s+?s+>s#bs#as#rs#is#-#1s+?s#gs#fs#fs#rs#is#d#:s+?s(y1s+@s+@s#ss#js(zs(z$#&s+As#~s%Bm#$#j#(s&I#&Ls&IS-3KNk##$#3GK&Ls&HS-k##$#D&#3NRk##&#j##%#&Ls&GS-k##,#j###Kj##-#VS]KGYS>/,($#j#;C#j#<C#k#;C2k#<C#3s&ps(CVS^Cs+wWSIC#s&8LCs%0#M#S+)S$#s&64Cs&&S,s&(5s&1IFFH#MZSJs&2IFFHs%~4Cs&%S,s&.5s&4IFFH#M[S4s&5IFFH#s&$ZSEs&6IFFHSK=s&7IFFH$s&*#=s&8IFFH(s&+#=s&9IFFH*s&,#l#,#s&&s%|l#-s&=s&<#l#./s&A#j#/C#j#0C#j#1O#j#=O#3s%xs%yk##s%wS_3JND#S#k###S5k##&#k##(#k#/C#k#0C#k#1O#k#=O#&s+zs$[s%p[G#s,QQPS#SFS`l#20%#l#3s&bs&]#l#4s&ds&e#l#5s&hs&i#l#(s&ns#*#l#6s#.s#,#j#(s%y#XSGs$as#B#KU#Gl#(s'6s'5#l#)s'AL#/s%ns%uj#$C#/s%hs%lj#$C#WSICs#4s%`LC#s&iM#S+)S$#s&gZSJs&aIFFHs%\4Cs&TS,s%_5s&cIFFH#M[S4s&dIFFH#s&S4Cs%YS%s%^5s&fIFFH#M=s&gIFFH%s&Z#=s&hIFFH)s&[#l#,#s&Us&Ol#-s%hs&k#l#.-s&p#j#/C#j#0C#j#1O#Ds#.R7s,`N7s&0R'#J'%#'s,##''J's,%#/%#k##+#k##s#9#k#/C#k#0C#k#1O#3s';s-&YG#s'<s)BNS5l#23%#l#:s&.s&)#0Cs'?s#'#s%^s%]0Cs)Fs#*#s%[s%Z/s%Hs%Mm#$#/s%Ds%Fm#$#CDs*-#0s,Zs%;s'hs#2s*-#j#>s'u#U#Gj#+s'w#ZSas'ys'xs'ns%D#Gl#'s'{s'x#ISKJ#Ks,Y$%EE$#-EE#,D#*s,i#.EE&,D#+#&*s,m#%s,ms,m'#)s,m#s*J(s,nGs(;(s,os),#(s,ps)F#(s,q&#AD37s-4#%CC#s,j)s,q#s)a9s,rs,vs(M#(s,w#s(;&s,w)#j#%s,x#,Ds)O*s,}#,Ds)P+#%*s-$#%s-$s-$&#?s-$#*s-'s)w*s-(s,x%s-(s-($#?s-(#,Ds*`*s-,#,Ds*a+#%*s-/#%s-/s-/&#,Ds*b*s-2#,DS<+#%*s-5#%s-5s-5&#>s%cs)z%CCs%ds%b)s-3#s-&nL#$##s-#%#%###s-'9s-5s-9s(l#,Ds*c*s-=#,Ds*D+#%*s-@#%s-@s-@&#,Ds*E*s-C#+*$*s-E#%s-Es-E%#,Ds*G*s-H#+)$*s-J#%s-Js-J%#)s-J#s+')s-K)#)s-L/#(s-M6#)s-N<#)s-Os###*s-Rs*C%s-Rs-R#s#-*s-Ts*B+s&&s*C*s-V#%s-Vs-V%#*s-Xs,g*s-Ys,=%s-Ys-Y$#*s-[s+}*s-\s+k%s-\s-\$#*s-^s+P*s-_s+P%s-_s-_$#)s-_#s+<)s-`'#)s-a+#(s-bs#+#)s-c0#)s-d5#@s-fs-fs#H@s-gs-gs#C'Js'U&C#s#Sj#$C#VSCCK6Cs(.s'64C#S&s(75s(>IFFH#Ml#,#s(+s(%l#-'s(A#l#.s(Hs(F#j#/C#&C-s'}k#/C#IS5AD#N#l#2(&#l#:s'Ss'N#Fs*qPD#QDs*s0Cs*s5&$#%CS's.>&)s+O#s+L%Cs+OJ#-Cs+P#.Cs+Q$2D#'%#&C#s*zm#+#,D)&C#s*}m#%#&Cs#ms+#m#$#m##$m##%1Cs.2s&Os&Os#qs+'s&M#1s.3s&Ts&Ss&Ss#qs#ks&Q#'s.)s'}+#s#+&C#s.+j#$C#;Cs.-6C#s'_BC#s#,4C#S&%5s(hIFFH#Ml#,#s(Us(Ol#-s#1s(k#l#.s(rs(p#j#/C#k#/C-l#2$#s#)l#:s'ys't#0Cs+:/#s#'s#&%Cs+ps.:s#$-Cs+q#.Cs+r$2D#'%#+#s#$&C#s.@m#*#,D*+#s#%&C#s.Dm#&#&Cs$1s.Fm#$#m##$m##%1Cs.Us&rs&rs$5s.Js&p#1s.Vs.Us#Ns#Ms$5s$1s#%#1s.Vs&~s&}s&}s$5s$1s&{#?s.Ws$+?s.Xs#e@s.Zs.Zs$1@s.[s.[s#h&Cs#Rs+Nj#$C#Ns+Ql#2s#Ks#I#l#:s(:s(5#FS)PD#QDS)0Cs+W)&$#%CS's/%&)s,6#s,3%Cs,6J#-Cs,7#.Cs,8$2D#'%#&C#s+^m#+#,D)&C#s+am#%#&Cs$Is+cm#$#m##$m##%1Cs.us'6s'6s$Ms+gs'4#1s.vs';s':s':s$Ms$'s'8#l#2s#9s#8;l#:s(Rs(M#0Cs+ls#D#98%Cs,Is.o6-Cs,J#.Cs,K$2D#'%#+#6&C#s.um#*#,D*+#7&C#s.ym#&#&Cs$[s.{m#$#m##$m##%1Cs/.s'Ks'Ks$_s/#s'I#1s//s/.s#3s#2s$_s$f7#1s//s'Ws'Vs'Vs$_s$<s'T#?s/0s$Z?s/1s$:@s/3s/3s$`@s/4s/4s$?&Cs$+s,$j#$C#Ns,'l#2s$$s#~#l#:s(os(j#0Cs,*&#s(?s(>%Cs,fJs(8-Cs,g#.Cs,h$2D#'%#&C#s,/m#)#,D)&C#s,2m#%#&Cs$ss,4m#$#m##$m##%1Cs/Is'fs'fs$ws,8s'd#1s/Js'ks'js'js$ws$Us'h#'s/Os)1+#s$B&C#s$Wj#$C#'s/Ss)-'Js)2+$#&C#s$\j#$C#6Cs*#s(uBC#s$GBCs'js)|4C$S&#5s*(IFFH#Ml#,#s)qs)kl#-s)(s*+#l#.s*2s*0#j#/C#j#0C#'s/bs'g+#s$U+s'fs)j&C$#k#/C#k#0C#l#2)#s'el#:s)?s):#0Cs*P5#s(os(n0Cs,W;#s(ls(k%Cs-7s/ls(g-Cs-8#.Cs-9$2D#'%#+#s#0&C#s$xm#*#,D*+#s#1&C#s$|m#&#&Cs%Cs$~m#$#m##$m##%1Cs/xs(9s(9s%Gs%&s(7#1s/ys/xs#Hs#Gs%Gs%&s#1#1s/ys(Es(Ds(Ds%Gs%&s(B#:s/ys$v1s/zs/zs#Ms#Ls%0s$w$#1s/{s/{s$'s$&s%0s$ws#O#1s/|s/|s%[s%Ws%0s$ws$)#(s/~s+3s+K(s0#s,<#(s0$s,V#(s0%s,K#(s0&s+Es+F&s0&$#m#)#0s0(s+:s%j#s-WGl#?s&(s+:#YSLs0's0+s+^s,ks-v0s0+s+Ls+H$s+Y#(s0)s+\s,l9s0*s0.s+a#YSLs0+s0/s+bs+^s,n0s0/s+\s+S&$#(s01s-is+WH'&s02$#m#&#<Ds,$;Cs.*6C#s*V;Cs.\6C#s*X4C%S%#5s*hIFFH#Ml#,#s*Us*Ol#-s*ns*k#l#.s*rs*p#'s.3J's.dJ/$#l#2&#G-Cs-os,1.Cs-ps,22D#'%#-Cs-ss,2.Cs-ts,32D#'%#/'#m#,#/s,:s,7m#$#CDs,>#0s0Os,6s,->=#<Ds,R;Cs/c6C#s*r;Cs-]6C#s*t4C%S%#5s+(IFFH#Ml#,#s*qs*kl#-s+.s++#l#.s+2s+0#'s/lJ's-eJ/$#l#2&#G-Cs./s,_.Cs.0s,`2D#'%#-Cs.3s,`.Cs.4s,a2D#'%#/'#m#,#/s,hs,em#$#CDs,l#0s0ks,ds,\>=#<Ds-$4Cs#7S%=5s+@IFFH#Ml#,#s+-s+'l#-s+Fs+C#l#.s+Js+H#/s#5:l#2$#G-Cs.Es-+.Cs.Fs-,2D#'%#-Cs.Is-,.Cs.Js--2D#'%#/'#m#,#/s-4s-1m#$#CDs-8#0s1%s-0s-(87#/s%zs$;j#$C#/s$8s$9j#$C#LCs(.s+cM#S+)S$#s+a;Cs1`4Cs*YS,#5s+]IFFH#M[S4s+^IFFHs+M#4Cs&%S%s$=5s+`IFFH#M=s+aIFFH%s+T#l#,#s+Ns+Hl#-s*as+d#l#.,s+i#j#/C#j#0C#j#1O#3Ks1mDN#'Js*T's1Cs*Q/$#k##&#k#/C#k#0C#k#1O#3Js,/XG#s,0s.6Rl#2.%#l#:s*~s*y#0Cs,3@#s*Rs*Q0Cs.:s###s*Os*N%EEs$ns$A-EE#-Cs.x#.Cs.y$2D#'%#.EE(-Cs.}#.Cs.~$2D#'%#/(#m#/#/s-ws-tm#$#CDs//#0s1Ys-ss-ns#6s//#4Cs&NS%s&%5s,-IFFH#Ml#,#s+vs+pl#-s&Rs,0#l#.s,7s,5#j#/C#/s&Xs&0k#/C#VS1Ds%aN#l#2'%#l#3s,Js,E#l#4s,Ls,M#l#5s,Ps,Q#%EEs%as%N-EE#-Cs/;#.Cs/<$2D#'%#.EE(-Cs/@#.Cs/A$2D#'%#/(#m#/#/s.Ss.Pm#$#CDs/Q#0s1xs.Os.?As/Q#<Ds/`ISbF#VS1D#N#l#2A?#l#3s,ds,_#l#4s,fs,g#l#5s,js,k#Fs/l%CS's2E#)s/V#s/S%Cs/VJ#%Cs/Ws1}$%EE$#-EE#-Cs/Z#.Cs/[$2D#'%#.EE(-Cs/_#.Cs/`$2D#'%#/(#m#4#/s/ys/vm#$#CDs/}#0s2;s/ts.wA@#EEEEs/is/iG#)$s/A#)%s/E#)&s/I#)(s/r#))s/v#)*s/z#)+s0,#RD#&s2G#s$tm#/#US7RRD#&s2K#s$xm#&#VS8RDUS9#%CC#s2FUS:%%CC#s2HUS;'+s2W#%CC$#)s2R#s2E)s2S'#)s2T*#'(s25>s/D#+$s/E%CCs/F#)s2Y#s2LnL#$##s2I&#%###s2M(s2[#s0N(s2\*#H#&s2a9#m#8#USc8:C4YSd:QP#G0Cs2js0Q&%#VSeN<H#&s2iA#m#&#j#@s3+#j#As3A#j#BC#j#CL##"). Qed.
End Dens.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PMDef.
  Variables (sp0 brk0 mbase : word) (inp : ProcInput).
  Let sp0z := bv_unsigned sp0. Let brk0z := bv_unsigned brk0.
  Let argc := Z.of_nat (length (in_argv inp)).

  Record PM (X : pm_syms) (c : config) : Prop := MkPM {
    (* [comment removed for export] *)
    pm_pc    : ms_pc (cfg_ms c) = Z_to_bv 64 A_MAIN;
    pm_svc   : ms_svc_pending (cfg_ms c) = None;
    pm_resv  : ms_resv (cfg_ms c) = None;
    pm_fregs : ms_fregs (cfg_ms c) = bvmap_empty;
    pm_fcsr  : ms_fcsr (cfg_ms c) = Z_to_bv 32 0;
    pm_rom   : ms_rom (cfg_ms c) = seg_rom BSEGS2;
    pm_regs  : let R := ms_regs (cfg_ms c) in
               getr R 1 = Z_to_bv 64 0x102ee8 /\ getr R 2 = Z_to_bv 64 (sp0z - 0x30) /\ getr R 3 = Z_to_bv 64 0x10800 /\
               getr R 4 = Z_to_bv 64 0x6617f0 /\ getr R 8 = Z_to_bv 64 (sp0z + 8) /\ getr R 9 = Z_to_bv 64 argc /\
               getr R 10 = Z_to_bv 64 argc /\ getr R 11 = Z_to_bv 64 (sp0z + 8) /\ getr R 12 = Z_to_bv 64 (pm_envp sp0z argc) /\
               getr R 18 = Z_to_bv 64 A_MAIN /\ getr R 19 = Z_to_bv 64 (pm_envp sp0z argc) /\
               (forall r : Z, 20 <= r <= 27 -> getr R (Z_to_bv 5 r) = Z_to_bv 64 0);
    (* [comment removed for export] *)
    pm_halted : m_halted (cfg_model c) = None;
    pm_fds    : m_fds (cfg_model c) = fds_std;
    pm_fs     : m_fs (cfg_model c) = in_fs inp;
    pm_limit  : vm_limit (m_vmmaps (cfg_model c)) = target_alloc_limit;
    (* #38: restated IN PLACE, same name and same position -- the "new field LAST" rule
       protects consumers we are not touching, and every consumer of this field moves in
       the same step.  Leaving the old (false) equation beside a new field is what (a)
       forbids. *)
    pm_reserved : exists rx : list (word * word),
                    vm_reserved (m_vmmaps (cfg_model c)) = segments_reserved BSEGS2 ++ rx
                    /\ Forall (resx_entry_ok BOTH_H) rx /\ (length rx <= n_resx BOTH_H)%nat
                    /\ sum_sizes rx <= resx_bytes BOTH_H;
    pm_topz   : TOP (cfg_model c) = pm_top sp0z;
    pm_brk    : vm_brk (m_vmmaps (cfg_model c)) = Z_to_bv 64 (if ps_granted X then brk0z + 0x2000 else brk0z);
    pm_eager  : eager_used (cfg_model c) <= 16515072;
    pm_maps   : vm_maps (m_vmmaps (cfg_model c)) = zz2ww (PM_MAPS brk0z X);
    pm_noacc  : vm_noaccess (m_vmmaps (cfg_model c)) = zz2ww (PM_NOACC brk0z X);
    pm_lazy   : m_vm_lazy (cfg_model c) = zz2ww (PM_LAZY sp0z X)
  }.
End PMDef.

Section PMOpen.
  (* [comment removed for export] *)
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : valid_sp sp0.
  Hypothesis Vbrk : valid_brk BSEGS2 brk0.
  Hypothesis Vav : valid_argv (in_argv inp).
  Hypothesis Vev : valid_envp (in_envp inp).
  Hypothesis Hh : HSF_both h = Some ch.
  Hypothesis HC : cs_ok BSEGS2 BOTH_H AsanInit.LIMIT
                        (SINV0L BPH2 OSSVerify.boost_beast.http_request.images.AsanUbsan.M.init_pc sp0 rdraw brk0 inp)
                        (argH0 sp0 rdraw inp) (in_fs inp) E ch R FULL model.
Scheme kc__6 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__7 := Elimination for Corelib.Init.Datatypes.nat Sort Prop.

  (* [comment removed for export] *)
  Lemma open_facts :
    let g := hole_granted h in let cls := hole_class h in
    hs_digest ch = DGX g cls /\ (cls <= 1)%nat
    /\ 0 <= vE E K_R06 <= 15 /\ (4096 * vE E K_B06) mod 65536 = 4096 * vE E K_R06 /\ 4295491576 <= vE E K_B06 <= 34326181871
    /\ 4294901760 <= vE E 0 <= 4294967295 /\ 1 <= vE E K_TID <= 4194303
    /\ qlo cls <= vE E 6 <= qhi cls /\ wlo cls <= vE E 10 <= whi cls
    /\ 32768 * vE E 0 + 4096 * vE E 6 + 16 * vE E 10 = bv_unsigned sp0 /\ 16 * vE E 10 = bv_unsigned sp0 mod 4096
    /\ 4096 * vE E 5 = bv_unsigned brk0 /\ vE E 1 = Z.of_nat (length (in_argv inp)) /\ vE E 2 = Z.of_nat (length (in_envp inp))
    /\ pm_stack_top (bv_unsigned sp0) = 32768 * vE E 0 + 4096 * vE E 6 + (if Z.leb 11 (vE E 10) then 4096 else 0)
    /\ TOP model = bv_unsigned sp0 - 8388608.
  Proof.
    (* LPS 727298f3: the recorded proof applied [cs_range] and the other cs_* facts of Section
       Generic to the run's input exploded into argv, envp, uid and hwcap; that Section now takes
       the whole input, so the recorded body no longer type-checks.  It is replaced by the text of
       the same lemma in projects/openssl/echconfiglist_parser/proofs/lib/Both/AsMainFacts.v (same
       Section PMOpen and statement; the text holds no binary-specific literal).  This tree's Bo
       Section Generic has nine Variables (its [fs] is a notation for [in_fs inp]), so each
       cs_* fact takes nine arguments before [HC] where the donor passes ten. *)
    cbv zeta. pose proof (HS_digest h ch Hh) as D.
    set (g := hole_granted h) in D |- *. set (cls := hole_class h) in D |- *.
    pose proof (hole_class_le h ch Hh : (cls <= 1)%nat) as Hcls.
    assert (Dcls : kn_cls (kn ch) = cls) by exact (f_equal dg_cls D).
    assert (Dkf : kn_facts (kn ch) cls = true) by (rewrite <- Dcls at 1; exact (f_equal dg_kfacts D)).
    unfold kn_facts in Dkf.
    apply andb_prop in Dkf as [Dkf K0]. apply andb_prop in Dkf as [Dkf KTID]. apply andb_prop in Dkf as [Dkf K10].
    apply andb_prop in Dkf as [Dkf K6]. apply andb_prop in Dkf as [Dkf KREL]. apply andb_prop in Dkf as [KR06 KB06].
    pose proof (cs_range _ _ _ _ _ _ _ _ _ HC _ _ _ KR06) as VR06. rewrite uE_var in VR06.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ HC _ _ _ KB06) as VB06. rewrite uE_var in VB06.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ HC _ _ _ K6) as V6. rewrite uE_var in V6.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ HC _ _ _ K10) as V10. rewrite uE_var in V10.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ HC _ _ _ KTID) as VTID. rewrite uE_var in VTID.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ HC _ _ _ K0) as V0. rewrite uE_var in V0.
    pose proof (cs_range _ _ _ _ _ _ _ _ _ HC _ _ _ KREL) as VREL.
    pose proof (rel06_sound E ltac:(lia) VR06 ltac:(lia)) as REL.
    pose proof (cs_sp0 _ _ _ _ _ _ _ _ _ HC Vsp) as SP.
    pose proof (cs_sp0_mod _ _ _ _ _ _ _ _ _ HC Vsp) as SPM.
    pose proof (cs_brk0 _ _ _ _ _ _ _ _ _ HC Vbrk) as BRK.
    pose proof (cs_v1 _ _ _ _ _ _ _ _ _ HC Vav) as V1.
    pose proof (cs_v2 _ _ _ _ _ _ _ _ _ HC Vev) as V2.
    pose proof (stack_top_cls (bv_unsigned sp0) (vE E 0) (vE E 6) (vE E 10) cls ltac:(lia) V6 V10 Hcls) as STK.
    assert (TOPm : TOP model = bv_unsigned sp0 - 8388608).
    { rewrite (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC).
      pose proof (lin_of_sound E e_sp0_early) as LS.
      replace (lin_of e_sp0_early) with (lSP 0) in LS by (vm_compute; reflexivity).
      destruct LS as [qq LS]. unfold lden, lSP in LS; cbn [fst snd tden] in LS. rewrite ?uE_var in LS.
      pose proof (u64_range (edenot E e_sp0_early)). unfold AX2S.uE in LS.
      assert (V610 : 0 <= vE E 6 <= 7 /\ 0 <= vE E 10 <= 255) by (clear -V6 V10 Hcls; destruct cls as [|[|]]; cbn [qlo qhi wlo whi] in V6, V10; lia).
      lia. }
    repeat split; assumption || lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PM_open : PM sp0 brk0 inp (Xof (hole_granted h) E) (cfg_of BSEGS2 R A_MAIN FULL model).
  Proof.
    (* LPS 727298f3: the recorded proof applied the cs_* facts of Section Generic to the run's
       input exploded into argv, envp, uid and hwcap; that Section now takes the whole input, so
       the recorded body no longer type-checks.  It is replaced by the text of the same lemma in
       this unit's As/AsMainFacts.v (Section PMOpen; same PM record, digest and helper lemmas here,
       each read off this file), with each cs_* fact applied to this Section Generic's nine
       Variables ([fs] is a notation for [in_fs inp] here, a Variable in the As tree). *)
    pose proof open_facts as OF. cbv zeta in OF.
    destruct OF as (D & Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm).
    set (g := hole_granted h) in D |- *.
    set (cls := hole_class h) in D, Hcls, V6, V10.
    assert (Dregs : map lin_of (s_regs (a_ss ch)) = DG_regs g)
      by exact (f_equal dg_regs D).
    assert (Dmaps : map (fun m => (lin_of (am_base m), lin_of (am_len m), am_kind m)) (a_maps ch) = DG_maps g)
      by exact (f_equal dg_maps D).
    assert (Dnofog : no_fog (a_maps ch) = true)
      by exact (f_equal dg_nofog D).
    assert (Dled : cs_ledgers ch = Some (DG_noacc g, DG_lazy g))
      by exact (f_equal dg_ledgers D).
    assert (Dbrk : lin_of (a_brk ch) = (if g then pgo 8192 5 else pg 5))
      by exact (f_equal dg_brk D).
    assert (Dfd : a_fd ch = FdStd) by exact (f_equal dg_fd D).
    assert (Deager : a_eager ch = (if g then 16515072 else 16510976))
      by exact (f_equal dg_eager D).
    constructor.
    - (* pm_pc: cfg_of/mkst. *) reflexivity.
    - (* pm_svc: cfg_of/mkst. *) reflexivity.
    - (* pm_resv: cfg_of/mkst. *) reflexivity.
    - (* pm_fregs: cfg_of/mkst. *) reflexivity.
    - (* pm_fcsr: cfg_of/mkst. *) reflexivity.
    - (* pm_rom: cfg_of/mkst. *) reflexivity.
    - (* pm_regs: cs_reg_lin, Dregs, SP and V1 from open_facts. *)
      cbn [cfg_ms cfg_of mkst ms_regs].
      assert (RG : forall n : nat, (0 < n < 32)%nat ->
        getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 (lden E (nth n (DG_regs g) (0, [])))).
      { intros n Hn.
        rewrite (cs_reg_lin sp0 brk0 rdraw inp E ch R FULL model HC (Z.of_nat n) ltac:(lia)).
        rewrite <- Dregs, Nat2Z.id.
        change (0, []) with (lin_of (ELit 0)). rewrite map_nth. reflexivity. }
      let reg1 := fun n =>
        (etransitivity; [exact (RG n ltac:(lia))|];
         cbn [nth DG_regs]; unfold lSP, lENVP, lv, lvx;
         apply eqm_Z_to_bv; exists 0;
         unfold lden, pm_envp; cbn [fst snd tden];
         rewrite ?uE_var, <- ?SP, <- ?V1; lia) in
      (split; [reg1 constr:(1%nat)|];
       split; [reg1 constr:(2%nat)|];
       split; [reg1 constr:(3%nat)|];
       split; [reg1 constr:(4%nat)|];
       split; [reg1 constr:(8%nat)|];
       split; [reg1 constr:(9%nat)|];
       split; [reg1 constr:(10%nat)|];
       split; [reg1 constr:(11%nat)|];
       split; [reg1 constr:(12%nat)|];
       split; [unfold A_MAIN; reg1 constr:(18%nat)|];
       split; [reg1 constr:(19%nat)|]).
      intros r Hr.
      assert (Hr2 : r = Z.of_nat 20 \/ r = Z.of_nat 21 \/ r = Z.of_nat 22 \/ r = Z.of_nat 23
        \/ r = Z.of_nat 24 \/ r = Z.of_nat 25 \/ r = Z.of_nat 26 \/ r = Z.of_nat 27) by lia.
      destruct Hr2 as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
        (rewrite RG; [destruct g; reflexivity | lia]).
    - (* pm_halted: cs_halted. *)
      exact (cs_halted sp0 brk0 rdraw inp E ch R FULL model HC).
    - (* pm_fds: cs_fds and Dfd. *)
      exact (cs_fds sp0 brk0 rdraw inp E ch R FULL model HC Dfd).
    - (* pm_fs: cs_fs. *)
      exact (cs_fs sp0 brk0 rdraw inp E ch R FULL model HC).
    - (* pm_limit: cs_limit. *)
      exact (cs_limit sp0 brk0 rdraw inp E ch R FULL model HC).
    - (* pm_reserved: cs_reserved, including the tail's geometry and budgets. *)
      exact (cs_reserved sp0 brk0 rdraw inp E ch R FULL model HC).
    - (* pm_topz: TOPm from open_facts and pm_top. *)
      cbn [cfg_model cfg_of]. unfold pm_top. exact TOPm.
    - (* pm_brk: cs_brk, Dbrk and BRK from open_facts. *)
      cbn [cfg_model cfg_of].
      rewrite (cs_brk sp0 brk0 rdraw inp E ch R FULL model HC), Dbrk.
      apply eqm_Z_to_bv. exists 0. unfold Xof; cbn [ps_granted].
      destruct g; unfold lden, pgo, pg; cbn [fst snd tden]; rewrite ?uE_var; lia.
    - (* pm_eager: cs_eager and Deager. *)
      cbn [cfg_model cfg_of].
      pose proof (cs_eager sp0 brk0 rdraw inp E ch R FULL model HC) as EG.
      rewrite Deager in EG. destruct g; lia.
    - (* pm_maps: cs_maps, Dnofog, Dmaps and BRK from open_facts. *)
      cbn [cfg_model cfg_of].
      rewrite (cs_maps sp0 brk0 rdraw inp E ch R FULL model HC Dnofog).
      transitivity (map (fun t : lin * lin * mkind =>
        (Z_to_bv 64 (lden E (fst (fst t))), Z_to_bv 64 (lden E (snd (fst t)))))
        (map (fun m => (lin_of (am_base m), lin_of (am_len m), am_kind m)) (a_maps ch))).
      { rewrite map_map. apply map_ext. intros m. reflexivity. }
      rewrite Dmaps. unfold zz2ww, PM_MAPS, Xof, pm_meta_map.
      cbn [ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13
        ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted].
      destruct g; cbn [map fst snd DG_maps]; unfold lMETA, pg, pgo, lden;
        cbn [fst snd tden]; rewrite ?uE_var;
        repeat first [reflexivity | apply f_equal2]; f_equal; lia.
    - (* pm_noacc: cs_noacc_lazy, Dled and DG_noacc_den with VR06/REL/BRK. *)
      cbn [cfg_model cfg_of].
      rewrite (proj1 (cs_noacc_lazy sp0 brk0 rdraw inp E ch R FULL model HC _ _ Dled)).
      apply DG_noacc_den; [exact VR06 | exact REL | intros _; exact BRK].
    - (* pm_lazy: cs_noacc_lazy, Dled and DG_lazy_den with VR06/REL. *)
      cbn [cfg_model cfg_of].
      rewrite (proj2 (cs_noacc_lazy sp0 brk0 rdraw inp E ch R FULL model HC _ _ Dled)).
      exact (DG_lazy_den E g (bv_unsigned sp0) VR06 REL).
  Qed.
End PMOpen.

Section PMProof.
  Variables (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config).
  Hypothesis P : P_main sp0 brk0 mbase rdraw inp c.

  Theorem P_main_PM : exists X, PM sp0 brk0 inp X c.
  Proof.
    pose proof P as P'. destruct P' as [(Vsp & Vbrk & Vmb & Vav & Vev & Vfit & Vuid & Vhw) (h & ch & E & R & FULL & model & Hh & _ & Hc & HC)].
    exists (Xof (hole_granted h) E). rewrite Hc. exact (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
  Qed.
End PMProof.
