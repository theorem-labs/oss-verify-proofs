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
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AXL_bridge.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AXL_snpDisc AXL_snpRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Lemma kword_of_bytes : forall E m a bs (o : nat) (w : nat) x v,
  bytes_at asegs m a bs -> (o + w <= length bs)%nat -> (1 <= w <= 8)%nat ->
  x = a + Z.of_nat o -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  firstn w (skipn o bs) = word_to_le_bytes w (Z_to_bv 64 v) ->
  kentry_ok RSEGS E m (KWord (SA (ELit 0) x) w (ELit v)).
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.env); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@Corelib.Init.Peano.le); constr:(@Corelib.Init.Nat.add); constr:(@Corelib.Init.Datatypes.length); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Lists.ListDef.firstn); constr:(@Corelib.Lists.ListDef.skipn); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2SoundX.SX2S.kentry_ok); constr:(@OSSVerify.boost_beast.http_request.images.Asan.M.loaded_segments); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.KWord); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.SA); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymExec2X.SX2.ELit); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.SymRunX.kword_intro); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.rdn); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.eq_ind); constr:(@LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.rdn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at_rdn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXL_bridge.wa_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXL_bridge.rdn_same); constr:(@Stdlib.ZArith.BinInt.Z.add_0_l)|] [|@x; @Ha; @__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @__sat3; @__sat2; @cstr1; @cstr0; @cstr; @Hl0; @Hw0; @__x2; @__x3; @__x4; @z; @l; @n; @a; @mem; @segs; @o; @b; @Hv; @Hs; @H; @Hw; @Hl; @B; @v; @w; @bs; @m; @E|] "#&k#9$;#B#v#R#w#-#u###,#$#'#D#.#|#~#+#O#&#Z#1#0#%#)#(#@#*#/#G#Q#9#b#p$5#>#=#A#F#H#L#c#N#h#j#k#x$'$(#`$-#8$9#P#E#S#\#[#Y#2#d#e#f#g#i#l#n#m#o#r#t$#$$$%$)$*$&#5$,$/$+$1#6$3$4#7$8$:$;$<$=$>#^#<#_#K#M#z#y#X#?#I#s#J$2#T#q#{#}#C#V#U#W#]#a$.$0$6$7@#>%#2$#J%#~%$#$$$&$%'$&*$'%$($$)%#=%$*+$+%$,&$-$$.%$/%$0%$1$$2&$3&$4%$5$$6/$7%$8'$9%$:),S*,#,#,#,#,#US3#US4#US3(US4#US5#k##&#6%XSFS6S(S)LVS7LS#-(S).$#'S8.#L'$'#'#'#'#'#'#.L#0+#$S(%Q#(CL#$S+%J##EG-;G$#%N#2s#'2s##VSG$##&#7BGN8s##J#+s#'S+9J#(s##%#:EVSH#S#:QWSI$G#XSJS$SKS%#k##(#k##.#k##6#j#$C##EJ-s#1J$#%G###67s#5JG8s#6Q#+s#:S(9Q#(s#6%#+s#=E$G%S,#:S+&s#@&&s#A=.s#8J2S*$J#$#&C%&C%;MCS-RS.S0s#>'$J&#.Js#70*#2s#P#*#0*#&C%;MCS-RS.S0J-*s#=&#ZSL0)-&*#XS9)&#LVS7NG-s#QS,.$#$N%#;$&#$#&C&&C?fSMMMMCCCSNRRRS:SON($G@#&C';MCS-RS.S0-)$,(#XS9,(#S(-s#]S&US;#$$#E#US;S&$S&#E#VSPs#Hs#GVS<Es#I#Es#IVS<Es#Ik##$#k##&##Es#NWSQs#Os#NKj##S=#j#%%##Es#Pk##S=#k#%(#VSREs#U&SS#m##0UK#USTS16S13CKUSUCUSVC4Cs#;5CS*)C$O#*&HDDF#PZSW'HDDFS#[S>(HDDF$#USXD/*HDDF$#&VSY+F&S?S@VSZIS'(S?#S@m$%#WS[CEKXS\IS'$#l#&*)#l#'54#l#(87#j#)C#j#*S/##s#OI0#K#s#QKk##$#k#)C#k#*S/#$S]##s#NWI#$Ql#+,&#l#,s#&s#2#l#-s#.s#+#l#,s#8s#3#l#.s#<s#:#l#/s#=s#;#l#0s#As#?#l#1s#Ds#J#l#2s#Rs#V#XSAs#bs#_s#\#4Cs#Z)Cs#)O#*s#,HDDF#P[S>s#-HDDFs#(#/s#.HDDF#s#'$l#&#s#&@l#'s#2s#1#l#(s#5s#4#j#)C#j#*S/##Is#d0K##Ks#fk##$#k#)C#k#*S/##s#r?WI#@Ql#++%#l#,s#Bs#N#l#-s#Js#G#l#,s#Ts#O#l#.s#Xs#V#l#/s#Ys#W#l#0s#]s#[#l#1s#`s#f#l#2s#ns#r#XSAs#ws#ts#q#<Cs$W<Cs$Z<CS8WSBC$#WSBC&#VS^#S_WS`S1#s#P3CS'USaC=C$K#4CE5Cs$u)C$O#*s#SHDDF#P)C&Os#R*s#UHDDF#P1Cs#T'1C)#)C*O#*s#YHDDF#P/s#ZHDDF's#S#/s#[HDDF*s#T#l#&#s#Ss#Ml#'0s#^#l#(4s#a#j#)C#j#3C##EK%S'S#%E##E#k##&#k##'#k#)C#k#3C#$SbXI#SCS)Nl#+-%#l#,s#qs#}#l#-s#ys#v#l#,s$'s#~#l#.s$+s$)#l#/s$,s$*#l#0s$0s$.#l#1s$3s$9#l#2s$As$E#3CL=C#S's#)3CS#=C$K#UScS*5C#1Cs#+#5Cs%B)C$O#*s#}HDDF#P1Cs#|%4Cs$~WSdC#s%B)C%O#*s$&HDDF#P1Cs#.,)C#O&*s$)HDDF#P/s$*HDDF&s$##/s$+HDDF,s$$#l#&#s$#s#yl#'4s$.#l#(s#@s$1#j#)C#j#3C#j#4C#j#5C#%KS'##S#%KL##s%3%s#2L##s%5k##%#k##(#k#)C#k#3C#k#4C#k#5C#-s%ZSe$#ZI#s$&s#6SCS+Gl#+2&#l#,s$Hs$T#l#-s$Ps$M#l#,s$Zs$U#l#.s$^s$\#l#/s$_s$]#l#0s$cs$a#l#1s$fs$l#l#2s$ts$x#US5s%c+s%jIXS2S$S%#G+s%lQ9G#>s%h#((&#j#6C#%S&s$y+s%r#XS2S$S%#G>s%nI(.$#j#7s%p#6Sfk#8M1k#9s%x#k#:s%u#k#;&#XIS$S%,G7s%zNS,8s%{G#>s%y#(9&#j#<(#USgs%EXSDS$S%IG(=#'j#=s&(#\ShS6S&S,NGJS(S)+s&+s%JUSis%K?s&,)&%$#?1SD+#S2Sj?s&)s%g7#s%eI%Es%OUSks%PZSECs%Q@%$#dSlS$S%S&s%gs%Ts%RJs%Qs%js%Ps%Os$Js$.s#\s#)#j#>s%V#j#?s%\#j#%s%a#ZSECs%ys%c#S)Ij#@s%|#j#As&$#j#Bs&0#j#Cs&4#j#DC#j#$C#j#EM#j#<M#j#Fs&:#j#9C#j#Gs&=#j#HSm##"). Qed.

Lemma Forall_flat_map_intro : forall {A B} (P : B -> Prop) (f : A -> list B) l,
  Forall (fun a => Forall P (f a)) l -> Forall P (flat_map f l).
Proof. intros A B P f l H. induction H as [|a l Ha _ IH]; cbn [flat_map]; [constructor | apply Forall_app; split; assumption]. Qed.

Ltac zc := vm_compute; first [reflexivity | discriminate | lia | (intro; discriminate)].
Ltac kw B :=
  lazymatch goal with
  | |- kentry_ok _ ?E ?m (KWord (SA (ELit 0) ?x) ?w (ELit ?v)) =>
      lazymatch type of B with
      | bytes_at _ _ ?a ?bs =>
          let o := eval vm_compute in (Z.to_nat (x - a)) in
          apply (kword_of_bytes E m a bs o w x v B); [zc | lia | zc | zc | zc | vm_compute; reflexivity]
      end
  end.
Ltac grp RC :=
  cbn [fst snd kn_of_cells] in *; destruct RC as [[_ B] _];
  repeat (apply Forall_cons; [ kw B |]); apply Forall_nil.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

Lemma cells_know : forall m, ACONST m -> forall E, know_ok RSEGS E m CELLS.
Proof.
  intros m AC E.
  assert (H : flat_map (fun ac : Z * list cell => kn_of_cells (fst ac) (snd ac)) aconst_cells = CELLS) by (vm_compute; reflexivity).
  destruct AC as [C _].
  unfold know_ok. rewrite <- H. apply Forall_flat_map_intro.
  unfold aconst_cells in C |- *.
  repeat (apply Forall_cons_iff in C; let RC := fresh "RC" in destruct C as [RC C];
          apply Forall_cons; [grp RC |]).
  apply Forall_nil.
Qed.
