(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import MallocKit_B MallocKit_B2 MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import MallocKit_B3 F_ntf_D F_ntf_E F_ntf_F F_ntf_G F_ntf_H F_ntf.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RF_get_meta RF_ntf_A RF_ntf_C RF_ntf_D RF_ntf_E RF_ntf_F RF_ntf_G RF_ntf_H.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
    (st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ rmrep st' m'
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
    /\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_entry st lo (sp : word) m m1 :
  munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono usegs m m1 -> lo <= bv_unsigned sp - 96 ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof. try hcb. try hsb.
  intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Specif.sumbool Sort Prop.

Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
  oracle_ok o m st -> rmrep st mw -> hceil <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof. ltac2:(KReplay.runh [|@o; @m; @m'; @st; @lo; @sp; @mw|] [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocTree.mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.mstate); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.F_ntf.oracle_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rmrep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocTree.rpres_except); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocKit_B.rfree_fp); constr:(@Corelib.Numbers.BinNums.N); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.region); constr:(@Corelib.Init.Logic.eq); constr:(@stdpp.base.lookup); constr:(@stdpp.gmap.gmap); constr:(@stdpp.numbers.N.eq_dec); constr:(@stdpp.countable.N_countable); constr:(@stdpp.gmap.gmap_lookup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.s_regions); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.rkind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.r_kind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.RKGroup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.round_up_pg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.r_len); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.r_base); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.cellval); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.cell_read); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.get_shadow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.Unknown); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wa); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rregions_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rmrep_ctx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rmrep_globals); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rmrep_areas); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rmrep_groups); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rmrep_shadow); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Datatypes.prod); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.s_reserved); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.ref_reserved); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ranges_free); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocRep.lr_lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.area); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.aptr); constr:(@stdpp.decidable.prod_eq_dec); constr:(@stdpp.numbers.Z.eq_dec); constr:(@stdpp.countable.prod_countable); constr:(@stdpp.countable.Z_countable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.s_areas); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ghdr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.s_groups); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rreserved_disjoint); constr:(@Corelib.Init.Logic.eq_sym); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.USegs.usegs); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.RCTX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.conc); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.Known); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Stdlib.micromega.Tauto.OR); constr:(@kc__3); constr:(@Stdlib.NArith.BinNat.N.eq_dec); constr:(@Corelib.Init.Specif.sumbool); constr:(@kc__4); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.f_equal); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocRep.lr_lo_group); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rgroup_conc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.F_malloc_free.base16_mod); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Logic.False_ind); constr:(@kc__3 (@Corelib.Numbers.BinNums.N)); constr:(@kc__3 (@Corelib.Numbers.BinNums.Z)); constr:(@kc__3 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.aptr)); constr:(@kc__3 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ghdr)); constr:(@kc__3 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.region))|] [|@o; @r; @rid; @r2; @rid2; @r1; @rid1; @ar; @a; @gh; @b; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__p1; @__arith; @__sat9; @__sat10; @__sat11; @__sat12; @v; @__x5; @__p2; @__p3; @__p4; @A; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H2; @H1; @H0; @H; @s; @Hr'; @rid'; @t; @Hin; @Hk'; @r'; @e; @o0; @NE; @n; @x; @z; @__x6; @__x7; @__x8; @__sat24; @__sat25; @r4; @q4; @H23; @H22; @H21; @H20; @H19; @r3; @q3; @H18; @H17; @H16; @H15; @H14; @q2; @H13; @H12; @H11; @q1; @r0; @q0; @Cm; @_H0; @RbAL; @_H; @RbB0; @SbA; @Sb1; @Sb0; @Krb; @Cb; @Hrb; @rb; @Hb; @HC; @c; @hint; @HCEILB0; @D4; @D3; @D2; @D1; @RF; @RBC; @RL0; @RBAL; @RB0; @WG; @WA; @DJ; @WR; @Hres; @WF; @Hc; @M8; @Hq; @Hk; @Hr; @h; @q; @PE; @LO; @MR; @OK; @HCANB; @HSECB; @HCEILB; @mw; @sp; @lo; @st; @m'; @m|] "#O:$s&8$}%6&'%5%+###$&(&&%h#%#(&>#&&0$s#'%G#+%_%^#*&.#,#)#1#8#7%X%Z#/#4$&#-%?%A#5#:#0%t#|#~#.&2#x#{%##9#A#o%*#p#}$#$'$,$-#;#>#B#I#=#i#t#z#2$$&P$)#<#?#C#E%z&*&:#u#s&?&B&C&D&E#y%K$%$($z#3#@#F#G#J#M#e#l#m#j#q#r#v#w$*&9#D#W#V#k#n$.$y%:#H#K#L#O#X#\#[#`#d#Z#h%l%m#b#c#f&K$+&M&W$0%9%;%<%J#6%N%O%P%Q%R%S#N#P#T#S#R#a#Y#]%q#g&F&H%k&O$`$a&T$1$w$v%1%2%4%U%T%V%a#Q#U#_%n%y&G&J&N&L$[$\$]$^$_&V&U&X&Z$f$2$/$~%(%)%,%.%/%0%3%W%`%b%c%j#^%p%r%{%~&#&%&3&4&6&7&8&5&Q&R$K$L$M$N$O$P$Q$R$U$V$W$X$Y$Z$b&S&Y$r$e$8$7&[$:$9&\$|${%$%%%7%E$x%-%F%8%e%D%C%B%'%\%=&$%|&,&+%g&;%H%I&<%M%>%]%i%[%v&A%L&)&=%&&-%Y%@%o&/%d%x%w%s&1%f%}&@&I%uU%b%%c%%d&%e%%f$%g%%h$%i)%j%%k%%l$%m$%n$%o%%p$%q+%r'%s'%t*%u&%v%%w%%x%%y%%z(%{%%|$%}$%~$&#&&$%&%$&&*&'$&($&)%&*&&+$&,%&-%&.$&/$&0%&1&&2&&3&&4%&5%&6(&7%'T%'#'#'#'#'#UTY#UTZ#UTY(UTZ#USj#k##&#UTwSA/T%/#/#/#/#/#/#/#/#/#/#/#/#/#'#/#/#/#/#/#/#/#/#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#E#UTxSA$$#/s#&/#/#/#/#/#/#/#/#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#E#$s#%##s#%#m#s#W#UTySEUTzSE$G#Es#gEs#cVT{$#('##'#m#*#UT|SEUT}SE$G#($)#$#m#'#WT[S*S%S+XT\SASES(S#$s#9S(WT]S*S%S(WT~#S=S4USjDXT<FT&T=DXT>FT&T=D1S,*FD%$P#<DM%($#HP%S5#S6$GP-S#.#(P##&#Es$()N&#S#Es$*,$#$'#9S7S(8#NUT?S#%S$$#)S(&#S+B#US-#)S%&#S(B#US-#%s$2H#j#$s$3#XT\SASET@SkVTASAS.VTBS.S2VTCSES2VTDS.S2VTES.S2VTFS.S2#$##&##(##*##,#)S*&#S%B#US8#USB$%s$E$#j##)#VTBS-S7VTCSES7VTDS-S7VTES-S7VTFS-S7#$##&##(##*#VTASASBVTBS8S.VTCSES.VTDS8S.VTES8S.VTFS8S.#$##&##(##*#VTASASLVT^CCUT_#UT`SXUU#SA%%$#1SM*FDs#Ps#OI#<DH%s#S$#)I(G#'s$k'#'#'#'#'#E#,+#%C#G-I$G#.$&0#$#s$AG82%%S/#S0#%##)##,##6#k##9#k#%D#k#&F#1Sl*FDs#ms#lP#%s#o#s#j1SC*FDs#ps#oM#<DI%s#s$#%FNP?#-N.#&s#i#=P$$#)P-P.#&%#=N$$#0)#k##/#k##2#k##7#k#'D#k#(F#k#)D#k#*F#VT^FCUSjS'XU$FT&CTaZU%FT&T=CTaU&XT<S&$#S'XT>S&%$S'KSM*)S'%$I#<S'H%*$#PFCP*FDs$7s$6#s#)%s$9#s#E6FCP$G#&$s#>-H.#$%#,(s#B%C#GHH%S5#S6?#=H)H&#/$%##'##+##.##3##6#j#%D#+D#k##<#k#+S'#k#,s#'#USjLXT<S&s#'s#&LXT>S&s#(s#'L>SM*s#,L%$I#<LH%($#&Bs$I$#?,s#$s$K%C#G#%##s#&##?##s#*#j#%D#+D#k##-#k#-L#k#.s#;##7##s#>##s#[##s#y#)S,&#S9B#USY#USM$%s&$$#j##)#1SY*FDs$rs$qI#%s$t#s$$k###s#jk#%D#k#&F#*FDs$ws$vPs#f%s$y#s$t1SN*FDs$zs$yM#%s$|#s#hk###s#Yk##'#k#'D#k#(F#k#)D#k#*F#KSY*s#YS's#Us#TI#%s#Y#s#R*FDs%)s%(s#Qs#t%s%+#s$7##s#>j#%D#+D#k##(#k#+S'#k#,s#b#>SY*s#dLs#=s#<I#%s#?#s#:#,s#3j#%D#+D#k##&#k#-L#k#.s#k##,##8##s#$#UT`SM%s$Q#s$O*FDs%?s%>Is$.%s%A#s$Mk###s$7k#%D#k#&F#1SZ*FDs%Es%DP#%s%G#s%B1S{*FDs%Hs%GM#%s%J#s$6k###s$'k##'#k#'D#k#(F#k#)D#k#*F#KSC*s$'S's$#s#~I#%s$'#s#|*FDs%Ss%Rs#{1%s%U#s$a##s#hj#%D#+D#k##(#k#+S'#k#,s$0#>SC*s$2Ls#gs#fI#%s#i#s#d#,s#]j#%D#+D#k##&#k#-L#k#.s$9##,##8##s#%#*FDs%gs%fIs#L%s%i#s$uk###s$_k#%D#k#&F#*FDs%ls%kPs#'%s%n#s%i1S[*FDs%os%nM#%s%q#s$]k###s$Nk##'#k#'D#k#(F#k#)D#k#*F#KSN*s$NS's$Js$II#%s$N#s$G*FDs%zs%ys$Fs#5%s%|#s%,##s$3j#%D#+D#k##(#k#+S'#k#,s$W#>SN*s$YLs$2s$1I#%s$4#s$/#,s$(j#%D#+D#k##&#k#-L#k#.s$`##,##8##s#$#)S7&#S2B#USZ#USN$%s'H$#j##)#*FDs&9s&8Ps#)%s&;#s&61Sm*FDs&<s&;M#%s&>#s%*k###s$wk##'#k#'D#k#(F#k#)D#k#*F#KSZ*s$wS's$ss$rI#%s$w#s$p*FDs&Gs&Fs$os#7%s&I#s%U##s$\j#%D#+D#k##(#k#+S'#k#,s%$#>SZ*s%&Ls$[s$ZI#%s$]#s$X#,s$Qj#%D#+D#k##&#k#-L#k#.s%-##,##8#*FDs&Zs&YIs#q%s&\#s%hk###s%Rk#%D#k#&F#1Sn*FDs&`s&_P#%s&b#s&]1T'*FDs&cs&bM#%s&e#s%Qk###s%Bk##'#k#'D#k#(F#k#)D#k#*F#KS[*s%BS's%>s%=I#%s%B#s%;*FDs&ns&ms%:1%s&p#s%|##s%'j#%D#+D#k##(#k#+S'#k#,s%K#>S[*s%MLs%&s%%I#%s%(#s%##,s$xj#%D#+D#k##&#k#-L#k#.s%T##,##8#*FDs'%s'$PA%s''#s&~1SO*FDs'(s''M#%s'*#s%rk###s%ck##'#k#'D#k#(F#k#)D#k#*F#KSm*s%cS's%_s%^I#%s%c#s%\*FDs'3s'2s%[s#/%s'5#s&A##s%Hj#%D#+D#k##(#k#+S'#k#,s%l#>Sm*s%nLs%Gs%FI#%s%I#s%D#,s%=j#%D#+D#k##&#k#-L#k#.s%u##,##8#)SB&#S-B#USn#USm$%s(\$#j##)#KSn*s&$S's%|s%{I#%s&$#s%y*FDs'Ps'Os%xs#+%s'R#s&^##s%ej#%D#+D#k##(#k#+S'#k#,s&-#>Sn*s&/Ls%ds%cI#%s%f#s%a#,s%Zj#%D#+D#k##&#k#-L#k#.s&6##,#1So*FDs'cs'bP#%s'e#s'`1T(*FDs'fs'eM#%s'h#s&Tk###s&Ek##'#k#'D#k#(F#k#)D#k#*F#KSO*s&ES's&As&@I#%s&E#s&>*FDs'qs'ps&=.%s's#s'###s&*j#%D#+D#k##(#k#+S'#k#,s&N#>SO*s&PLs&)s&(I#%s&+#s&&#,s%{j#%D#+D#k##&#k#-L#k#.s&W##,#KSo*s&ZS's&Vs&UI#%s&Z#s&S1T)*FDs(+s(*s&S#%s(-#s'9##s&@j#%D#+D#k##)#k#+S'#k#,s&d#>So*s&fLs&?s&>I#%s&A#s&<#,s&5j#%D#+D#k##&#k#-L#k#.s&m##,#)SP&#SXB#UT(#USo$%s)S$#j##)#>T(*s&wLs&Ps&OI#%s&R#s&M1Sp*FDs(Hs(Gs&p#%s(J#s'V##s&Ij#%D#+D#k##)#k#-L#k#.s'%#KT)*s''S's'#s&~I#%s''#s&|1TG*FDs(Ts(Ss&|#%s(V#s'b##s&ij#%D#+D#k##)#k#+S'#k#,s'1#>Sp*s'3Ls&hs&gI#%s&j#s&e1T**FDs(`s(_s',#%s(b#s'n##s&aj#%D#+D#k##)#k#-L#k#.s'=#WS*SCSlSP)Sl(G#,$s'n%C#G-Sl$G#.$&)#$#s)PGs('+%%S/#S0#%##)##,##/#)SC(G#,$s'}%C#G-SC$G#.$&)#$#s)_Gs(6+%%S/#S0#%##)##,##/#)SN&#SCB#UTH#UT*$%s*A$#j##)#,)s(5%C#G-SN$G#.$&.#$#s)sGs(J0%%S/#S0#%##)##,#)SZ(G#)S{,#s(D%C#G-S{$G#.$&(#$#s*&Gs(Y*%%S/#S0#%##)##,#)S[,#s(Q%C#G-S[$G#.$&(#$#s*3Gs(f*%%S/#S0#%##)##,#)Sm&#S[B#UTI#UTJ$%s*p$#j##)#-Sm$G#.$&,#$#s*DGs(w.%%S/#S0#%##)#)Sn,#s(n%C#G-T'$G#)T'.%&$#$#s*QGs)(&%%S/#S0#%##*#-SO$G#)SO.%&$#$#s*[Gs)2&%%S/#S0#%##*#)So&#SOB#UT+#US|$%s+;$#j##)#-So.#&+#$#s*jGs)A-%%S/#S0#%#-T($G#)T)-T).#&%#$#s*tGs)K'%%S/#S0#%#)Sp-Sp.#&%#$#s*|Gs)S'%%S/#S0#%#)TG&#SpB#UT,#UT-$%s+[$#j##)#-TG.#Gs)_+#%S/#S0)T*-T*.#&%#$#s+3)TH-TH.#Gs)i%#%S/#S0)Tb-Tb.#XU'SA%#H&&$'s)c'#'#'#E#'T%'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#E#/3'#/#/#'#'#'#'#'#'#'#'#'#'#'#'#E#/T%/#/#/#/#'#'#'#'#'#'#'#'#'#'#'#'#'#E#/s#4'#'#'#'#'#'#'#'#'#'#'#'#'#'#E#/s#6/#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#E#'4/#/#'#/#/#'#'#'#/#/#/#/#'#'#'#E#$s#ps#Z/s-0'#/#/#'#'#'#'#'#'#'#'#'#'#'#'#E#$s#[s$*05#$s$(s#]'s-3'#'#'#'#'#'#'#'#'#'#'#'#E#$s#Ys$;02#$s$9s#[/s-R'#'#'#'#'#'#'#'#'#'#'#'#'#'#E#$s#\s$N04#$s$Ls#^/s-g/#'#'#'#'#'#'#'#'#'#'#'#'#'#'#'#E#$s#_s$c06##8##s#,##s#>#)TK-TK.#&%#$#s$R$s$B'0$#$&s$D$s$2*0$#$)s$4$s$%-0$#$,s$'$s#r00$##&##*##.#)TJ&#TKB#UTL#UT.$%s.1$#j##)#-TJ.#&+#$#s$Z$s$H-0$#$&s$J$s$;00$#$)s$=$s$,30$##&##*#)TI-TI.#&%#$#s$z$s$j'0$#)Tc-Tc.#&%#$#s$p$s$^'0$#$&s$`$s$Q*0$#$)s$S$s$B-0$##&##*#)S}-S}.#&%#$#s%#$s$m'0$#$&s$o$s$`*0$#$)s$b$s$Q-0$##&##*#)S|&#S}B#USq#UT/$%s.k$#j##)#-S|.#&+#$#s%%$s$r-0$#$&s$t$s$c00$##&#)T+-T+.#&%#$#s%C$s%1'0$#)TM-TM.#&%#$#s%7$s%('0$#$&s%*$s$u*0$##&#)T0-T0.#&%#$#s%B$s%3'0$#$&s%5$s%$*0$##&#)T-&#T0B#USQ#UT1$%s/=$#j##)#-T-.#&+#$#s%C$s%2-0$#)T,-T,.#&%#$#s%Z$s%K'0$#)TN-TN.#&%#$#s%Q$s%@'0$#)Td&#U(B#USr#USs$$G&('s.X#$#)T.&#TdXT]SrS~St#?#)TL&#T.B#UT##USD$%s/d$#WT2T3SD&UTes/g%s/g$#?#)T4&#TLB#WT2T3SD#%s/m#)?#k##)##.#USD(USF)%s/s$#j##&#WT2T3SF,%s/v#2?#)T5&#T4B#WT2T3SF#%s/|#8?#k##)#j###Ij##>#WT5s##IH;@50$#j##s#'#j##s#,#k##s#)s##k##s#.#Is#.s-y$Gs#/$Gs-{,s##s-|$G#k##%#k##'#VU)s/3s/2(Gs/4$Gs/4(Gs/4k##$#k##&#$Gs/9WU*s/:s/9Ij##TO#j#/%#$Gs/;k##TO#k#/(#Is#$s.z$Gs#%$Gs.|)Sq&#T/,#s/#$G#k##'#k##)#LTfL#L#MC#MC%MCTf@C$#@C&#T#S\L)L#MC#MC%MC/@C#+@C%#@C'#T#S\UU+S:NS:$#NS:.#UT_S:QCMUU,CQCS#3C$P#3C&I#UU-CUU.CZS]#KEEJS+FCs0cJCs/o4C$S)#5'KEEJ#QC(KEEJ'#UTeEFCT%FCs0iOC$#4C#S)+5.KEEJ#QJCG4C#S>(51KEEJ#QFCs0~4C&S)#54KEEJ#Q4C%S>,56KEEJ#QC7KEEJ%#OC0(4C,S)#5:KEEJ#QJCs/~WU/C#s1&4C'S>#5>KEEJ#QC?KEEJ'#2@KEEJ+9#2AKEEJ2:#2BKEEJ6;#2s##KEEJ=<#VU0s#$JVU1S/S0VU2HM%S/#S0m$%#WU3CGIXU4HM$#l#0*)#l#1s#.s#-#l#2s#5s#4#j#3C#j#4C#j#5C#j#6C#j#7R#$Ms0A#S##&IS#$#P(GM$GS#(S#S+#$#&S#N$G#($s0B#$#k##'#k##+#k##-#k##0#k#3C#k#4C#k#5C#k#6C#k#7R#-Sq.#]Hs0y#s0zT/s#lS+S-S{T.l#8;&#l#9s#qs#i#l#:s#vs#s#l#;s$$s#{#l#<s$,s$&#$Srs$T(s$US~#$#$S^s$W's1V/#'#'#'#'#'#E#&S^#(s$a##-#1SD*FDs0Us0TI#%s0W#s/c$s.qs$M&s.qs.y(s$O##%##s.v##(#j#%D#+D#j#&F#+F#00#0=#>SD*S&Ls.os.nI#%s.q#s.l7SDI$#s$]&$s0[(s$_##%##(#j#-L#+L#j#.S&#+S&#1SF*FDs0qs0pM#%s0s#s/_HI%S5#S6)T/&#T5$s0&#($s/u#$#9SFM:'s0*8$#DH%S$$##(##.##1#j#=C#+C#j#%D#+D#j#&F#+F#0;#0s#)#j###O$Sss%4(s%5Sr#$#$S^s%7(s%8s#@#$#*FDs15s14Is##%s17#s0C$s/Q?(@s#>#$##s/U##'#j#%D#+D#j#&F#+F#0.#02#$T#s%8(s%9Ss#$#$S^s%;(s%<s#S#$#1Su*FDs1Is1HI#%s1K#s0W$s/es$w(s$xs#R#$##s/i##'#j#%D#+D#j#&F#+F#0/#03#j###O$SDs#?(s#@T##$#Is%+s0]$Gs%,)TP,#s0`$G#k##s%E#k##'#)T1&#TPI#s1S$G$)St&#SQ,#s1W$G#k##s%;#k##(#@Cs%3s%(@Cs%,#T#S\NS:#s%'QCN3C#Ms%$3C#Ns%$QCP3C#Ns%'3C%I#FCs33FCs33FCs(dOC$#4C&S)#5s%)KEEJ#QZS]s%*KEEJS(Cs%+KEEJ$#JCs2]4C#S)s%%5s%.KEEJ#QZS]s%/KEEJS%Cs%0KEEJ$#'s34FC#OC0#4C#S)s%,5s%5KEEJ#Q4Cs%)S>35s%7KEEJ#QZS]s%8KEEJS*4C5S>)5s%:KEEJ#QCs%;KEEJ%#4Cs%4S):5s%=KEEJ#QZS]s%>KEEJS42s%?KEEJ$s%8#2s%@KEEJ's%9#2s%AKEEJ,s%:#2s%BKEEJ/s%;#2s%CKEEJ5s%<#2s%DKEEJ;s%=#l#0#s%#s$yl#1s#%s%G#l#2s#,s%N#j#3C#j#4C#j#5C#j#6C#j#>C#j#7R#j#?R#j#@R#j#AR#&S#M$I###N$s3)I##S(&S+N$#M(GS((S+S(#S=#$NS+k###S,k##%#k##(#k##*#k##-#k##0#k#3C#k#4C#k#5C#k#6C#k#>C#k#7R#k#?R#k#@R#k#AR#$GSQ(s#YSR-St.#cHO&s2|%s#]#SQS_s3CNS=SPSOSqSsl#8B(#l#9s#as#Z#l#:s&?s&<#l#;s&Is&D#l#<s#ms#g#j#Bs#o#U#Hj##s$*#$S^s$U(s$Vs${#$#1Sv*FDs2qs2pI#%s2s#s2#)T6&#Sq$s13#($s$|#$##s17##)#j#%D#+D#j#&F#+F#01#$S^s&O(s&Ps%1#$#1S`*FDs3's3&I#%s3)#s25&s$+T6$s1D#($s%1#$##s1H##(#j#%D#+D#j#&F#+F#00#j###O$S^?(@s%C#$#Is$:s2;$Gs$;)SQ,#s2>$G#k##s'##k##'#Is$7s3/$Gs$8)Sr&#S~,#s33$G#k##s&s#k##(#)S~&#StVSa#s39%Cs3:G?#A,s3<Rs3=#&#-%C/#k##'#VSb1s3A(Gs3B)Ss&#Sr,#s3E$G#($s3G#$#k##)#VSc(s3J(s3KG)T#&#Ss,#s3N(s3O#$$G#$#k##)#VSd(s3S)SD&#T#A#s3V%C#Gk##@#VSe&s3Y)SF&#SD,#s3\%C#$k##s#&#VTg&s3_m#TQ#)SuVSa#s2u%Cs2vG?#)SvA#s2yRs2z#,%s2{&$#%C'#k##)#VSb)s3#(Gs3$)S`,#s3&$G#($s3(#$#k##(#VSc(s3+(s3,G)SR,#s3.(s3/#$$G#$#k##(#VSd(s33)S_A#s35%C#Gk##?#VSe&s38)Sw,#s3:%C#$k##s#$#VTg&s3=m#TQ#@Cs'`s'^@Cs'Y#T#S\@Cs'cs'Y@Cs'[#T#S\NS:#s'WNS:'#3Cs%0Ps'T3C#Ps'VQCI3C#Ps'W3C%P#'s*Z/#/#'#/#/#/#'#/#'#/#'#/#'#'#'#E#JCs+I4C#S)s%A5s'gKEEJ#QJCs&kOC&#4Cs%ES>#5s'kKEEJ#QCs'lKEEJ'#JCs+t4Cs%=S)#5s'oKEEJ#QJCs+e4C#S)s%N5s'rKEEJ#Q[TRs'sKEEJ&#4Cs'gS)s%P5s'uKEEJ#QCs'vKEEJ#s%>ZS]s'wKEEJN2s'xKEEJ$s'q#2s'yKEEJs%Ds'r#2s'zKEEJ)s's#2s'{KEEJ1s't#l#0#s'Zs'Tl#1s#,s'~#l#2s#2s()#j#3C#j#4C#j#5C#j#7R#&MH$s+h#&s+is',(%##%#&PM$#s,4$s,#P0$#(GS#(PS##s4{#k###S(k##&#k##(#k##-#k#3C#k#4C#k#5C#k#7R#)S?-S?.#\HO%#SxS2SPS|S`l#8;'#m##Ol#Cs#Ys#Z#l#Ds#`s#\#l#Es#fs#b#l#Fs#os#h#l#Gs#xs#q#l#Hs$'s#z#l#Is$*s$+#l#Js$2s$-#l#Ks$9s$4#l#Ls$Cs$;#l#Ms$Ms$E#l#Ns$Vs$O#l#9s$as$Z#l#:s(ws(t#l#;s)%s(|#l#<s$ks$e#j#Bs$m#U#Hj##s%%#1SR*FDs5Js5II#%s5L#s4X$s3fs&H(s&Is'S#$##s3j##'#j#%D#+D#j#&F#+F#1S_*FDs5Vs5UI#%s5X#s4d&s$|T1$s3s#($s'`#$##s3w##(#j#%D#+D#j#&F#+F#j###O1Sw*FDs5ds5cI#%s5f#s4r$s4$s&^(s&_s'm#$##s4(##'#j#%D#+D#j#&F#U#H1Sx*FDs5ps5oI#%s5r#s4~$s40s%,(s%-s'y#$##s44##'#j#%D#+D#1S?*FDs5zs5yM#%s5|#s5,$s4:s%<(s%=s('#$##s4>##'#j#%D#+D#j###O1Sf*FDs6)s6(P#%s6+#s57$s4Es%5(s%6s(2#$##s4I##'#j#%D#U#H1SS*FDs63s62S##%s65#s5A$s4Os%6(s%7s(<#$##s4S##'#1S@*FDs6;s6:N#%s6=#s5)?s('=I$#s%8(s%9s5=#$##'##)#j###OHM%S5#S6?#=M$#s%<)M-M.#&%#(s%A##(##+#1SG*FDs6Rs6QS(#<DP%s6U$#HS#%S5#S6?#=S#&s%BSu$$#)S#&#s6R(&##&##*#HN%S5#S6?#&s%CSv$s5D#($s5L#$##'#j###O=S+&s%BS`$$#)S+-S+.#&%#((##(#HS(%S5#S6?#=S%&s%BS_$$#-S%.#&s6_#('##'#VThS9S?%FS9S??#VT7$#%FS,Sf?#VT7$#j#O#O%FSTSS1T8*FDs7+s7*H#<DS9%s7.$#k#P#Oj#QF#1Sy*FDs71s70S@#<DS1%s74$#*FDs74s73S;,<DS,%s77H#j#$s78#<DS@ZT9s7:'$H#S?%s7;$0nSj$D$#$DH#%$##H#STj#Rs7=#<DS;XTSs7?#+HZTis7@D%,$#%DS,S;<DS<%s7C#s6O)SU&#SH$s#[#($s#W#$#k#S#Ok#Ts#j#k#P*#j#UD#<DSG%s7N##HS<%S5#S6?#=SH)SH&#S<$%#-SH.#&'#('##'#UIS;j#S$#j#T.#j#P2#]SgDSG5#STHIS(S+l#NBA#l#Ps#)s#(#j#Ps#0#[SgFS@s#5#SkHS%j#Vs#<#U#Hj#Vs#B#?s#?VTTSSSw=SS)SS%C$#[T5S2S9S;S@S*S?I)S9-S9.#&%#=S@$$#)S@-S@.#&%#=S9$$#0)#-S,.#&s5o#=S;$$#)S;-S;.#&%#=S,$$#0)#j###O)ST-ST.#&%#=SG$$#)S<I#s74$G$,s#Ns76$G#k##s+w#k##&#)Sh&#SUI#s8)$G$)SI&#S3,#s8-$G#k##s+m#k##(#@Cs+\s+aT#S\NS:#s+X3Cs+UNs)03Cs+UNs)43C$N#3Cs+WIs+V3C#Ns+X3C%N#'s)&FC#/s)(FC#OC%#FCs*d4C$S)#5s+\KEEJ#Q4C%SVs):5s+^KEEJ#Q4Cs):S>(5s+`KEEJ#QCs+aKEEJs)9#Cs+bKEEJs&Ks)52s+cKEEJ#s+\s)-2s+dKEEJs)/s+]#2s+eKEEJ&s+^#2s+fKEEJ*s+_#2s+gKEEJ-s+`#l#0#s+Fs+@l#17s+j#l#2>s+q#j#3C#j#4C#j#5C#j#6C#j#>C#j#7R#j#?R#j#@R#&MP$#S#%CNM(s&Ls+=#S(##s+BS4k###S1k##s&L#k##&#k##)#k##+#k#3C#k#4C#k#5C#k#6C#k#>C#k#7R#k#?R#k#@R#-SI.#(S3#=S-$#s#E=SI-S-.#)S-aHO)'&$#s#KS3NS%S1T4S<l#8@-#l#9s#Os#H#l#:s,_s,\#l#;s,is,d#l#<s#Zs#U#j#Ms#]#U#Hj##s#m#)SG-SG.#&%#=ST$$#NS:s,Vs,L3Cs*$S#s,H3C#S#s,J3Cs,IS#s,J3Cs'SS##3C%S##/s0*FC#4Cs)uS)#5s,KKEEJ#Q4C%S)s*'5s,MKEEJ#QCs,NKEEJ#s,MCs,OKEEJs*'s)s2s,PKEEJ#s,Is*#2s,QKEEJs)xs,J#2s,RKEEJ&s,K#2s,SKEEJ*s,L#l#0#s,2s,,l#10s,V#l#26s,]#j#3C#j#4C#j#5C#j#6C#j#7R#j#?R#j#@R#&MI$#P&PI$S####N#S%s'4k###S4k##s'7#k##&#k##*#k#3C#k#4C#k#5C#k#6C#k#7R#k#?R#k#@R#$GS3&s#@s#A(s$,#_HO%#s#Gs$.s#IS3NS1T4S<l#88'#l#9s$2s$+#l#:s-Bs-?#l#;s-Ls-G#l#<s$=s$8#j#Ms#9#U#Hj##s$J#ZSzs$Qs$Ks$Is#B#Hl#Ws$ds$W#l#Ns$is$f#j#Xs$k#U#Hj#Ys%Q#ZTjs%Ss%Rs%Ps$o#Hl#Os%Xs%U#j#Ss%Z#j#Ts%c#V#IHj##s%h#j##s%x#;s%ys%us%s#Hj#Ns%}#j#Ps&-#V#IHj##s&3#j##s&H#;s&Is&Cs&A#Hj#Ns&M#j#UD#V#IHj##s&X#j#ZD#SDs&fs&d#Hj#Ns&p#j#QF#V#IHj##s&}#j#ZF#SFs'1s'/#Hj#Bs'>#U#Hj##s)b#ZSzs)ps)cs)as'M#Hj#Ns)t#U#Hj##s+D#ZSzs+Us+Es+Cs*-#Hj#Ns+Y#U#Hj##s,:#>SF*S&Ls8Ks8JI#%s8M#s8H7SFI$#s,+&$s:7(s,-##%##(#j#-L#+L#j#.S&#+S&#*FDs:Ls:KMs+b%s:N#s9:$s9Ys-z(s-{s9L#$#9SuM:s-~s9]8$#%S$#s,5#'##s,@##,#j#=C#+C#j#%D#+D#j#&F#+F#05#>Su*S&Ls8ks8jI#%s8m#s8h7SuI$#s.3&$s:W(s.5##%##(#j#-L#+L#j#.S&#+S&#*FDs:ls:kMs*Z%s:n#s9Z$s9ys*X(s*Ys9l#$#9SvM:s*\s9}8$#%S$#s,U#'##s,`##,#j#=C#+C#j#%D#+D#j#&F#+F#05#j###O>Sv*S&Ls90s9/I#%s92#s9-7SvI$#s*n&$s:x(s*p##%##(#j#-L#+L#j#.S&#+S&#>S`*S&Ls9=s9<I#%s9?#s9:7S`I$#s*j&$s;)(s*l##%##(#j#-L#+L#j#.S&#+S&#j###O>SR*S&Ls9Ks9JI#%s9M#s9H7SRI$#s,?&$s;7(s,A##%##(#j#-L#+L#j#.S&#U#H>S_*S&Ls9Xs9WI#%s9Z#s9U7S_I$#s(V&$s;D(s(X##%##(#j#-L#+L#>Sw*S&Ls9cs9bM#%s9e#s9`7SwM$#s,S&$s;O(s,U##%##(#j#-L#+L#j###O>Sx*S&Ls9os9nP#%s9q#s9l7SxP$#s*}&$s;[(s+###%##(#j#-L#U#H>S?*S&Ls9zs9yS##%s9|#s9w7S?S#$#s+2&$s;f(s+4##%##(#>Sf*S&Ls:'s:&N#<LI%s:*$#7SfN$#s+*&$s;p(s+,##%##(#j###O7SSS+$#s+(&$s;w(s+*##%#>S@*S&Ls:7s:6S(#<LP%s::$#7S;S%$#s+#&$s<$(s+%##%#ZU5SASGS*NT6IPFCS41S<*FDs<7s<6$#%s<9#s;E7S<S46FCS4&s:T#%C%#$G%&&s<.$#s:`,(s<0%C#G(Gs:[$s.Is<~#$##&##)##,##s:d##/##4#j#%D#+D#PFCS=1SH*FDs<Os<N$#%s<Q#s;]7SHS=6FCS=&s:l#%C%#$G%&&s<F$#s:x,(s<H%C#G##8#&##)##s:y##,##1#j#%D#+D#j###OPFCS11SU*FDs<es<d$#%s<g#s;s7SUS16FCS1&s;&#%C%#$G%&&s<\$#s;2,(s<^%C#G##s#.#&##)##s;3##,##1#j#%D#U#HPFCS91Sh*FDs<zs<y$#%s<|#s<,7ShS96FCS9&s;;#%C%#$G%&&s<q$#s;G,(s<s%C#G##s#C#&##)##s;H##,##1#PFCS,1S3*FDs=1s=0$#%s=3#s;{7S3S,6FCS,&s<@#%C%#$G%&&s=($#s<7,(s=*%C#G#s<Fs<8#$##'##*##s/*##-##2#j###O7SIST6FCST&s)Z#%C%#$G%&&s=9$#s)\,(s=;%C#G(Gs)a$s)_s>-#$##&##)##,##s)k##/#PFCSk1Si*FDs=Ws=V$#%s=Y#s)c7SWS26FCS2&s)^#%C%#$G%&&s=N$#s=U,(s=P%C#G(Gs)e$s)es>B#$##&##)##,##s)p##/#7SyS76FCS7&s=^#%C%#$G%&&s=_$#s<X,(s=a%C#G(Gs=e$s<[s>S#$##&##)##,##s)v##/#j###OHS+%S5#S66FCT@$G#&$s=p$#s)q,&s=r%C#G(Gs)v$s)ts>d#$##&##)##,##/#7SJS.6FCS.&s=v#%C%#HS%%S5#S66FCS-$G#&$s>'$#s)y,&s>)%C#G(Gs=|$s)|s>w#$##&##)##,##/#HS*%S5#S66FCSB$G#&$s>6-S*.#$%#,(s>:%C#G(Gs={&s=|'$#s?-#%##'##*##/##2#j###O6FCS8$G#&$s>G-S4.#$%#,(s>K%C#G)S4(G#&$($#s??#%##(##+##0#HS=%S5#S66FCSX$G#&$s>Y-S1.#$%#,(s>]%C#G)S1(G#&$($#s?Q#%##(##+##0#6FCSP$G#&$s>i$#s)j,&s>k%C#G(Gs)o$s)ms?]#$##&##)##,#j###O6FCSM&#s>u$#s)j,%s>w%C#G(Gs<}$s)ms?i#$##&##)#6FCSY$G#6FCSl&#s?%-Sk.#$%#,'s?)%C#G)Sk(G#&$($#s?y#%##(##+#6FCSC&#s?3-S2.#$%#,'s?7%C#G)S2(G#&$($#s@+#%##(##+#j###O6FCSN,#s?B%C#G(Gs<$-S7.#&s<'#$#s@7#'##)#6FCSZ&#s?L-T@.#$%#6FCS{,#s?Q%C#G)S.(G#-S..#&&#$#s@G#'##*#6FCS[,#s?\%C#G(Gs)I$s(hs@N#$##&#j###O(Gs;/-SB.#&s;2#$#s@V#'#6FCSn,#s?j%C#G)SL(G#-SL.#&&#$#s@`#'#)SX(G#-SX.#&&#$#s@g#'#j###O-SP.#&s:R#$#s@m)SM(G#)SY-SY.#&%#$#s@tPFCSpWS<#SlSXj##s9pOj##s9BO6FCS}&s9$#,Hs@0%C#Gj#[C#XU6s9('IS,7U7S}ZSgC(%$#SC,$s@6%C#G7U8S|VSa#s@97U9T+A#s@;Rs@<#,%s@=&$#%C'#k##s/c#VSb)s@A7U:TM,#s@C$G#($s@E#$#k##s/c#VSc(s@H7U;T0,#s@J(s@K#$$G#$#k##s/a#VSd(s@O7U<T-A#s@Q%C#Gk##s/w#VSe&s@T7U=T,,#s@V%C#$k##s/|#A&s@Y7U>TN,#s@[VSas8ps?oAs6gs?pRs?q#,s6is?r&$#%Cs6k#k##s/\#VSbs6ms?v,s6[s?w$G#($s?y#$#k##s/Y#VScs6`s?|,s6Ls?}(s?~#$$G#$#k##s/W#VSds6Qs@&As6Ks@'%C#Gk##s/m#VSes6Ns@*,s6@s@+%C#s6Ak##s/q#As6Cs@.,s65s@/6FCSqVSa#s@z6FCT6A#s@|Rs@}#,%s@~&$#%C'#k##s0H#VSb)sA&6FCTP,#sA($G#($sA*#$#k##s0H#VSc(sA-6FCT1,#sA/(sA0#$$G#$#k##s0F#VSd(sA46FCSQA#sA6%C#Gk##s0\#VSe&sA96FCSt,#sA;%C#$k##s0a#A&sA>6FCS~,#sA@)U?VSa#s@U)U@A#s@WRs@X#,%s@Y&$#%C'#k##s0C#VSb)s@])UA,#s@_$G#($s@a#$#k##s0A#VSc(s@d)UB,#s@f(s@g#$$G#$#k##s0@#VSd(s@k)UCA#s@m%C#Gk##s0W#VSe&s@p)UD,#s@r%C#$k##s0\#A&s@u)Tk,#s@w)Tl&#TkVSa#sAg)Tm&#TlA#sAjRsAk#,%sAl&$#%C'#k##s16#VSb)sAp)Tn&#Tm,#sAs$G#($sAu#$#k##s17#VSc(sAx)To&#Tn,#sA{(sA|#$$G#$#k##s16#VSd(sB$)TU&#ToA#sB'%C#Gk##s1M#VSe&sB*)TV&#TU,#sB-%C#$k##s1S#A&sB0)UE&#TV,#sB3UTpT%VTqC#Ls5cL#L#L#MC#WTWC(#MC&MC(@Cs5js5q@C$#@C&#@C(#EsAZVTrC#WT:C#s5vVTrCsBEL/L#MC#WT:C&#MC&WT:C(#UTpsCtVTqC#WTWC#6WTWC$5WT:C-5@C$#@C&#@C*#@C-#@C3#T#S\VUF8#NS:#s5}NS:$#NS:%#NS:&#3Cs5{S%s5|QCS(3C#S%s5~QCS%3C#S%s6$3C%M#3C(S%#QCS+3C#S%s6(3C#Is6)3Cs3ePs6*3C$S%#3C(S%#JCsBi4Cs5xS>#5s6*KEEJ#Q4Cs5~S>%5s6,KEEJ#QCs6-KEEJs3M#2s6.KEEJ&s6'#4C)SVs5~5s60KEEJ#QZUGs61KEEJ#'s,HFC#WTsC.#OC#s6,4Cs3mSV#5s67KEEJ#Q2s68KEEJ)s61#FCs1CWTsC4#/sDIFC#OC%#4Cs,SSV#5s6?KEEJ#Q2s6@KEEJ1s69#4C'SVs645s6BKEEJ#QJCsC+OCs,Y#4Cs3|S>#5s6FKEEJ#QCs6GKEEJs,X#JCs:_4Cs3tS)#5s6JKEEJ#Q4Cs1<S)s4(5s6LKEEJ#Q[TRs6MKEEJ%#JCs:x4Cs3zS)#5s6PKEEJ#Q4C+S)s4.5s6RKEEJ#Q[TRs6SKEEJ%#4C3S)s6K5s6UKEEJ#QZS]s6VKEEJS=2s6WKEEJs1?s6P#2s6XKEEJ%s6Q#2s6YKEEJ(s6R#2s6ZKEEJ/s6S#2s6[KEEJ6s6T#2s6\KEEJ<s6U#2s6]KEEJ?s6V#2s6^KEEJs#(s6W#2s6_KEEJs#3s6X#l#0#s6>s68l#1s#<s6b#l#2s#Js6i#j#3C#j#4C#j#5C#j#6C#j#>C#j#\C#j#]C#j#^C#j#7R#j#?R#(PsCR#S*#k##s2p#k##s2yO&NMRsCWS*&#S#%C%#k##'#&&S%%CS(#k##*#%CS%G&S(S#$S%#&S%sCd(%##%#&S%S+$#s;;$s;,S%0$#&S*S($#s;R$s;@S*0$#$sCoS*$GS%(S%S*#$#k###S7k##'#k##)#k##.#k##3#k##9#k##;#k##?#k##s#&#k#3C#k#4C#k#5C#k#6C#k#>C#k#\C#k#]C#k#^C#k#7R#k#?R#7UHSG)Tt-Tt.#gHOsD3S#SZSN&%P#UIS%S*T'SOSRSJT;TUTVl#8s#9(#l#_s7qs7n#l#`s7{s7v#l#as$ZC#l#bs$^C#l#cs$es$`#l#ds$ls$g#l#es$us$n#l#fs$~s$w#l#gs%,s%$#l#hs%0C#l#is%3C#l#js%9s%5#l#ks%?s%;#l#ls%Gs%A#l#ms%Os%I#l#ns%Xs%Q#l#'s%[C#l#os%^C#l#ps%ds%`#l#qs%js%f#l#rs%rs%l#l#Cs%zs%t#l#Ds&'s%|#l#)s&*C#l#ss&,C#l#Es&1s&.#l#Fs&6s&3#l#Gs&=s&8#l#Hs&Ds&?#l#Is&Ls&F#l#ts&NC#l#us&QC#l#Js&Ws&S#l#Ks&]s&Y#l#Ls&es&_#l#Ms&ms&g#l#Ns&vs&o#l#vs&{s&y#j#ws=K#j#xs=V#V#IHj##s=[#j##s=v#;s=ws=ns'-#Hj#Ns={#j#ys>-#V#IHj##s>1#j##s>R#;s>Ss>Gs'4#Hl#,s'6s>V#j#ys'9#j#zs'?#V#IHj##s'C#j##s'N#;s'Os'Ks'I#Hj#Ns'R#j#{s'Z#V#IHj##s'_#j##s'k#;s'ls'is'g#Hj#Ns'p#j#|s'|#V#IHj##s('#j##s(<#;s(=s(5s(3#Hj#Ns(C#j#}s(R#V#IHj##s(V#j##s(l#;s(ms(ds(b#Hj#Ns(p#j#~s)%#V#IHj##s))#j##s)K#;s)Ls)=s);#Hj#Ns)O#j$#s)_#V#IHj##s)e#j##s*'#;s*(s)xs)v#Hj#Ns*-#j$$s*?#V#IHj##s*E#j##s*h#;s*is*Zs*X#Hj#Ns*n#j$%D#V#IHj##s+(#j#ZD#SDs+As+?#Hl#Vs+ns+V#j#Ss+p#j$&s+v#V#IHj##s+|#j##s,-#;s,.s,)s,'#Hj#Ns,3#j#-L#V#IHj##s,?#j#ZL#SLs,Ns,L#Hj#Ns,Y#j#.S&#V#IHj##s,g#j#ZS&#SS&s,xs,v#Hj#Bs-)#U#Hj##s-L#*FDsEZsEYMs56%sE\#sDH$sDgs55(s56sDZ#$#9S`M:s59sDk8$#%S$#s7C#'##s7N##,#j#=C#+C#j#%D#+D#j#&F#+F#*FDsElsEkMs3%%sEn#sDZ$sDys6j(s6ksDl#$#9SRM:s6nsD}8$#%S$#s7U#'##s7`##,#j#=C#+C#j#%D#+D#j#&F#+F#j###O*FDsF#sE~Ms3,%sF%#sDm$sE0s3+(s3,sE##$#9S_M:s3/sE48$#%S$#s7h#'##s7s##,#j#=C#+C#j#%D#+D#j#&F#U#H*FDsF5sF4Ms30%sF7#sE#$sEBs7/(s70sE5#$#9SwM:s73sEF8$#%S$#s7z#'##s8)##,#j#=C#+C#j#%D#+D#*FDsFEsFDPs34%sFG#sE3$sERs5](s5^sEE#$#9SxP:s5asEV8$#%S$#s8.#'##s89##,#j#=C#+C#j#%D#+D#j###O*FDsFVsFUS#s3;%sFX#sED$sEcs5t(s5usEV#$#9S?S#:s5xsEg8$#%S$#s8?#'##s8J##,#j#=C#+C#j#%D#U#H*FDsFfsFeNs3@%sFh#sET$sEss5r(s5ssEf#$#9SfN:s5vsEw8$#%S$#s8O#'##s8Z##,#j#=C#+C#*FDsFtsFsS+s3D%sFv#sFq$s3.s5w(s5xs3,#$#9SSS+:s5{s328$#%S$#s8]#'##s3:##,#j#=C#+C#j###O*FDsG'sG&S(s3K%sG)#s33$sEis5~(s6#sEg#$#9S@S(:s6&sEm8$#%S$#s8l#'##sG*##,#j#=C#U#H1S;*FDsG6sG5S%#<DS#%sG9$#$s3<s6,(s6-s3<#$#9S;S%:s60s3@8$#%S$#s8|#'##s3I##,#*FDsGCsGBS*s3P<DN%sGF$#&s63SF$sG9#($sF/#$#9SGS*:'sG=8$#DI%S$$##(##s3M##.#j###O$s3Es3X(s3Ys3C#$#9S<S4:s3\s3I8$#DM%S$$##(##s,=#*FDsG]sG\S=s-m<DS(%sG`$#$sGEs3T(s3Us3E#$#9SUS1:s3XsGI8$#DS#%S$$##(##s,7#&s6;SR$sG>#($s+}#$#9ShS9:'sGB8$#DN%S$$##(##s,3#j###O$s+ws3^(s3_s+v#$#9S3S,:s3bs+{8$#DS+%S$$##(#&s5QSx$s+o#($s+n#$#9SiSk:'s+s8$#DS%%S$$##(#)Sf&#S?$s2}#($s2{#$#9SWS2:'s3%8$#DS*%S$$##(#j###O9SyS7&s3/Sf:#sF/8%#DS4%S$$#&s3+SS$s2t#($s2r#$#9SJS.&s3$S@:#s+h8%#DS1%S$$#VThS-S<%FS-S<?#VT7$#%FSBSH?#VT7$#j#O#O%FS8SU1TX*FDsHSsHRH#<DS-%sHV$#9TuI)S3&#Sh:#sCq8&#DS7%S$$#k$'#Ok#P+#j#QF#1T;*FDsHasH`Sh#<DS.%sHd$#9TXS3:s3/s2@8$#DS2%S$$#1Tu*FDsHjsHiSI#<DS8%sHmH#j#$sHn#<DS3ZT9sHp'$I#SH<DSB%sHr%#nSj$D$#$DH#%$##H#SLj#RsHt#<DSIXTSsHv#,HZTisHwD%-$#%DS8SI<DSW%sHz#sH*)T8&#Sy$s54#($s52#$#9UJSK)SJ&#T8:#sGf8&#DSL%S$$#k$'#Ok#S+#k#Ts:r#k#P2#j#UD#<DSi%sI1##HSW%S5#S6)Sy&#SW$$#-Sy.#&'#('##'#9UKSJ:?@8$#DS8%S$$#I>sHC$G?)T$,#sHF$G#k##s=+#k##'#)Tv&#T$I#sI9$G$)TX&#T;,#sI=$G#k##s<}#k##(#3Cs<bIs<aOCs<Ms<UWULC#s<N4Cs<WSV#5s<`KEEJ#Ql#0#s<?s<9l#1(s<c#l#2s<ms<j#j#3C#j#4C#&IH:#I%CH#k#3C#k#4C#VH7T;l#8)$#l#9;4#l#:s=;s=8#l#;s=Es=@#l#<s#'A#:s#Cs#D%CT8#)SK&#SJ:#$9UMTv8#HDSP%S$$#j#[C#ZSgC(#ISJH9UNT$8#SJDSX%S$$#8,SKDSM%S$H#j$(S$#UT?SJZT9S$'$H#SI%S$$0UT?SKnS$#$$(RH#%$#=O$$)TOj#VS$#ZT9S$%#TQ+HVUOOHl#N$O#l$'*)#l$'51#l#NA?#j$'s#H#j#Ss#N#j#Ts#W#j#Ps#Z#^SgDSis#]#SLHIS1S%Ml#Ns#rs#q#l#Ps#zs#x#j$'s$&#j#Ps$,#\SgFShs$1#SLHS1Pj#Vs$@#U#Hj#Vs$F#?s$CVTTSUS;=SU%C#s5TVTTS-S*%Cs3ws3r[StSPSBSIS3S,SHM=S3$s-&#-S3.#&s$H#=SB$$#0(#)S8-S8.#&%#$#s4'&s4ms4,=S8$$#0&#j###O=Si$s-.#)SWI#sIU$G$,s$8sIW$G#k##s><#k##&#Is$5sJH$Gs$6&s#vSK,#sJK$G#k##s>/#k##'#3Cs=pNs=n3C#Ns=p3Cs=qIs;P3C#Ns;M3C%N#OCs4(s4w4C#S)s4v5s=qKEEJ#Q4Cs4xSVs;O5s=sKEEJ#Q4Cs;OS>'5s=uKEEJ#QCs=vKEEJs;N#2s=wKEEJ#s=ps4q2s=xKEEJ's=q#2s=yKEEJ*s=r#l#0#s=Xs=Rl#1/s=|#l#2s50s>'#j#3C#j#4C#j#5C#j#6C#j#>C#j#7R#j#?R#j#@R#-T$.#(SK#$sDcs#%=T$aHO%$#sD_sDes$?SKNS*S,SQSWl#8)s4d#l#9s#+s#%#l#:s>Zs>W#l#;s>ds>_#l#<s#4s#/#j#Ls#7#U#Hj##s#@#)Si-Si.#&%#=SL$$#3Cs>BMs;}3Cs;zN#3Cs>CNs>D3Cs9MN#3C%N#4Cs;mS)s5F5s>CKEEJ#Q4Cs5HSVs4Y5s>EKEEJ#QCs>FKEEJs4Ws;zCs>GKEEJs;vs;k2s>HKEEJ#s>As;n2s>IKEEJs;ps>B#2s>JKEEJ&s>C#2s>KKEEJ(s>D#2s>LKEEJ+s>E#l#0#s>+s>%l#1/s>O#l#2s5_s>V#j#3C#j#4C#j#5C#j#6C#j#>C#j#7R#j#?R#j#@R#$s4XS#%CNS#$Ns;g##S((GN(S#N#S4#k###S1k##&#k##(#k##+#k##-#k#3C#k#4C#k#5C#k#6C#k#>C#k#7R#k#?R#k#@R#$GSK(s#fsEA=SCaHO%$#sEJs%$s#GSKNS%S,SQSWl#8;'#l#9s#ls#f#l#:s??s?<#l#;s?Is?D#l#<s#us#p#j#Ls#;#U#Hj##s#~#ZSzs$&s$#s#}s#D#Hl#Ws$4s$,#l#Ms$7s$6#l#Ns$;s$9#j#Xs$=#U#Hj#Ys&'#ZTjs&)s&(s&&s$A#Hl#Os&.s&+#j$'s&0#j#Ss&7#V#IHj##s&=#j##s&K#;s&Ls&Gs&E#Hj#Ns&R#j#Ts/u#V#IHj##s&_#j##s0?#;s0@s&ls&j#Hj#Ns&w#j#Ps'&#V#IHj##s'+#j##s'C#;s'Ds'9s'7#Hj#Ns'H#j#=C#V#IHj##s'Y#j#ZC#SCs'ks'i#Hj#Ns'y#j#UD#V#IHj##s(.#j#ZD#SDs(Bs(@#Hj#Ns(R#j#QF#V#IHj##s(e#j#ZF#SFs({s(y#Hj#Bs)1#U#Hj##s3}#ZSzs44s3~s3|s)F#Hj#Ns4B#U#Hj##s=v#ZSzs>As=ws=us4e#Hj#Ns@X#m##s@XVHs>b#l#Ns@4s@2#XTSsM[s@cs@b#%sM\s@cs@dm#$#l$*sLcsLd#j$+s@k#j$,s@s#V#IHj##s@|#j##sA2#;sA3sA0sA(#Hj#NsA;#j$-sAG#V#IHj##sAP#j##sAj#;sAksAdsA\#Hj#NsAs#j$.sB'#V#IHj##sB0#j##sBR#;sBSsBHsB@#Hl#NsDasB[#j$/sDf#j$0sDl#V#IHj##sDs#j##sE&#;sE'sE%sDy#Hj#NsE-#j$1sE6#V#IHj##sE:#j##sEQ#;sERsEKsEC#Hj#NsEU#j$2sE`#V#IHj##sEe#j##sF$#;sF%sExsEp#Hj#NsF)#j$3sF7#V#IHj##sF;#j##sF\#;sF]sFQsFI#Hl#,sFosF`#j$4sFq#j$5sF~#V#IHj##sG0#j##sGN#;sGOsGFsG>#Hj#NsG\#j$6sGr#V#IHj##sH$#j##sHW#;sHXsHCsH;#Hj#NsHd#j$7sI+#V#IHj##sI2#j##sI}#;sI~sI]sIU#Hj#NsJ(#j$8sJQ#V#IHj##sJU#j##sLD#;sLEsK+sK##Hl#NIsLK#j#ysLM#j$9sLW#V#IHj##sLZ#j##sLu#;sLvsLmsLe#Hl#NS=sLx#USBsM%]S1S%S(S+NS#PMIHZSgsNQsM&sL|%$#j$:sM+#j$;sM0#j$<sM7#j$=sM=#j$>sM@#j$?C#j$@C#j#%D#j#&F#WT[S9S=S4m#$#j$AsMN#j$BsMQ#j$CsMS#j$DsMU#l$EsMWsMX#l$FsM^sM_#l$GsMhsMi#j$HsNc#j$IC#j$JC#j$KUP#j$LUQ#j$MsNh#j#$sNi##"). Qed.

Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof. try hcb. try hsb.
  intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

Lemma rfree_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof. try hcb. try hsb. intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

(* [comment removed for export] *)
Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> hceil <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof. try hcb. try hsb.
  intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
  hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *.
  destruct H as [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC. lia.
Qed.

(* [comment removed for export] *)
Lemma rknown_byte st m (q : aptr) r v :
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v ->
  bytes_at usegs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof. try hcb. try hsb.
  intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

(* [comment removed for export] *)
Lemma rimplT_queue {R} o h g st0 (k : mstate -> Malloc.M R) bail s Q ms :
  (m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
  rimplT o (queue h g st0 k bail) s Q ms.
Proof. try hcb. try hsb.
  intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
  assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
  assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
  specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.

Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof. try hcb. try hsb. reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : hceil <= lo.

Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
  rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
  (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
  (exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
  oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
  rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof. try hcb. try hsb.
  intros RP PE FP KI ZI FR RES OOK MRX ER ES.
  destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
  unfold rntf_q. do 16 eexists. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
  split. { eapply rpres_except_trans; [exact PE|]. eapply rpres_except_mono; [exact PE'|]. exact FP. }
  split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
  eapply oracle_ok_frame; [| exact ER | exact ES]. eapply roracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> Malloc.M R) (bail : Malloc.M R)
    (s : PState) (Q : R -> PState -> machine_state -> Prop)
    (ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
  KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
  rmrep st m -> mem_inv usegs m -> oracle_ok o m st ->
  stk usegs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
  (forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
  rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x6c904) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  induction fuel as [|f IH]; intros until Zs; intros KI LP ZI MR MI OOK ST DEPTH KH.
  { cbn [nontrivial_free]. apply rimplT_undef. }
  rewrite ntf_unfold. cbv zeta.
  pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
  pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
  pose proof (go_slot _ _ _ GO) as MSL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
  set (ms0 := MS _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (ENTRY : entry_hyps st g i ->
    evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
  { intros EH. subst ms0. eapply rntf_entry; eauto. }
  (* [comment removed for export] *)
  assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
                       (G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
                       (G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
                             m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
             entry_hyps st g i).
  { intros. constructor; auto.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - pose proof (go_sc _ _ _ GO). lia.
    - intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
    - intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
    - split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
  destruct (ntf_cond st g i) eqn:HC.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
      rfg_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
              (m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
      (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
      wmono usegs m m2 -> oracle_ok o m2 stX ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
    { intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
      pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
      unfold rfg_post in FGP. destruct FGP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
      set (stU := fg_usage_st stX g) in *.
      assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
      assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
      rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
      rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).
      (* [comment removed for export] *)
      assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
      { destruct (data_of_fields _ _ g DATX) as (_ & EA & EF & EL & _).
        unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
        unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
        pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
        apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
          try lia; try exact HALL.
        - exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
        - destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tauto.
        - destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tauto. }
      assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
      assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; exact LPX).
      assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact GNX)).
      rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
          [ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
          | pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact Hj) ltac:(rewrite RU; apply ALLFREE; [exact Hj| exact NE])) as FC;
            rewrite RU in FC; exact FC ])).
      fold stG in GD. destruct GD as (KIG & NGM & NSL).
      assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; exact MR3).
      assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; exact FRX).
      assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).
      (* [comment removed for export] *)
      pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
      pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
      replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
      change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
      destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
      - (* [comment removed for export] *)
        assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
        rewrite free_meta_eq.
        eapply rimplT_evt.
        { eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
            first [exact MRG | exact MI3 | exact MSG | exact MWU | exact MEMU | exact MLNZ | exact FR3 | exact ST3 | exact LO | exact LOLE | reflexivity
                  | apply munch_refl | apply wmono_refl | idtac].
          - pose proof (ki_cx _ _ _ KIG) as (SQ & _). exact SQ.
          - intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [exact GNU| exact Hhd]. }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try exact RP.
        + destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
            (eapply rpres_except_mono; [exact PE3| exact FPX]).
        + intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | exact Ha].
          unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
        + eexists. apply KINV_fm; [apply KINV_seq; exact KIG| | | |].
          * unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [exact MSG|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros [b Hb]. apply NGM. exists b. unfold hosts in *.
            replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [exact Hb|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [exact GNU|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
        + apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + (* [comment removed for export] *)
          pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8).
          set (stS := record_seq _ (step_seq stG)) in *.
          assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; exact GNU).
          unfold fm_st. apply frame_queue.
          * apply frame_put_meta; [apply frame_seq; exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
          * apply links_put_meta0; [exact (ki_links _ _ _ KIS)| exact GNS].
          * cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
            intros hd Hhd. destruct (kinv_free_head stS LB _ hd KIS Hhd) as (_ & NX' & _).
            rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| exact NX'].
          * right; exact (hosts_is_gm _ _ _ HOSTS).
        + (* [comment removed for export] *)
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & FS2 & FS3 & _).
          destruct (go_region _ _ _ GOX) as (r & Hr & Kr & _ & _ & _ & TOP). rewrite <- RU in TOP.
          change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
          pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
          unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [exact SND| split]]]].
          * unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
          * exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
          * intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
            apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
            apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; exact MLNZ | exact ALLFREE | exact Hb' | exact E].
        + eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [exact OOK2 | exact MRW | exact LO | exact PE3].
        + exact MRG.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (_ & SR2 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (_ & FS2 & _). rewrite FS2, SR2. reflexivity.
      - (* [comment removed for export] *)
        assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).
        (* [comment removed for export] *)
        pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
        destruct (NEST MLZ) as (g1 & i1 & b1 & SL1 & HB1 & FB1 & PSS & I1 & NF1 & LT1 & v3 & lo8 & hi8 & K3 & V31 & K2 & K1 & OFF).
        clear NEST.
        pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
        destruct (go_region _ _ _ GOX) as (r & Hr & Kr & SP0 & SP16 & SPAN & _).
        destruct (go_region _ _ _ GO1) as (r1 & Hr1 & _ & SB0 & SB16 & SPAN1 & _).
        rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
        assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
        assert (B1LT : snd b1 + 16 <= snd p).
        { rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
          pose proof (go_stride _ _ _ GO1) as [S16 _].
          assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
        assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
        assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; exact HB1).
        assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [exact NEb1| exact HB1U]).
        (* [comment removed for export] *)
        pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
        assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
        { split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
          rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
          unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
          rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
          assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
          unfold UNIT, IB in *. lia. }
        destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].
        (* [comment removed for export] *)
        unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
        apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
        assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
        { intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
          unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
        rewrite !ESH.
        rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; exact K4).
        rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; exact K3).
        rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; exact K2).
        rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; exact K1).
        cbn [Z.eqb negb].
        set (off16 := lo8 + 256 * hi8).
        assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
        { unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
        rewrite EB. unfold get_group.
        replace (s_groups stG !! b1) with (s_groups stX !! b1).
        2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
        destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
        apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
        apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
        (* [comment removed for export] *)
        assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
        change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
        rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
        destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
        apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
        apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
        (* [comment removed for export] *)
        assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
        assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
        assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
                   bytes_at usegs m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
        { intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; exact Hr) Kr ltac:(cbn; lia)
                   ltac:(cbn; unfold get_shadow; rewrite ESU; exact Hc)) as [B V].
          cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; exact Hr). cbn [snd] in B.
          rewrite (conc_region' stU p r) by (rewrite ERU; exact Hr). split; [| exact V].
          replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. exact B. }
        destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
        destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
        assert (HDR : bytes_at usegs m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
        { change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
          apply bytes_at_app. split; [exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; exact Y3|].
          apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; exact Y2|].
          cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. exact Y1. }
        (* [comment removed for export] *)
        destruct HOSTSX as [aig Hghp].
        eapply rimplT_evt.
        { eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
          all: first [exact MR3 | exact MI3 | exact MWU | exact MLZ | exact MEMU | exact HDR | exact FR3 | exact ST3 | exact LO | exact LOLE
                     | exact R3 | exact R2 | exact R1 | exact AR1 | exact G15 | apply rntf_frame_size | idtac].
          all: try reflexivity.
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
          all: rewrite ?EU1.
          all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
               try exact G12; try exact G13; try exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
          all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); lia).
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
          all: try (unfold stU; rewrite fg_usage_groups; first [exact Hghp | exact Hgh1]).
          all: try (symmetry; exact EB).
          all: match goal with
               | |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
               | |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
                                   apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
               | |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
                                   fold off16 in G17; unfold UNIT in G17;
                                   replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
                                   rewrite Z.div_mul in G17 by lia; lia
               | |- ?G => idtac "NCGOAL" G; fail
               end. }
        intros ms3 NC. unfold rnest_call_post in NC.
        destruct NC as (z0 & z1 & z2 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
        fold stG in MR4.
        (* [comment removed for export] *)
        pose proof (bv_unsigned_in_range _ sp) as SPR'.
        assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in LO; rewrite unsigned_lit; lia).
        rewrite V31. replace (conc stU g1) with (conc stG g1) by reflexivity.
        eapply (IH R _ bail s Q (Z_to_bv 64 0x6cb8c) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
        + exact KIG.
        + constructor.
          * exact HB1G.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact I1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact NF1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
            apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
            pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
            pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
        + unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + exact MR4.
        + exact MI4.
        + apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [exact OOK2 | exact MRW | exact LO |].
          eapply rpres_except_trans; [exact PE3|]. eapply rpres_except_mono; [exact PE4|].
          intros a Ha. eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha].
        + rewrite SPU. exact ST4.
        + rewrite SPU. lia.
        + (* [comment removed for export] *)
          intros st3 mi ms5 NQ. rewrite free_meta_eq.
          unfold rntf_q in NQ. rewrite SPU in NQ.
          destruct NQ as (u0 & u1 & u2 & ra0' & ra1' & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MI5 & ST5 & MR5 & PE5 & [c3 KI3] & ZI3 & FR35 & RES5 & OOK5).
          replace (ret_pc (Z_to_bv 64 0x6cb8c)) with (Z_to_bv 64 0x6cb8c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
          assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
          { apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
          assert (NGM3 : ~ is_gm st3 g).
          { intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). exact Hb. }
          eapply rimplT_evt.
          { eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
              first [exact MR5 | exact MI5 | exact LO | exact LOLE | reflexivity | idtac].
            - unfold meta_slot. rewrite (nf_areas _ _ FR35). exact MSG.
            - intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; exact GNU| exact Hhd].
            - unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
            - eapply rpres_except_rw_cells; [exact PE5 | exact FR4 |].
              intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
            - exact ST5. }
          intros ms6 RP. apply KH.
          pose proof (frame_trans _ _ _ FRG FR35) as FR03.
          pose proof (fm_shape st3 g) as (FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
          eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try exact RP.
          * destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE3| exact FPX]|]);
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha]]|]);
              (eapply rpres_except_mono; [exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [exact FRG| lia| exact Ha]]).
          * intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [exact FR03| lia| exact Ha].
          * exists c3. apply KINV_fm; [exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); exact MSG| exact NGM3| rewrite RG3; exact GNU|].
            intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). exact Hs.
          * apply ZINV_fm. exact ZI3.
          * unfold fm_st. apply frame_queue.
            -- apply frame_put_meta; [exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
            -- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; exact GNU].
            -- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
               intros hd Hhd. destruct (kinv_free_head st3 LB _ hd KI3 Hhd) as (_ & NX' & _).
               rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; exact GNU| exact NX'].
            -- right; exact (hosts_is_gm _ _ _ HOSTS).
          * destruct mi as [[bb len]|]; [| exact RES5].
            destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
            unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
            split; [exact A1|]. split; [exact LEN|]. split; [exact SND|]. split; [exists rr; rewrite FS1; auto|].
            intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
          * exact OOK5.
          * exact MR5.
          * exact FS1.
          * exact FS2. }
    (* [comment removed for export] *)
    assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
      s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
      (m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
      rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono usegs m m4 -> mem_inv usegs m4 ->
      stk usegs m4 lo (bv_unsigned sp + -96) -> rw_cells usegs m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
      ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
               F (Z_to_bv 64 0x6cb2c) fc None m4 (seg_rom usegs) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
    { intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
      assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
      eapply rimplT_evt.
      { eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
          first [exact MR4 | exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | exact USX | exact FR4 | apply rntf_frame_size | exact ST4 | exact LO | exact LOLE]. }
      intros ms5 FGP.
      eapply (FG2 stX m4 junk); [exact KIX | exact ZIX | exact LPX | exact FRX | exact GNX | right; exact PE4 | exact FGP | | exact WM4 | | exact DATX | exists m4; exact MR4].
      - intros a Ha. eapply (rfree_fp_same st stX); eauto.
      - apply (oracle_ok_frame o m4 st stX); [| exact ERX | exact ESX].
        eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [exact OOK | exact MR | exact LO | exact PE4]. }
    destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
    + (* [comment removed for export] *)
      apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
      set (sc := m_sizeclass (get_meta_rec st g)) in *.
      set (an := optr_eqb (active st sc) (Some g)).
      set (stm := deq_mid (LActive sc) g st).
      set (st1 := dequeue (LActive sc) g st).
      assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
      pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
      pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
      assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
      assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; exact ZI).
      assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [exact SBL1| exact LP]).
      assert (FR1' : ntf_frame st st1).
      { unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
      destruct (kinv_next _ _ _ _ _ KI NX) as (MSnx & Pnx & Nnx & pv & PV & MSpv & Npv & NEpv).
      pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
      destruct DS as (DSdata & GN1 & GP1 & _).
      (* [comment removed for export] *)
      assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono usegs m m2 ->
        rat9c_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
                   (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (match an, active st1 sc with
                 | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
                 | _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
                 end) s Q ms2).
      { intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
        unfold rat9c_post in AP. destruct AP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
        assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
        { destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE3]| eapply rpres_except_trans; [exact PE0| exact PE3]]. }
        (* [comment removed for export] *)
        assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
        { pose proof (rmeta_slot_bounds st m g MR MSL) as (B0 & B1 & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in B1.
          rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
          - destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
            pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. pose proof (rmeta_slot_bounds st m h MR MSh) as (C0 & C1 & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in C1.
            unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). exact E.
          - unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
        assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
          evt usegs (rat00_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x6cac8) fc None m3 (seg_rom usegs))).
        { intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
          eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
            first [exact MR3 | exact MI3 | exact HA3 | exact FR3 | apply rntf_frame_size | exact ST3 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBLm| exact MSL].
          - pose proof (go_sc _ _ _ GO). subst sc. lia.
          - rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
            destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
            destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
            destruct Hba as [ai Hgh]. pose proof (ki_grps _ _ _ KI1 ba _ Hgh) as (g' & Eg' & AI). cbn in Eg', AI. inversion Eg'; subst g'.
            split; [exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
            exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
        assert (AVK : forall a, an = true -> active st1 sc = Some a ->
                 rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x6cac8) fc None m3 (seg_rom usegs))).
        { intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
          change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
          set (stA := act_st st1 a (act_of st1 a)).
          destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
          assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
          eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; exact AV0|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX stA m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4.
          - unfold stA. apply KINV_act; [exact KI1| exact GMa| exact AV0| apply act_of_nonneg].
          - unfold stA. apply ZINV_act. exact ZI1.
          - unfold stA, act_st. apply LPRE_upd_other; [exact NEa| exact LP1].
          - unfold stA. apply frame_act; [exact FR1'| eapply (LG_frame st st1 a FR1'); left; exact Na].
          - unfold stA. rewrite act_st_rec_other by congruence. exact GN1.
          - unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
          - unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
          - unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
          - unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
          - unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
            change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
            apply (ki_usage _ _ _ KI1). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        assert (NOACT : (an = false \/ active st1 sc = None) ->
                 rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x6cac8) fc None m3 (seg_rom usegs))).
        { intros NA.
          eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
          rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX st1 m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4; try exact KI1; try exact ZI1; try exact LP1; try exact FR1'; try exact GN1.
          - apply DSdata.
          - apply (sbl_regions _ _ SBL1).
          - apply (sbl_shadow _ _ SBL1).
          - apply (sbl_groups _ _ SBL1).
          - intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| exact SC48b]|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); congruence).
      * (* [comment removed for export] *)
        destruct D as (_ & NXg & _ & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx = g) by congruence.
        eapply rimplT_evt.
        { eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - rewrite NX, Enx. reflexivity. }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
      * (* [comment removed for export] *)
        destruct D as (_ & _ & nx' & NX' & NE & x0 & x1 & x2 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx' = nx) by congruence. subst nx'.
        eapply rimplT_evt.
        { eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact NX | exact PV | exact NE | exact MSnx | exact MSpv | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | reflexivity | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - apply NEpv. exact NE.
          - destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
            exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
    + (* [comment removed for export] *)
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as (nx0 & D3 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
      eapply (FGX st m1 junk); [exact KI | exact ZI | exact LP | apply frame_refl | exact NX | reflexivity | reflexivity | reflexivity | reflexivity
                               | | eapply rpres_except_entry; eauto | exact WM | exact MI1 | exact ST1 | exact FR1 | exact MR1 | reflexivity].
      intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
  - destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
    + (* [comment removed for export] *)
      apply Z.eqb_eq in HM.
      apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.
      (* [comment removed for export] *)
      assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
        stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
        (active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
        forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
                      x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (k (aor_st stq g i) None) s Q ms2).
      { intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
        assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
        assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); exact ZI).
        assert (KIq : KINV stq LB c).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [exact KI|].
          apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
        assert (FRq : ntf_frame st stq).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
          apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
          cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
        unfold rqpath_post in QP. cbv beta in QP.
        destruct QP as (qa0 & qa2 & qa3 & qa5 & m2 & -> & PE2 & WM2 & MI2 & ST2 & FR2 & MR2).
        pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
        rewrite <- (conc_sbl st stq g SBL).
        eapply rimplT_evt.
        { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
            first [exact MR2 | exact MI2 | reflexivity | exact FR2 | exact ST2 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBL| exact MSL].
          - pose proof (go_li _ _ _ GO). lia.
          - destruct (data_of_fields st stq g (sbl_data _ _ SBL g)) as (_ & _ & -> & _). exact (go_freed _ _ _ GO). }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try exact RP.
        * eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [exact FRq| lia| exact Ha].
        * exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
        * apply ZINV_aor. exact ZIq.
        * apply frame_aor; [exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
        * exact eq_refl.
        * apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
          eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO|].
          eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * exact MR2.
        * reflexivity.
        * reflexivity. }
      destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
      * (* [comment removed for export] *)
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
        { destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia | exact HAct]|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - right. exists g. split; [exact HAct| exact MSL].
          - intros NE. exfalso. exact (NE HAct).
          - intros hd Hhd NE. exfalso. apply NE. congruence. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| exact QP].
      * (* [comment removed for export] *)
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
        { intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
        apply rimplT_queue. intros GN GPV.
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia]|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as [D3 _]; congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
            exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
          - intros _. split; assumption.
          - intros hd Hhd NE. destruct (kinv_active _ _ _ _ _ KI Hhd) as (_ & Shd & Nhd & _ & _ & pv & Ppv & Spv & Npv).
            split; [exact Shd|]. exists pv. split; [exact Ppv|]. split; [| exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros _; split; assumption| exact QP].
    + (* [comment removed for export] *)
      apply Z.eqb_neq in HM.
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y0 & y2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
      eapply rimplT_evt.
      { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
          first [exact MR1 | exact MI1 | exact MSL | reflexivity | exact FR1 | exact ST1 | exact LO | exact LOLE | idtac].
        - pose proof (go_li _ _ _ GO). lia.
        - exact (go_freed _ _ _ GO). }
      intros ms2 RP. apply KH.
      eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try exact RP.
      * eapply rpres_except_entry; eauto.
      * auto.
      * exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
      * apply ZINV_aor. exact ZI.
      * apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
      * exact eq_refl.
      * eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO| eapply rpres_except_entry; eauto].
      * exact MR1.
      * reflexivity.
      * reflexivity.
Qed.
End NTF.

End HCW.

