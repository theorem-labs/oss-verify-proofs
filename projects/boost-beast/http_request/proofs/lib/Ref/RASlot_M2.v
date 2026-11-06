(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W9 RASlot_W12 RASlot_W19 RASlot_M0.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RBand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : hceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.

(* [comment removed for export] *)
Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
  mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
Definition rHAG_stmt : Prop :=
  forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
  IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
  am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
  rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -144) ->
  rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk) ->
  rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
  brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
  rimplT o (ag_body f sc req k bail st2 mm) s' Q
    (MS (rag_regs (Z_to_bv 64 0x691f0) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) t3' t4' t5' t6')
        F (Z_to_bv 64 0x691fc) fc None m3 (seg_rom rsegs)).
Hypothesis HAG : rHAG_stmt.

Lemma rerrno_lit2 : errno_addr tp = 0x925ac.
Proof. try hcb. try hsb. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof. try hcb. try hsb.
  intros REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
  destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

(* [comment removed for export] *)
Lemma rta_fp_malloc_fp stE mE a :
  rmrep stE mE -> mrel st stE -> (forall q, meta_slot st q -> meta_slot stE q) ->
  rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 stE lo (bv_unsigned sp) a.
Proof. try hcb. try hsb.
  intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - left. left. exact X.
  - left. right. right. left. exact X.
  - left. do 3 right.
    pose proof (AREAS q MSq) as MSq'.
    destruct (rmeta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
    exists rid0, r0. split; [exact H0|]. split; [exact K0|].
    rewrite (rconc_meta_stable stE q REL MSq) in L0, H0'. lia.
  - do 3 right. left. pose proof MR as (WF & _).
    destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
    destruct ER as [_ EG EGR _ _ _ _ _].
    destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
    exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
    rewrite Cb in Xq. lia.
Qed.

(* [comment removed for export] *)
Lemma rta_fp_not_image a : 0x10000 <= a < 0xb4000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof. try hcb. try hsb.
  intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO. lia.
  - exact (Hc X).
  - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
  - pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
    destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
    pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof. ltac2:(KReplay.runch [|@a|] [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RAllocSlot_iface.RAS_STACK_ge); constr:(sc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RAllocSlot_iface.RAS_STACK); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(sp); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RASlot_W9.rta_fp); constr:(st); constr:(lo); constr:(@kc__1); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.RCTX); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.aptr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocRep.meta_slot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.conc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ghdr); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.option); constr:(@stdpp.base.lookup); constr:(@stdpp.gmap.gmap); constr:(@stdpp.decidable.prod_eq_dec); constr:(@Corelib.Numbers.BinNums.N); constr:(@stdpp.numbers.N.eq_dec); constr:(@stdpp.numbers.Z.eq_dec); constr:(@stdpp.countable.prod_countable); constr:(@stdpp.countable.N_countable); constr:(@stdpp.countable.Z_countable); constr:(@stdpp.gmap.gmap_lookup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.s_groups); constr:(@Corelib.Init.Datatypes.Some); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(LO); constr:(CLO); constr:(@kc__2); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocKit_B.rmeta_slot_bounds); constr:(m); constr:(MR); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.ge); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.rmrep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.rregions_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.rmrep_ctx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.rmrep_globals); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.rmrep_areas); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.rmrep_groups); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.rmrep_shadow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMallocRep.rgroup_conc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.region); constr:(@Corelib.Init.Datatypes.fst); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.s_regions); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.r_base); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.rkind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.r_kind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.RKGroup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.round_up_pg); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.r_len); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Logic.not); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.aptr)); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ghdr)); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.region))|] [|@q; @gh; @b; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__p1; @__p2; @__arith; @__sat12; @__sat13; @__sat14; @__sat15; @X; @__x3; @__x4; @__x5; @__p3; @__x6; @_H0; @GC; @H; @_H; @a8; @Xq; @MSq; @x; @r; @__x7; @__x8; @__x9; @__sat17; @__sat18; @__sat19; @__sat20; @__sat21; @HCEILB1; @RC; @RB0; @M16; @BE; @B0; @Kb; @Cb; @Hrb; @rb; @e; @WF; @Hbq; @bq; @HCEILB0; @ASG; @HCANB; @HSECB; @HCEILB; @a|] "#3.#j$s#m$Q#y##$R$1$P$:$*$4#$$C#+#(%##)#,#j#*#%$Y#3#-#'#1#/#5%(%*#x$[#.#&#0#4#o$+#2#7$s#6#9$.#8#;$;$E$H$X#<#?$>$n$o#F#=#G#u#|$$$6$<$8$@$D$F$_$`$h$d$i$c$m$t#B#:#>#Y#i#n#v#w#z#}#~$#$%$'$&$($)$9$=$?$A$G$I$K$M$O$Z$\$^$a$b$]$l$r#@$w$x$y$z${$|$}$~%%#A#C#D#E#H#I#J#L#W%-#X%.#P#c#e%/#p#q#s$/#{$5#t$u%'$0%&$3%,%+$N$J#r$-$V$U$7$q$W%)$L$f$T$g$e$k$v$B$j%$$S$p$2$,I$M%$N%$O$$P%$Q%$R&$S$$T%$U&$V%$W$$X%$Y$$Z$$[+$\'$]$$^%$_'$`*$a)$b($c%$d$$e%$f%$g)$h$$i&$j%$k%$l%$m&$n&$o*$p($q%$r)USbS6)SL)#)#)#)#)#)#)#)#)#)#)#)#)#%#)#)#)#)#)#)#)#)#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#3#UScS6$$#)s#&)#)#)#)#)#)#)#)#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#3#$s#%##s#%#m#s#W#USdS0USeS0$E#%SL3#%$%#%#%#%#3#VSM)#'-##-#m#0#USfS0USgS0$E#'$)#$#m#'#WShS6S0SN)3)#%#%#%#%#3#USiSN$$#USj8VSk#Sl$#PXSmKS7$R$S7S%'S%&#$#$S=S%%s#})#%#%#%#%#%#3#&S=#'S%##-#GKF.KF$#O)s#4%#%#%#3#&)#'O##*##-#j#$H#,H#USOLXSnJS@CSPZSoJS@SFCSPSpXSQH$#LXSRH%$LUSqK7HL%$M#BLF(*$#.KM$#S#3s#7&%#'S###&##)#j#%L#,L#j#&H#,H#47#4s#&#4s#3#j###N$S7O'Os#;#$#3s#UVSSs#Z#'Es#[$E%VSMs#]&'E#k##%#k##'#$Es#aWSTs#b+Mj##SA#j#'%#$E*k##SA#k#'(#VSSs#hs#b$Es#c'Es#ck##$#k##3#WSTs#ms#gMj##SA#j#'0#$Es#ik##SA#k#'3#USrSBUSsSBUStC;CS&2C#M$2C%S&#2C#S&&USuCUSvC=#IDDGS*9Cs#K%s${9C#5C%SC#6(IDDG#S'E)IDDG(#USwD5C'S1)6,IDDG#S'=-IDDGP1.IDDG$&#1/IDDG('#VSx0GVSySUSVVSzFS&(SU#SVm$%#WS{CEMXS|FS&$#l#(*)#l#):9#l#*A@#j#+C#j#,C#j#-S$#j#.S$#'MF#S&#$MS&k###Pk##%#k#+C#k#,C#k#-S$#k#.S$#$S7S+ZFN#S+s$)POl#/.%#l#0s#6s#3#l#1s#>s#:#l#2s#Cs#@#l#3s#Ns#H#j#4s#Q#U#Fj##s$,#$S=O'Os$$#$#$s#~S#'S#s#x#$##s$&#j#$H#,H#$s#nS)'S)s#l#$##s#r#j#%L#,L#j#&H#,H#4+#42#$S=S#'S#s$7#$#$s$5S)'S)s$/#$##s$9#j#$H#,H#$s$%S2'S2s$##$##s$)#j#%L#,L#j#&H#,H#4+#42#j###N$S=S)'S)s$K#$#>SW>#>#>#>#<C#<C%<C'<C)<C+<CSW?C$#?C&#?C(#?C*#?C,#VSX#SYWSZSB#s#t;CM;CP2C#S3s#u2C%P#;CS*2Cs#wP#2C%P#=s#tIDDGS%%s%$%#)#%#)#%#)#)#%#)#)#)#)#%#%#%#3#%SL)#)#%#%#)#%#)#%#%#)#%#)#%#)#)#%#%#%#3#%6%#%#%#%#%#%#%#%#%#%#%#%#%#%#3#)s##%#%#%#%#%#%#%#%#%#%#%#%#%#%#3#@Cs##@Cs%RCC$#5Cs$_SC#6s$bIDDG#S'Es$cIDDGs#M#@Cs&P9Cs&%5C$S1#6s$gIDDG#S'=s$hIDDGOEs$iIDDG$#@Cs%o9Cs'(5C$S1#6s$mIDDG#S'9Cs%ZWS}Cs$k&5C$S1#6s$qIDDG#S'5C/S1&6s$sIDDG#S'=s$tIDDGS#1s$uIDDG$s$m#1s$vIDDG's$n#1s$wIDDG,s$o#1s$xIDDG1s$p#1s$yIDDGs$os$q#1s$zIDDG9s$r#l#(#s$ms$gl#)s#gs$}#l#*s#os%(#j#+C#j#,C#j#5C#j#6C#j#7C#j#-S$#j#.S$#j#8S$#&s#Ks%y'S*##P#$S3P$s&vS&##O$s&5RVS[RS%$P#$PRk###S4k##%#k##(#k##*#k##-#k##/#k#+C#k#,C#k#5C#k#6C#k#7C#k#-S$#k#.S$#k#8S$#$s#cS(bFNs&g#S(s&Gs&DS7s'.PS)S2S,SGSHl#/=%#l#0s%Qs%N#l#1s%Ys%U#l#2s%^s%[#l#3s%is%c#j#4s$M#U#Fj##s$c#$s&:S2'S2s&4#$##s&>#j#$H#,H#$s&*S,'S,s&(#$##s&.#j#%L#,L#j#&H#,H#4+#$s&IS,'S,s&C#$##s&M#j#$H#,H#$s&9S4'S4s&7#$##s&=#j#%L#,L#j#&H#,H#4+#j###N$s&YS4'S4s&S#$##s&]#j#$H#,H#$s&_S+'S+s&Y#$##s&c#j#$H#,H#j###N$s&fS8'S8s&`#$##s&j#j#$H#U#F$s&lS('S(s&f#$##s&p#GKM$s&[S5&s&\s&l'S5##%##'#j###N.KS&$#S-&$s&s'S-##%#GKS3.KS*$#S9&$s&y'S9##%#[S~S6S0KS:PS\M.KP'E#&$s'#$#s('%s'U%#%#%#%#%#%#%#%#%#3#$/s$Y)s%2%#%#%#%#%#%#%#%#%#%#%#%#%#%#3#$s$ZB44#3s'w*s#%#(C#E3>*s#(#%s&]%#3#A&##)##-##s#,##s#/#.KR'E#&$s'R$#s(V$$s$}$s$n'4$#*)6(C#E*+5A#2#%##(##,##/#j###N.KS%&#s'a$#s(e$$s%0$s$}&4$#*(s#%(C#E**s#$A#A#%##(##,#.KO'E#.KS#&#s'p$#s(t$$s%?$s%0&4$#*(s#4(C#E**s#3A#s#0#%##(##,#.KS)&#s'}$#s)%$$s%L$s%=&4$#*(s#A(C#E**s#@A#s#=#%##(##,#j###N.KS2&#s(/$#s%Y$s%J%4$#*'s#N(C#E*)s#MA#s#J#%##(#.KS,&#s(:$#s)>.KS4&#s(=$#s%g$s%X%4$#*'s#\(C#E*)s#[A#s#X#%##(#2Cs&PRs&N;CR2C#S*s'g2Cs'gR#2C&R#)s(P9C#@Cs(NCC$#5C#S1s%a6s'iIDDG#S'5Cs'hSC%6s'kIDDG#S'Es'lIDDGs%b#1s'mIDDGs'cs'es%T1s'nIDDG$s'f#1s'oIDDG(s'g#l#(#s'bs'\l#)0s'r#l#*s&ds'y#j#+C#j#,C#j#5C#j#6C#j#7C#j#9C#j#-S$#j#.S$#&Ps(c$#F&Rs(e'P##S%#$S*Rk###s%Mk##%#k##)#k#+C#k#,C#k#5C#k#6C#k#7C#k#9C#k#-S$#k#.S$#.KS;$#SIbFN#$SIs)6s)3S7s)yRS+T#S]SGSHl#/7&#l#0s(@s(=#l#1s(Hs(D#l#2s(Ms(J#l#3s(Xs(R#j#:s#8#j#;s#D#V#MFj##s#I#j##s#`#8s#as#Xs#V#Fj#<s#e#j#=s#s#V#MFj##s#w#j##s$7#8s$8s$,s$*#Fl#>s$js$;#j#?s$l#j#@s$r#V#MFj##s$u#j##s%%#8s%&s$~s$|#Fj#<s%(#j#$H#V#MFj##s%/#j#AH#FHs%9s%7#Fj#<s%?#U#Fj##s%Q#$s),S+'S+s)*#$##s)0#j#%L#,L#j#&H#,H#$s)4S8'S8s)2#$##s)8#j#%L#,L#j#&H#,H#j###N$s)=S('S(s);#$##s)A#j#%L#,L#j#&H#U#F'S5s)B#s%I##s)H#j#%L#,L#7HLs)Ps)OS&s)N(s)T#s)M&s%Is)J'S-##s%J##&#j#%L#,L#j###N7HLs)Ys)XS3s)W(s)]#s)V.KS3$#S;&$s)U'S;##%##(#j#%L#U#F7HLs)cs)bS*s)a(s)g#s)`&s%Vs)]'S9##s%W##&#7HLs)is)hPs)gBLM(s)n$#$s%WS>&s%Xs)e'S>##%##'#j###N$s%.S<&s%/s)k'S<##%#7HLs)vs)uS%s)tBLS3(s){$#$s$tS?&s$us)r'S?##%#XT$S6S0KS:VT%S6KVT&KS:VT'S0S:VT(KS:VT)KS:VT*KS:#$##&##(##*##,#j###NZT+S6KS+S)MRUSOQXSQJS@SFQXSRJS@SFQDJCS8UT,K7JQ&%$#BQF()$#.KS8-F+JCS8&$#(C&#:F(S.#S/$E'3s*{&)#/F0#$%#*-'(C#E'E0&1'$#s+U#%##'##*##0##2##5##;#j#BQ#,Q#DJCS(7JQs#%s#$#B(s#'#A.KS(+JCS(&A#(C%#$E%&&=$#;*(?(C#E##7#&##)##s#&##,##1#j#BQ#,Q#j###NDJCS57JQs#:s#9#s#7(s#<#s#6.KS5+JCS5&s#6#(C%#$E%&&s#2$#s#0*(s#4(C#E##s#,#&##)##s#;##,##1#j#BQ#U#FDJCS-7JQs#Ns#M#s#K(s#P#s#J.KS-+JCS-&s#J#(C%#$E%&&s#F$#s#D*(s#H(C#E##s#@#&##)##s#O##,##1#DJCS;7JQs#`s#_#s#]BQM(s#c$#-M+JCS;&$#(Cs%,#:M(S.#S/$E'&(s#[/M0#$%#*,s#_(C#E'E/&0'$#s,Q#%##'##*##/##1##4##9#j###N.KS9-S&+JCS9&$#(C&#:S&(S.#S/$E'&(s#t/S&0#$%#*,s#x(C#E'E/&0'$#s,j#%##'##*##/##1##4#DJCS>7JQs$7s$6#s$4BQS3(s$:$#.KS<-S*+JCS<&$#(C&#:S*(S.#S/$E'&(s$3/S*0#$%#*,s$7(C#E'E/&0'$#s-)#%##'##*##/##1##4#.KS^-P+JCS^&$#(C&#:P(S.#S/$E'&(s$J/P0#$%#*,s$N(C#E'E/&0'$#s-@#%##'##*##/##1##4#j###N:R(S.#S/+JCS?$E#&$s$^/R0#$%#*(s$b(C#E-R'E#&$($#s-U#%##(##+##0##3#.KSD-S%+JCSD&$#(C&#:O(S.#S/+JCSJ$E#&$s$v/O0#$%#*(s$z(C#E-O'E#&$($#s-m#%##(##+##0##3#:S#(S.#S/+JCS_$E#&$s%-/S#0#$%#*(s%1(C#E-S#'E#&$($#s.$#%##(##+##0##3#j###N+JCSE$E#&$s%?/S)0#$%#*(s%C(C#E-S)'E#&$($#s.6#%##(##+##0#:S2(S.#S/+JCT-$E#&$s%Q/S,0#$%#*(s%U(C#E-S,'E#&$($#s.H#%##(##+##0#+JCS]$E#&$s%a/S40#$%#*(s%e(C#E-S4'E#&$($#s.X#%##(##+##0#j###N+JCT.&#s%q/S+0#$%#*'s%u(C#E-S+'E#&$($#s.h#%##(##+#+JCT/$E#+JCT0&#s&%/S(0#$%#*'s&)(C#E-S('E#&$($#s.x#%##(##+#+JCSI&#s&3/S50#$%#*'s&7(C#E-S5'E#&$($#s/*#%##(##+#j###N+JCSK*#s&B(C#E-S-'E#/S-0#&&#$#s/7#'##*#+JCT1&#s&M/S;0#$%#+JCT2*#s&R(C#E-S9'E#/S90#&&#$#s/G#'##*#+JCT3*#s&](C#E-S>'E#/S>0#&&#$#s/R#'##*#j###N-S<'E#/S<0#&&#$#s/[#'#+JCT4*#s&p(C#E-S?'E#/S?0#&&#$#s/e#'#-SD'E#/SD0#&&#$#s/l#'#j###N-SJ/SJ0#&%#$#s/s-S_'E#-SE/SE0#&%#$#s/z+JCT5WT6#s'2S-$Es'3+JCT7*#s'5$E#k##&#>s-:>#<C#<C%?C#s-3?C%#VSX#SYWSZSB#s.J;CS%2Cs.JM#;CS#2Cs-6S3#2C%S##;CO2Cs.OS&#2C#S#s)G2C&S##9Cs*J9Cs/GCC$#5C#S1s,H6s.PIDDG#S')s.N9C#@Cs'PCC$#5C#S1*6s.VIDDG#S'CC-'5Cs)QT8#6s.YIDDG#S'=s.ZIDDGS2@Cs/1CCs)U#5Cs.[SC#6s.^IDDG#S'Es._IDDG'#=s.`IDDGS,1s.aIDDGs,Ls.Y#1s.bIDDGs,Os.Z#1s.cIDDGs,Ts.[#1s.dIDDGs.Zs.\#1s.eIDDG(s.]#1s.fIDDG/s.^#1s.gIDDG3s._#1s.hIDDG:s.`#l#(#s.[s.Ul#)As.k#l#*s#+s.r#j#+C#j#,C#j#5C#j#6C#j#7C#j#9C#j#CC#j#DC#j#EC#j#-S$#j#.S$#&RO$#F&Os'v$#S#&OS#(CS%#&Os/S'S%##S,#$RO$s0*OVS[OS#$S%#$S%Ok###S-k##%#k##(#k##*#k##,#k##0#k##3#k##6#k#+C#k#,C#k#5C#k#6C#k#7C#k#9C#k#CC#k#DC#k#EC#k#-S$#k#.S$#.KS`$#Sa/SK0#+JCS`-SKgFN'%$#(Sas0Fs0CS7s1-S%S(SET9T:T;SGSHl#/s#+*#l#Fs#ms#h#l#Gs/Qs/N#l#Hs/Ys/U#l#Is/^s/[#l#Js/is/c#l#Ks0ks0l#j#Ls#u#j#Ms#{#V#MFj##s$##j##s$/#8s$0s$,s$*#Fj#<s$3#j#Ns$;#V#MFj##s$@#j##s$Q#8s$Rs$Ks$I#Fj#<s$V#j#Os$b#V#MFj##s$i#j##s%##8s%$s$xs$v#Fj#<s%*#j#Ps%9#V#MFj##s%=#j##s%[#8s%\s%Os%M#Fj#<s%_#j#Qs%p#V#MFj##s%t#j##s&;#8s&<s&,s&*#Fj#<s&?#j#Rs&S#V#MFj##s&Z#j##s'%#8s'&s&qs&o#Fj#<s',#j#Ss'D#V#MFj##s'J#j##s'z#8s'{s'es'c#Fj#<s($#j#TQ#V#MFj##s(9#j#AQ#FQs(Qs(O#Fl#Us),s(e#j#=s)0#j#Vs):#V#MFj##s)3#j##s)=#8s)>s)5s)3#Fl#<S\s)@#j#?s)B#j#Ws)G#V#MFj##s)L#j##s)W#8s)Xs)Ts)R#Fj#<s)\#j#%L#V#MFj##s)e#j#AL#FLs)ss)q#Fj#<s){#j#XH#V#MFj##s*'#j#AH#FHs*3s*1#Fj#<s*;#U#Fj##s-0#Hs-9s-1s-/s*F#Fj#<s-@#U#Fj##s/G#Hs/Ws/Hs/Fs-R#Fj#<s/[#U#Fj##s0j#Hs1?s0ks0is/q#Fj#<s1C#UT<s1Dm#$#j#'s1G#l#Ys1js1k#l#Zs1Us1L#l#[s1Ws1X#l#\s1^s1_#l#]s1ns1o#j#^C##"). Qed.

(* [comment removed for export] *)
Lemma runk_agree_keep stE mE :
  s_shadow stE = s_shadow st ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
  (forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
  unk_agree stE o mE.
Proof. try hcb. try hsb.
  intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov st rid off).
  { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

(* [comment removed for export] *)
Lemma rta_fp_not_inband rid r off :
  (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
  ~ rta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof. try hcb. try hsb.
  intros Hr Hk Ho NG. pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC, CLO.
  intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
  - destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
  - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
    destruct (N.eq_dec (fst bq) rid) as [E|NE].
    + apply NG. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

Lemma rag_phase : forall st1 m1 (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  rmrep st1 m1 -> mem_inv rsegs m1 -> rw_cells rsegs m1 (bv_unsigned sp + -144) (rFRM junk) -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m1 ->
  rimplT o (as_grp full_lay f sc req k bail st1) s Q
    (MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
        F (Z_to_bv 64 0x691d8) fc None m1 (seg_rom rsegs)).
Proof. try hcb. try hsb.
  intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO'.
  pose proof rerrno_lit2 as EA.
  pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  rewrite (as_grp_eq f sc req k bail st1).
  riprefixT. unfold rag_regs.
  eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
  cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
  assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
  assert (BL1 : brk_link_ps st1 s).
  { unfold brk_link_ps in *. unfold ctx in *. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
    unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
  assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
  { apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling; lia]. eapply rauxv_ok_pres; [exact AUX| exact PE1| |].
    - intros a Ha. apply rta_fp_not_high. exact Ha.
    - intros a Ha. apply rta_fp_not_image; unfold RAUXV_CELL, RCTX in *; lia. }
  assert (ERR2 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| unfold RCTX; lia]. }
  eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
    [ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2
    | rewrite unsigned_lit by lia; exact ST1 | exact CLO
    | rewrite unsigned_lit by lia; unfold RAM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
  intros st2 mo s' ms' PO BL2 LF.
  destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL).
  rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
  replace (ret_pc (Z_to_bv 64 0x691f0)) with (Z_to_bv 64 0x691f0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof MR3 as (WF3 & _). pose proof WF3 as (RS3 & WR3 & DJ3 & _).
  (* [comment removed for export] *)
  assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0xb4000 /\ ~ (RCTX <= a < RCTX + 928) /\ ~ (0x925ac <= a < 0x925b0)) ->
            ~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
  { intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
    - lia.
    - rewrite unsigned_lit in X by lia. lia.
    - unfold RCTX in *. lia.
    - destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in BC.
      pose proof (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
    - destruct X as [XC XF]. hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in XC.
      pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). pose proof (rfresh_below st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). lia. }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk)).
  { eapply rpres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }
  (* [comment removed for export] *)
  assert (REL02 : mrel st st2).
  { split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
    intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. auto. }
  assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
  { intros q (ar & arr & kk & Ha & Hk & E). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
    exists ar, arr', kk. auto. }
  assert (PE03 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
  { eapply rpres_except_trans.
    - eapply rpres_except_mono; [exact PE1|]. intros a Ha. eapply (rta_fp_malloc_fp st2 m3); [exact MR3| exact REL02| exact AREAS2| exact Ha].
    - eapply rpres_except_mono; [exact PE3|]. intros a [[X|[X|[X|X]]]|X].
      + left. left. lia. + left. right. left. exact X. + left. right. right. left. exact X. + left. right. right. right. exact X.
      + do 4 right. eapply (fresh_addr_anti st0 st1); [| | exact X].
        * rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
        * intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L'). exists r'. rewrite REG1. auto. }
  (* [comment removed for export] *)
  assert (UA3 : unk_agree st2 o m3).
  { eapply (runk_agree_keep st2 m3).
    - rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
    - intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
      + destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      + exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
    - intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
    - intros rid r off h Hr Hk Ho Hc NG.
      destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in RC.
      transitivity (m1 (wa (r_base r + off))).
      + refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
        * lia.
        * rewrite unsigned_lit in X by lia. destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2).
          specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
        * destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
        * assert (Hr2 : (s_regions st2) !! rid = Some r).
          { rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G'). rewrite H'. f_equal. apply G'. exact Hk. }
          assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
          pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
        * rewrite <- REG1 in Hr. pose proof (fresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
      + refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (rta_fp_not_inband rid r off Hr Hk Ho NG). }
  destruct mo as [mm|].
  - (* [comment removed for export] *)
    destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
    pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _).
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in GC; lia| exact MI3]. }
    cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done.
    eapply (HAG st1 st2 mm m3 s'); try eassumption.
    + eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
    + eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
    + eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
    + eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
  - (* [comment removed for export] *)
    cbn iota.
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := 0); [lia| exact MI3]. }
    cbv beta. intros ms' ->. cbn [Z.eqb].
    eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [exact MR3| exact MI3| exact FR3| exact ST3| exact CLO| lia]. }
    cbv beta. intros ms' (a1x & a2x & -> & ST4). apply evt_done.
    apply HK. unfold ras_post2.
    do 14 eexists. exists m3, errv3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST4|]. split; [exact ERR3|].
    split. { eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia]. }
    split; [exact MR3|]. split; [exact TK3|]. split; [exact UA3|]. split; [exact PE03|].
    split; [exact REL02|]. split; [exact BL2|]. split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split. { rewrite (amr_counter _ _ _ REL). unfold ctx. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
             pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
    left. reflexivity.
Qed.
End LEVEL.

End HCW.

