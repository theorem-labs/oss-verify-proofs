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
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 ASlot_W9 F_ntf_C.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RASlot_W2 RASlot_W4 RASlot_W3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RBand.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ RCTX <= a < RCTX + 928
  \/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof. try hcb. try hsb. intros; left; assumption. Qed.
Lemma rta_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rta_fp st lo sp a. Proof. try hcb. try hsb. intros; right; left; assumption. Qed.
Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof. try hcb. try hsb. intros; do 2 right; left. exists q; auto. Qed.
Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof. try hcb. try hsb. intros; do 3 right. exists b, gh; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
(* [comment removed for export] *)
Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : hceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
  rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
Hypothesis HK1 : forall stX g3 msk k m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv usegs m' -> stk usegs m' lo spv ->
  rpres_except (rta_fp st lo spv) m m' ->
  rimplT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom usegs)).

Lemma rfin_block : forall stX g3 msk mZ (t0 t1 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 ->
  rmrep stX mZ -> mem_inv usegs mZ -> rw_cells usegs mZ (spv + -144) (FRM junk) -> stk usegs mZ lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mZ ->
  rimplT o (ta_fin stX g3 msk K) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) (wz (sxv msk)) a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x6d4c4) fc None mZ (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until junk. intros TR HA GM HM MR0 MRZ MIZ FRZ STZ PEZ.
  destruct (gmf_geom st stX sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds st m g3) as GB0.
  pose proof (rmeta_slot_bounds stX mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
  destruct (lowbit_facts msk ltac:(lia)) as (k & Hk & LB).
  unfold ta_fin. riprefixT. unfold RR, rt1_regs.
  eapply evt_mono.
  { eapply (rfin_walk stX mZ g3 msk lo MRZ MSZ ltac:(lia) CLO); [| exact FRZ| exact STZ| unfold spv; lia| exact MIZ].
    rewrite unsigned_lit by lia. symmetry; exact ECONC. }
  cbv beta. intros ms' (a1' & a2' & a3' & m' & k' & Hk' & LB' & -> & MU & WM & MI' & ST' & MR').
  assert (k' = k) by (rewrite LB in LB'; apply Z.pow_inj_r in LB'; lia). subst k'.
  eapply (HK1 stX g3 msk k m'); try eassumption; try lia.
  eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
  cbn [ivs_covered]. split; [|split; [|exact I]].
  - intros x Hx. apply rta_fp_stack. unfold spv in *; lia.
  - intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Logic.False Sort Prop.

Lemma ravz_block : forall (pc : Z) stZ g3 mZ (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  (pc = 0x6d440 \/ pc = 0x6d44c) ->
  ta_rel sc st stZ -> active stZ sc = Some g3 -> gmf st sc g3 ->
  rmrep stZ mZ -> mem_inv usegs mZ -> rw_cells usegs mZ (spv + -144) (FRM junk) -> stk usegs mZ lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mZ ->
  rimplT o (ta_avz K bail stZ g3) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 pc) fc None mZ (seg_rom usegs)).
Proof. ltac2:(KReplay.runc [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil_range); constr:(HCEIL); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret_range); constr:(HSEC); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hsecret); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapSecret.hcanary); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.mstate); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.aptr); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.list); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W0.ta_rel); constr:(sc); constr:(st); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.optr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.active); constr:(@Corelib.Init.Datatypes.Some); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.gmf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.rmrep); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.mem_inv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.USegs.usegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(spv); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(FRM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.stk); constr:(lo); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocTree.rpres_except); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RASlot_W9.HCW.rta_fp); constr:(m); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.gmf_geom); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocRep.meta_slot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_avail); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.get_meta_rec); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_freed); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocFacts_AS.mw_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_mem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_last_idx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_sizeclass); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_freeable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.conc); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocTree.rimplT); constr:(R); constr:(o); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W1.ta_avz); constr:(K); constr:(bail); constr:(s); constr:(Q); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.MS); constr:(RR); constr:(@stdpp.bitvector.definitions.Z_to_bv); constr:(F); constr:(fc); constr:(@Corelib.Init.Datatypes.None); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.PropExec.seg_rom); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocKit_B.rmeta_slot_bounds); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.ge); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.gmf_grp); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ghdr); constr:(@stdpp.base.lookup); constr:(@stdpp.gmap.gmap); constr:(@stdpp.decidable.prod_eq_dec); constr:(@Corelib.Numbers.BinNums.N); constr:(@stdpp.numbers.N.eq_dec); constr:(@stdpp.numbers.Z.eq_dec); constr:(@stdpp.countable.prod_countable); constr:(@stdpp.countable.N_countable); constr:(@stdpp.countable.Z_countable); constr:(@stdpp.gmap.gmap_lookup); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.s_groups); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.g_meta); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.g_active_idx); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.cellval); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.cell_read); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.get_shadow); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.Unknown); constr:(@kc__2); constr:(@Corelib.Init.Logic.proj2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W0.tr_groups); constr:(@Corelib.Init.Logic.ex_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W0.tr_gmeta); constr:(@Corelib.Init.Logic.not); constr:(@Corelib.Init.Logic.eq_ind); constr:(@Corelib.Init.Logic.f_equal); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.gmf_mw); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_maplen); constr:(@kc__3); constr:(@Corelib.Init.Logic.eq_refl); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(sp); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@kc__4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.guard); constr:(@Corelib.Init.Datatypes.negb); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.mask_upto); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.group_active_idx); constr:(@stdpp.option.from_option); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.id); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Numbers.BinNums.N0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ta_fin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.decay_bounces); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.upd_meta); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.meta); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_set_avail); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.m_set_freed); constr:(@Stdlib.ZArith.BinInt.Z.ldiff); constr:(@Stdlib.ZArith.BinInt.Z.eqb_eq); constr:(@Stdlib.ZArith.BinInt.Z.mod_small); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.ZArith.BinInt.Z.ones); constr:(@Stdlib.ZArith.BinInt.Z.land_ones); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocTree.rimplT_undef); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.UAssert); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.M); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.STree.SVis); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.EUndef); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.eqb_neq); constr:(@Corelib.Init.Logic.eq_sym); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.MState.unsigned_lit); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocTree.rimplT_evt); constr:(@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RASlot_W4.rt1_regs); constr:(ra); constr:(gp); constr:(tp); constr:(t2); constr:(s1); constr:(a1); constr:(s3); constr:(s8); constr:(s9); constr:(s10); constr:(s11); constr:(t3); constr:(t4); constr:(t5); constr:(t6); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt_mono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocRep.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RASlot_W3.ravz_pre_walk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Exec.evt_done); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocTree.rimplT_from_evt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.F_malloc_free.sxv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocRep.RCTX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RASlot_W3.ravz_walk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.taf_bnc); constr:(TAF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.bounces); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W0.tr_bounces); constr:(SC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W0.ta_rel_trans); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.put_meta); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W0.ta_rel_put_meta); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Datatypes.orb); constr:(@Stdlib.ZArith.BinInt.Z.testbit); constr:(@Stdlib.Bool.Bool.orb_prop); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.land_spec); constr:(@Corelib.Init.Datatypes.andb_prop); constr:(@Stdlib.ZArith.BinInt.Z.ldiff_spec); constr:(@Stdlib.ZArith.BinInt.Z.bits_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocKit_B3.land_upper); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocKit_B3.ldiff_le); constr:(@Stdlib.ZArith.BinInt.Z.ldiff_nonneg); constr:(@Corelib.Init.Logic.iff); constr:(@Stdlib.micromega.Tauto.IFF); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocKit_B.upd_meta_put); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W0.ta_rel_decay); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RBand.rdisjoint_high); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.Lists.List.In); constr:(@kc__5); constr:(LO); constr:(CLO); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.stk_transport_disjoint); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RASlot_W9.HCW.PHASE.rfin_block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.active_upd_meta); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.active_decay); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.F_malloc_enframe.get_meta_rec_upd_same); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.rec_decay); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocTree.rpres_except_trans); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMallocKit_B.rpres_except_of_munch_cov); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RASlot_W9.HCW.rta_fp_meta); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.ASlot_W9.gmf_slot); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RASlot_W9.HCW.rta_fp_ctx); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Agent.MallocKit_B.ivs_covered); constr:(@kc__2 ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))))); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.aptr)); constr:(@kc__2 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Malloc.ghdr))|] [|@h; @o; @gh; @b; @gh1; @g; @e; @AI1; @GM1; @Hgh'; @gh'; @Ha; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__p1; @__arith; @__sat12; @__sat13; @__sat14; @__sat15; @heq_spv; @H; @H0; @x; @a; @r; @AV0; @m; @n; @z; @__sat16; @__sat17; @MZ; @c; @y; @heq_act; @heq_f; @a1x; @ms'; @pc; @ms0; @m'; @a7'; @a6'; @a5'; @a4'; @a3'; @a2'; @B0; @i; @_H; @Hb; @Hi; @__x4; @H1; @Hf; @p; @E; @lo'; @hi'; @HCEILB0; @H2; @Hx; @ST5; @FR5; @TR5; @TR4; @st5; @st4; @MR5; @MI5; @WM; @MU; @m5; @HG; @EMb; @b0; @f; @act; @AI1R; @_H1; @_H0; @LI0; @Hgh1; @UNK; @SC0; @AIR; @GMg; @Hgh; @Hmem; @GI; @GC; @Gpos; @ECONC; @EFB; @ESC; @ELI; @EM; @MWZ; @RFZ; @RAZ; @MSZ; @PEZ; @STZ; @FRZ; @MIZ; @MRZ; @GM; @HA; @TR; @PC; @junk; @a7; @a6; @a5; @a4; @a3; @a2; @a1'; @t1; @t0; @mZ; @g3; @stZ; @HCANB; @HSECB; @HCEILB|] "#e9%_(O%s##'0%~%m#$&A'1'/%c#%&T&K&L%u&#%}'P&B&F&G#&'f&D'=#'&)#(%l'9&E&X'h'i'j'k'l'm'n'o'p'q'r's't'u'v#+#)'>#*#,#/'7$`#0#8#1#.#-$_$a$^#9&`&n$Z$X$Y&p$b&6&e&d&f&c&b$[#3#=#d$\$]#2#7#<#e#f'A$c#4#A%_#;#@#H#P#b#c'8$W'V$e#5#:#E#L#M#g&x'6$V'D%@&9#?#D#I#Q&Q#a&{$d$t$s$w${%#&(#>#C#K#N#T#j&}'C(($u$v$x$|%$%,%p&0#G#O#S#h#m&r$q$r$y$z$}$~%'%*&h%x#B#J#U#X#\#`#k#u$T$U'G$f$p%%%&%/%3%=#R#W#n#w$P&w&|'%$S'`$i%(%)%+%A#F#Y#]#i#l#s#v#y$,$E$O$Q'H%-#6#Z#_#o#q#r#t#z$@$?&o$G$F&~&s'd$o$k%.%0%1%7(9%B&$&,#V#[#^&_#p#{#|#~$#$'$0$6$A$>$=$D$H$L$M$N&y'#$R$j%<%>(.(/%?(G%{%i%|#x#}$$$%$($)$-$+$/&m$5$7$9$;$8$<$B$C$I$K':$h%2%4%5%t%w$.$1$3$4$:$J'+'I$g(#%6%8%:%G%H%I%O&5$&&k$2'3'W$n%9%;(@%F%C%J%N%P%v%y&-&.&*&/&2&3&M&Y&Z$*&u'$'&'('['Z'w'x(&('()$l(2(4(8(7(<(+%D%E%K%L%M%W%Q(J(D(O&S'B%b%j%k%n%q%r&&&1&4&N&O&R&W&[&\&]&V&^&g&j&i&l&q&v'''*','.';'?'@'<'J'L'T'U'X'Y'\'_']'^'a'b'c'z'{$m(%(*(,(1(3(5(6(:(;(>(=(?(-(A(B(F(E%V%](H(I(C%X%R%^(K(M(N(P(T(S(U(V(W(R(Q(L'|'e%d%e&7&>%g&<&J&+'E&a&H%o'S&8&;'R'Q%h'O&@'N'K'F&=&:'5'4&%&z&I'g&t&''-%z&C&?')($%f'y(0'}&P'M'~'2&UU'{%%t&'|%'}%'~%(#$($$&~%(%%(&%('%(($()*(*%(+%(,$(-$(.%(/%(0$(1&(2*(3%(4'(5$(6$(7$(8'(9*(:%(;&(<-(=>(>%(?'(@+(A%(B((C((D'(E&(F$(G$(H%(I$(J%(K((L&(M*(N)UVpL6Ue6#6#6#6#6#6#6#6#6#6#6#6#6#(#6#6#6#6#6#6#6#6#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#L#UVqL%$#6s#&6#6#6#6#6#6#6#6#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#L#%s#%##s#%#m#s#W#UVrS/UVsS/%G#(UeL#($(#(#(#(#L#VTG)#0-##-#m#0#UVtS/UVuS/%G#0$)#$#m#'#UV%.UVF#UV%3UVF#UTX#k##&#UVG%(s#s6#6#(#6#(#6#(#6#6#6#6#(#(#6#(#(#L#6Ue(#6#6#(#6#(#6#(#(#(#6#(#(#(#(#(#(#L#6(6#(#(#L#(Ue(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#L#636#6#(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#L#6s#56#(#(#(#6#(#(#L#(=6#6#(#6#6#(#(#(#6#6#6#6#(#(#(#L#$CSJs#F6s#`(#(#(#(#L#$CSJs#HG*#WUfS#FSJVUDSLS#@QSJ$R$#WVvFS#SLELS/SaSLVT7S-Sf6s$5(#(#(#(#UVH#,UE#UVISCXVJS-Sa$#XVKS-SmTH%WVLFTHUEWVw#VMSzZVxFSKS#SgSES.VV7SKSg&SKSgUSZ#%G#Ls$CVTGs$H#0&##&#2)%G#0$'#$#UT)-=.&FSg=#$R%#323&$C$#)5))$C$#<8<,$C$#'SKSg'FSg$C$##&##*##.##2##7##9##>##s#&#VV7SRSK&SRSKUSZ#%G#0$s#&#$#2'%G#0$s#*#$#UT)+=,&FSK=#$R%#303&$C$#)3))$C$#<6<,$C$#'SRSK'FSK$C$##&##*##.##2##7##9##>##s#$#HIS*S1S{SR'FSR+s$|#BSgU,#SzSmSaSfSLSJSG+s$~SpUVNs$~UVyS-/&O%P$SK#8LIS%*S&S'#j##,#&S{SRUSZ#%G#0$s#R#$#2'%G#0$s#V#$#UT)+=,&FSR=#$R%#303&$C$#)3))$C$#<6<,$C$#'S{SR$C#s###%##)##-##1##6##8##=#VV7SpS{&ShSpUSZ#%G#0$s#s#$#2'%G#0$s#w#$#UT)+=,&FSp=#$R%#303&$C$#)3))$C$#<6<,$C$#'ShSp'FSp$C$##&##*##.##2##7##9##>#&SbShUSZ#%G#0$s$8#$#2'%G#0$s$<#$#UT)+=,&FSh=#$R%#303&$C$#)3))$C$#<6<,$C$#'SbSh'FSh$C$##&##*##.##2##7##9##>#HIS*S1T8Sb'FSb+s&1#BSpS{#SRSKSgU,SzSmSa+s&3T*/$O#Ps#oShs#n8LIS%(S&S'#j##*#&T8Sb2#%G#0$s$a#$#UT)'=(&FSb=#$R%#3,3&$C$#)/))$C$#<2<,$C$#'T8Sb$C#=#%##)##-##1##6##8#&T*T8USZ#%G#0$s$|#$#&SqT*2#%G#0$s%%#$#UT)'=(&FT*=#$R%#3,3&$C$#)/))$C$#<2<,$C$#'SqT*'FT*$C$##&##*##.##2##7##9#&SnSq2#%G#0$s%A#$#UT)'=(&FSq=#$R%#3,3&$C$#)/))$C$#<2<,$C$#'SnSq'FSq$C$##&##*##.##2##7##9#HIS*S1TYSn'FSn+s'5#BT*T8#SbShSpS{SRSKSg+s'7T9/$O#Ps$sSqs$r8LIS%(S&S'#j##*#&TYSnUT)#=$&FSn=#$R%#3(3&$C$#)+))$C$#<.<,$C$#'TYSn$C#9#%##)##-##1##6#&T9TY2#%G#0$s%{#$#&T+T9UT)#=$&FT9=#$R%#3(3&$C$#)+))$C$#<.<,$C$#'T+T9'FT9$C$##&##*##.##2##7#&S|T+UT)#=$&FT+=#$R%#3(3&$C$#)+))$C$#<.<,$C$#'S|T+'FT+$C$##&##*##.##2##7#HIS*S1TzS|'FS|+s(*#BT9TY#SnSqT*T8SbShSp+s(,TI/$O#Ps%hT+s%g8LIS%(S&S'#j##*#&TzS|=#&FS|=#$R%#3'3&$C$#)*))$C$#<-<,$C$#'TzS|$C#8#%##)##-##1#&TITzUT)#&SrTI=#&FTI=#$R%#3'3&$C$#)*))$C$#<-<,$C$#'SrTI'FTI$C$##&##*##.##2#&T,Sr=#&FSr=#$R%#3'3&$C$#)*))$C$#<-<,$C$#'T,Sr'FSr$C$##&##*##.##2#HIS*S1TZT,'FT,+s(r#BTITz#S|T+T9TYSnSqT*+s(tT:/$O#Ps&TSrs&S8LIS%(S&S'#j##*#&TZT,3#&FT,3#$C%#)')&$C$#<*<)$C$#'TZT,$C#5#%##)##-#&T:TZ=#&FTZ=#$R%#&S}T:3#&FT:3#$C%#)')&$C$#<*<)$C$#'S}T:'FT:$C$##&##*##.#&S~S}3#&FS}3#$C%#)')&$C$#<*<)$C$#'S~S}'FS}$C$##&##*##.#HIS*S1T;S~'FS~+s)U#BT:TZ#T,SrTITzS|T+T9+s)WTJ/$O#Ps'7S}s'68LIS%(S&S'#j##*#&T;S~)#&FS~)#$C%#<'<&$C$#'T;S~$C#2#%##)#&TJT;3#&FT;3#$C%#&SsTJ)#&FTJ)#$C%#<'<&$C$#'SsTJ'FTJ$C$##&##*#&T-Ss)#&FSs)#$C%#<'<&$C$#'T-Ss'FSs$C$##&##*#HIS*S1TkT-'FT-+s*,#BTJT;#S~S}T:TZT,SrTI+s*.TK/$O#Ps'jSss'i8LIS%(S&S'#j##*#&TkT-<#&FT-<#$C%#'TkT-$C#/#%#&TKTk)#&FTk)#$C%#&T<TK<#&FTK<#$C%#'T<TK'FTK$C$##&#&T[T<<#&FT<<#$C%#'T[T<'FT<$C$##&#HIS*S1UFT['FT[+s*S#BTKTk#T-SsTJT;S~S}T:+s*UTl/$O#Ps(5T<s(48LIS%(S&S'#j##*#'UFT[$C#*&TlUF<#&FUF<#$C%#'T\Tl'FTl$C$#[VzLS/T{TlT\SrSq'T{T\0G#6s*x(#(#(#L#,)#%#s+K(s*y(#(#(#(#(#(#(#(#(#L#%/s*76s)V(#(#(#(#(#(#(#(#(#(#(#(#(#(#(#L#%s*6s#(G5#Ls+@Ps#+#$C#GL?Ps#.#(s+.(#L#VT.&##)##-##s#-##s#5#'U-T{0G#,$s#3%#s+{%$s*\%s*J'G$#P)6$C#GP+5VT.#2#%##(##,##/#HIS*S1UGU-'FU-+s+N#BT\Tl#UFT[T<TKTkT-Ss+s+PT]/$O#Ps)0T{s)/8LIS%(S&S'#j##*#'UGU-,#s#I%#s,5%$s*r%s*`&G$#P(s#,$C#GP*s#+VT.#s#(#%##(##,#'T]UG0G#'T|T],#s#X%#s,D%$s+%%s*o&G$#P(s#;$C#GP*s#:VT.#s#7#%##(##,#'UHT|,#s#e%#s,Q%$s+2%s*|&G$#P(s#H$C#GP*s#GVT.#s#D#%##(##,#HIS*S1U.UH'FUH+s,##BT]UG#U-T{T\TlUFT[T<+s,%T^/$O#Ps)aT|s)`8LIS%(S&S'#j##*#'U.UH,#s#z%#s+F%s+4%G$#P's#\$C#GP)s#[VT.#s#X#%##(#'T^U.,#s$)%#s,q'T/T^,#s$,%#s+T%s+B%G$#P's#j$C#GP)s#iVT.#s#f#%##(#'StT/,#s$7%#s+_%s+M%G$#P's#u$C#GP)s#tVT.#s#q#%##(#HIS*S1SuSt'FSt+s,O#BT^U.#UHT|T]UGU-T{T\+s,QSc/$O#Ps*1T/s*08LIS%(S&S'#j##*#'SuStP#s$($C#GP%s$'VT.#s$$#%#'ScSu,#s$P%#s+x%s+f%G$#'SiScP#s$3$C#GP%s$2VT.#s$/#%#'SjSiP#s$9$C#GP%s$8VT.#s$5#%#HIS*S1T#Sj'FSj+s,n#BScSu#StT/T^U.UHT|T]+s,pTL/$O#Ps*PSis*O8LIS%(S&S'#j##*#'T#SjP#s$DVT.#s$A'TLT#P#s$J$C#G'T}TLP#s$JVT.#s$GXV{FS#T}U-&FT_=#@QH$R$#UTXNXV|S2VOCVPZV}S2VOV~CVPW#XW$Q$#NXW%Q%$NUUIFTQN%$H#@ND$*$#USSD@QT_$R$#.D%G#34%%##%#)7$C#G.H&FT~3#$C%#k##'#%GDLs+x0D##%#WS[S2CS,VS\F#WS]S2CS,,#MVS^%#UW&D$S_$#j#$C#*C#k##,#k#%C##2##:##@##s#$##s#.#j#&N#*N#j#'Q#*Q#=>$R#s#5@QT~$Rs#,#%s#*A#s#*#)s#$$C#G&FTM3#$Cs#)#k##&###8#*##-##s#9##1#j#&N#*N#j#'Q#*Q#HIS*S1T~T_'FT_+s-m#BT}TL#T#SjSiScSuStT/+s-oTM/$O#Ps+OT=s+N8LIS%(S&S'#j##*#=7$R#s#R@QTM$Rs#I#%s#G:#s#G#)=$C#G&FTm3#$Cs#F#k##&###s#5#*##-##s#V##1#j#&N#*N#j#'Q#U#D=/$R#s#g@QTm$Rs#^#%s#\2#s#\#)5$C#G&FU/3#$Cs#[#k##&###s#J#*##-##s#k##1#j#&N#*N#=-@QM$R$#TQNs#ws#vMs#u$s#{#s#t@QU/$Rs#t#%s#r3#s#r#)6$C#G&FUJ3#$Cs#q#k##&#WS[S2CS.VS\F#WS]S2CS.,#MVS^%#$S_#s#jj#$C#*C#k##s#s#k#%C##-##4##7##:##=#j#&N#*N#HIS*S1UJU/'FU/+s.a#BTMT~#T_T=T}TLT#SjSi+s.cU0/$O#Ps,CTms,B8LIS%(S&S'#j##*#=?@QS($R$#TQNs$Cs$BS(s$A$s$G#s$@@QUJ$Rs$@#%s$>s#%#s$>#)s#($C#G&FU03#$Cs$=#k##&#WS[S2CSCVS\F#WS]S2CSC,#MVS^%#$S_#s$6j#$C#*C#k##s$?#k#%C##-##4##7##:##=#j#&N#U#D=7@QS,$R$#TQNs$cs$bS,s$a$s$g#s$`@QU0$Rs$`#%s$^=#s$^#)@$C#G&FU13#$Cs$]#k##&#WS[S2CSEVS\F#WS]S2CSE,#MVS^%#$S_#s$Vj#$C#*C#k##s$_#k#%C##-##4##7##:##=#=5@QS.$R$#TQNs%%s%$S.s%#@NH$s%*$#USSH@QU1$R$#%Gs$w%s$x>#$#)A$C#G.M&FU#3#$C%#k##'#WS[S2CSBVS\F#WS]S2CSB,#MVS^%#$S_#s$xj#$C#*C#k##s%%#k#%C##-##5##9##=##A#HIS*S1U2U#'FU#+s/m#BU0UJ#U/TmTMT~T_T=T}+s/oT`/$O#Ps-OU1s-N8LIS%(S&S'#j##*#TQNs%Ls%KSCs%J@NM$s%Q$#USSM@QU#$R$#%Gs#$%s#%s###$#)s#&$C#G.S(&FU23#$C%#k##'#WS[S2CSFVS\F#WS]S2CSF,#MVS^%#$S_#s%Cj#$C#*C#k##s%L#k#%C##-##5##9##=#=4@QSE$R$#TQNs%ms%lSBs%k@NS,$s%r$#USSS,@QT`$R$#.S,%G#&FT`3#%&##&#)&$C#G.S.&FU$3#$C%#k##'#WS[S2CSMVS\F#WS]S2CSM,#MVS^%#$S_#s%gj#$C#*C#k##s%p#k#%C##-##5##<##@#TQNs&2s&1SFs&0@NS.$s&7$#USSS.@QU$$R$#%G;%<:#$#)=$C#G.SC&FTn3#$C%#k##'#WS[S2CSGVS\F#WS]S2CSG,#MVS^%#$S_#s&)j#$C#*C#k##s&2#k#%C##-##5##9##=#HIS*S1UgTn'FTn+s0y#BT`U2#U#U1U0UJU/TmTM+s0{U%/$O#Ps.[U$s.Z8LIS%(S&S'#j##*#USSSC@QTn$R$#%G@%A?#$#)B$C#G.SE&FUg3#$C%#k##'#WS[S2CSJVS\F#WS]S2CSJ,#MVS^%#$S_#s&Lj#$C#*C#k##s&U#k#%C##-##5##9#TQNs&rs&qSMs&p@NSE$s&w$#USSSB@QU%$R$#.SB%G#&FU%3#%&##&#)&$C#G.SF&FU33#$C%#k##'#WS[S2CSfVS\F#WS]S2CSf,#MVS^%#$S_#s&lj#$C#*C#k##s&u#k#%C##-##5##<#USSSF@QU3$R$#%G7%86#$#)9$C#G.SN&FUK3#$C%#k##'#WS[S2CSaVS\F#WS]S2CSa,#MVS^%#$S_#s'*j#$C#*C#k##s'3#k#%C##-##5##9#HIS*S1ULUK'FUK+s1y#BU%Ug#TnU$T`U2U#U1U0+s1{Uh/$O#Ps/[U3s/Z8LIS%(S&S'#j##*#%G<%=;#$#)>$C#G.SM&FUL3#$C%#k##'#WS[S2CSmVS\F#WS]S2CSm,#MVS^%#$S_#s'Ij#$C#*C#k##s'R#k#%C##-##5#USSSM@QUL$R$#.SG%G#&FUh3#%&##&#)&$C#G.SJ&FUM3#$C%#k##'#WS[S2CU,VS\F#WS]S2CU,,#MVS^%#$S_#s'ej#$C#*C#k##s'n#k#%C##-##5#%G3%42#$#)5$C#G.SL&FUN3#$C%#k##'#WS[S2CSgVS\F#WS]S2CSg,#MVS^%#$S_#s'{j#$C#*C#k##s((#k#%C##-##5#HIS*S1UiUN'FUN+s2m#BUhUL#UKU3U%UgTnU$T`+s2oUj/$O#Ps0OUMs0N8LIS%(S&S'#j##*#):$C#G.Sf&FUi3#$C%#k##'#WS[S2CSKVS\F#WS]S2CSK,#MVS^%#$S_#s(:j#$C#*C#k##s(C#k#%C##-#%G2%31#$#&FUj)#$C#G.Sm&FV83#$C%#k##'#WS[S2CS{VS\F#WS]S2CS{,#MVS^%#$S_#s(Pj#$C#*C#k##s(Y#k#%C##-#)1$C#G.Sz&FUO3#$C%#k##'#WS[S2CSpVS\F#WS]S2CSp,#MVS^%#$S_#s(bj#$C#*C#k##s(k#k#%C##-#HIS*S1UkUO'FUO+s3S#BUjUi#UNUMUhULUKU3U%+s3UUl/$O#Ps15V8s148LIS%(S&S'#j##*#WS[S2CShVS\F#WS]S2CSh,#MVS^%#$S_#s(uj#$C#*C#k##s(~#k#%C#&FUk)#$C#G.Sg&FUl3#$C%#k##'#WS[S2CT8VS\F#WS]S2CT8,#MVS^%#$S_#s)+j#$C#*C#k##s)4#k#%C#UUIU&TQNs)Os)NSb#$s)S#s)Lj#(N#*N#TQNs)Ss)RT8s)Q$s)W#s)Pj#&N#*N#k##'#TQNs)Xs)WSbs)V$s)\#s)Uj#&N#*N#UUIUmTQNs)]s)\T8#$s)a#s)Zj#(N#*N#k##(#YW'S#FUnU%ShXV9N+SKSJXW(/%$#HIS*S1UmU&'FU&+s42#BVQUl#UkUOV8UjUiUNUM+s44V&/$O#Ps1pUns1o8LIS%(S&S'#j##.#UUIV&TQNs)ns)mT*#$s)r#s)kj#(N#U#DUUIUoTQNs)ss)rSq#$s)w#s)p[W)S#FUPUMSnHDTQNs)vs)uTYs)t$s)z#s)s$Rs'+s)r$Cs'Ks)pLs5P%s'M##s',#@QD$Rs'X#&FH)#$C#GUUp#k##'#k#)Q##+#G/##1##3#j#&N#*N#TQNs*/s*.T9s*-$s*3#s*,USSS($R#s*,$Cs':s**%Gs';%s'<9#$###1G'##)##,#j#&N#*N#HIS*S1V:V''FV'+s4f#BUoV&#UmU&UnVQUlUkUO+s4hV(/$O#Ps2HUPs2G8LIS%(S&S'#j##*#TQNs*Es*DT+s*C$s*I#s*B$Rs'5s*A$Cs'3s*?%s'4s#-#s'4###s#%G&##(##*#j#&N#U#DTQNs*Qs*PS|s*O$s*U#s*N$Rs&|s*M$Cs'7s*K%s'8s#9#s&|###s#1G&##(##*#TQNs*[s*ZTzs*Y$s*_#s(8$Rs&cs(7$Cs'#s*N%s'$s#C#s&c#$Rs'ps#Bk###s#>k#)Q##&#G)##+##-#HIS*S1UQUq'FUq+s55#BV(V:#V'UPUoV&UmU&Un+s57Ur/$O#Ps2sV)s2r8LIS%(S&S'#j##*#USSSE$R#s($$Cs&ps(D%Gs&q%s&rs#X#$#$Rs#Gs#Wk###s#Sk#)Q##&#G*##,#TQNs*|s*{Srs*z@NS($s+%$#$Rs&Ks'm$Cs&^s'k%s&_s#e#s&K#$Rs'Ps#dk###s#`k#)Q##&#G)##+#USSSN$R#s'W$Cs&Os'n%s&Ps#p#s&7#$Rs'8s#ok###s#kk#)Q##&#G)##+#HIS*S1V*Us'FUs+s5a#BUrUQ#UqV)V(V:V'UPUo+s5cUt/$O#Ps3CUus3B8LIS%(S&S'#j##*#$Cs&As'a%Gs&B%s&Cs$&#$#$Rs#2s$%k###s#}k#)Q##&#G*#USSSG$R#s#8$Cs&0s'1%s&1s$0#s%}#$Rs&vs$/k###s$+k#)Q##&#G)#TQNs+Ss+RT;s+Q@NSN$s+XD#j#%s+Y#@NTZZSTs+['$S.#TY@NSF$s+]%#@NT:@NSG$s+`H#HIS*S1URU4'FU4+s6+#BUSUT#UvUtV*UsUuUrUQ+s6-Uw/$O#Ps3iU5s3h8LIS%(S&S'#k##*#$s+i-4@NS}@NSM$s+l$#nTX$N$#%ND#%$#)D#T;j#*s+n#@NS~ZU6s+pN$#3D$NS~SG$NT;SJ$NTJSLHIS*S1UUUx'FUx+s6>#BURU4#U5USUTUvUtV*Us+s6@U'/$O#Ps3|Uws3{8LIS%(S&S'#j#)N#@NT-$s+}#s+vUSSSR$R#s)V.S{$C#s)P%G$%%s$d#$###s#hG'#HIS*S1U7U8'FU8+s6Q#BUUUx#UwURU4U5USUTUv+s6SUV/$O#Ps43U's428LIS%(S&S'#k#+*#k#,2#k#-5#j#.N#@NSs$s,7##USSSKUSST-$R$#.SR.Tk$C$#%G%%&s$|#$#USSTK$R#s$|k###s$xk#)Q##'#G+#XW*FS#U'UQ&FU'UT)#&FU83#%G#%$s%.#$#<'%G#LUe%%##%#),%G#Ls8(%%##%#UTN1%G#(s6w(#L#VTGs77#0(##(##+##1##7#HIS*S1UVU7'FU7+s7.#BU'UU#UxUwURU4U5USUT+s70Uy/$O#Ps4lU8s4k8LIS%(S&S'#j##*#&FU7<#%G#%$@#$#)'%G#%$?#$#UTN+%G#0$;#$##'##,#&FUV3#%G#%$s%_#$#&FUy<#%G#%$s#4#$#)'%G#%$s#3#$#UTN+%G#0$s#/#$##'##,#&FV+<#%G#%$s#C#$#)'%G#%$s#B#$#UTN+%G#0$s#>#$##'##,#HIS*S1UWUz'FUz+s7h#BUyUV#U7U8U'UUUxUwUR+s7jUX/$O#Ps5JV+s5I8LIS%(S&S'#j##*#&FUz)#%G#%$s#U#$#UTN'%G#0$s#Q#$##'#&FUW<#%G#%$s#d#$#&FUX)#%G#%$s#d#$#UTN'%G#0$s#`#$##'#&FUY)#%G#%$s#n#$#UTN'%G#0$s#j#$##'#HIS*S1ToU('FU(+s87#BUXUW#UzV+UyUVU7U8U'+s89U)/$O#Ps5uUYs5t8LIS%(S&S'#j##*#&FU(UTN#%G#0$s#x#$#&FTo)#%G#%$s$)#$#&FU)UTN#%G#0$s$&#$#.TI.T^$C$#%G%%&s&i#$#USST/$R#s&ik###s&ek#)Q##'#G+#.Sr%G#%$s&s#$#j##'#.T/$C(#VVRs8_W+DC#$CUE$m#$#VTps8ts7/0Gs8u%Gs710Gs71k##$#k##&#%Gs8zWUZs8{s76Hj##T$#j#/%#%Gs78k##T$#k#/(#VTps9%s8{%Gs8|0Gs8|k##$#k##2#WUZs9*s9$Hj##T$#j#/0#%Gs9&k##T$#k#/3#UU[VSUU[#UU[#UU[#VU9C#VU9C%VU9C(VU9CVSWT>C$#WT>C&#WT>C(#VTq#TrUVHUeVW,C#WVTC#+VU9C0WT>C#+WT>C%#VTq#TrUVUT0AT0$#AT0,#UVGT0UW-CVV,CS(JC#S($JC#S(%JC&S(#VV,CMJC#S((JC)S(#JC&H#UW.CUW/CZV;#KEEJS.6s1:VT%C#VSvCs']>C$SH#?(KEEJ#S0S)KEEJ(#UVNEVT%CUeVT%Cs8&>C$U{#?.KEEJ#S0VSvCG>C#SH&?1KEEJ#S0>C(SH/?3KEEJ#S0S4KEEJ%#>C(SH,?6KEEJ#S0>C.SH3?8KEEJ#S0S9KEEJ%#F:KEEJ(2#F;KEEJ/3#F<KEEJ54#VW0=JDS+SDVW1DM$S+#SDm$%#WW2CGHXW3DM$#l#0*)#l#1s#'s#&#l#2s#2s#1#j#3C#j#4C#j#5C#j#6So#%Hs(&#S(#$CHS(%GS,%S,S(#$#%GS(%S(s(-#$#k##&#k##*#k##,#k#3C#k#4C#k#5C#k#6So#&FSU3#%G#.TL.TJ[D%$&#SmSCT\l#79)#l#8s#gs#d#l#9s#os#k#l#:s#ts#q#l#;s#~s#y#l#<s$$s$%#j#=s$)#U#Dj##s$;#USSSt$R#s(Ck###s(?k#)Q##s$3#.T,%G#%$s(L#$#USSSu$R#s(Lk###s(Hk#)Q##'#.TZ%G#%$s(U#$#j##'#USSSc$R#s(Vk###s(Rk#)Q#.T:%G#%$s(^#$#USSSj$R#s(^k###s(Zk#)Q#VV,CHFs#jKEEJs#Ss#bs#Sl#0#s#Ps#Jl#1%s#m#l#2s#{s#x#j#3C#%Ds(j#s/r#%GH##s#Ik##%#k#3C#.TKVD#SEl#7+%#l#8s$As$>#l#9s$Is$E#l#:s$Ns$K#l#;s$Xs$S#l#<s$Zs$[#j#>7#j#=<#V#HDj##B#j##s#1#Is#2s#.s#(#Dj#=s#7#U#Dj##s$o#ZU:s$xs$ps$js#?#SJ&TaTsUSZ#VSk#GDS+D&TbTaUSZ#VSk#G$S+#D&SwT&USZ#VSk#G$S+#DLs<'&SVSw2#=$VV-S2CUW4#:S2CW5s$R&SWSV=#YU*''&%#VTcSW#;#nTX$Q$#?C+#%$#@##G--#VSk#GUT'#2+&SUSW=#YU*110/#VTcSU#;#nTX$Q$#?C0#%$#@##G-)#1*$4#D5%#j#AS$#7Sw#SV&#Sw)#9#%QI#Sw5S*YT?Is3.4#S1YT?Is#$H#S1'FSw+s;=#BTbTa#TsU\U)ToU(UYUX+s;?SW/$O#Ps8{T&s8z8LIS%(S&S'#k#Bs#,#j#'S+#&T&TbUSZ#VSk#G$S+#SDVSkHD$S+#SD$CMHk##$#$CHDVSkMH$S+#SDk##%##'#$CS(Mk##&#j##%#VSkS(M$S+#SDk##.#j###Hj##/#VW6HDI1-)$#j#CC#j#DC#k#CC4k#DC#USZs#GWD#GH$C$G&FSV=#2s#<YU*s#Js#Js#Is#HHVTcS`#;#nTX$Q$#?CD#%$#@##G-'#VSk#GUT'#&S`SU2#YU*s#Ss#Ss#Rs#QMVTcSd#;#nTX$Q$#?CH#%$#@##G-'#1($4#D5%#j#AS$#7SW#SU&#SW)#9#%QI#SW4S*YT?Is3p3#S1'FSW+s;~#BSwT&#TbTaTsU\U)ToU(+s<$S`/$O#Ps9`SVs9_8LIS%(S&S'#j#%R#@QT=.T;-s1Vs*CnTX$N$#?CD#%$#$##G$C%#j#%s1e#.S~Ls4'VTGs<A#P%#$C+Dj#EC#DC(VTps<F(%G)0G)k##$#k##s&3#WUZs<K-Hj##T$#j#/s&1#%G/k##T$#k#/s&4#VSvCs<QUV%s49WV<C$#>Cs%XSx#?s%bKEEJ#S0Ss%cKEEJs%O#Fs%dKEEJs%Ms%\#l#0#s%Js%Dl#1s$[s%g#l#2s%us%r#j#3C#0H=#s$W#k##s$Y#k#3C#.T[VD#SJl#7)%#l#8s&9s&6#l#9s&As&=#l#::7#l#;B>#l#Fs&Hs&E#l#Gs&Rs&M#l#<s&Ts&U#WW7s#-s#+#ZSXCs#.s#)s#(s#+#UW8s#.-s#0#VSvCs#0>Cs%oSH#?s%}KEEJ#S0l#0#s%cs%]l#1s&-s&$#l#2s&2s&/#l#7#s#/Dl#8s&Ks&H#l#9s&Ss&O#l#:s&Xs&U#l#;s&bs&]#l#<s&ds&e#WW9s#=s#<#ZSXCs#;s#920#UUISWTQNs2Es2DT=#ZSXs2Is)8s#B%#S}VTcSWT=$Cs#C#m#%#;D-s#c#VSk#GUT'#&SdS`2#;H-$#1%$4#D5%#j#AS$#7SU#S`&#SU)#9#%QI#SU1S*YT?Is4v0#S1'FSU+s=(#BSVSw#T&TbTaTsU\U)To+s=*Sd/$O#Ps:fSWs:e8LIS%(S&S'#j#EC#;s#c-DHVSk#G-HMVSk#G$S+#D-S(S,VSk#G$S+#DUT'H-S.SC1S.SC4#D5%#j#AS$#7SO#SI&#SO)#9#%-S,S.QI$SO#S*YT?Is57.#S1'FSO+s=E#BSeSd#S`SUSWSVSwT&Tb+s=GSP/$O#Ps;'SQs;&8LIS%(S&S'#k#H6#j#'S+#-MS(VSk#G$S+#SDUVVs5Cj##CS1'FSQ+s=R#BSdS`#SUSWSVSwT&TbTa+s=TSI/$O#Ps;4Ses;3]VWLS/IS%)(S&S'#UW:IUT'SD1S,S.4#D5<#j#AS$#7SQ#SO&#SQ)#9#%QI#SQs#/S*UW;5YW<W=CI#5nS+#$#I/.#%#%##8LIS%#S&S'2m#2#YT?Is5[1(S18LIS%#S&S'5m#%#j#H>#$S+@Tt$S+s%&TtUUps%%k##$#UUps%%$S+s%%Ttk##$##&#UUps%$k##&#j##%#$S+s%$Ttk##,#j###Hj##-#VW>HDI/,($#j#JC#j#?C#k#JC2k#?C#WDs#AGH$Cs#BGUUp#&SPSI4s#M#5s#O#)D-SESB1SESB4#D5%#j#AS$#7SP#SY9)#-SCSEQI$SP#S*'FSP+s>5#BSOSQ#SeSdS`SUSWSVSw+s>7Sl/$O#Ps;sSIs;r8LIS%(S&S'#j#CS$#&FSI=#$RDs1$j#%R#=:ZSXR&$T=#Uu$R$s1O'SlSY$CD#j#EC#'SYSPXW?C#4U&VVRs>G4&SYSP2#DC#$CSC$m#$#.Tl;#DC#$CSB$m#$#WT>Cs(0s(%VTq#TrWVTCs(*s((WT>C#s(0WT>Cs(5#VTq#TrAT0#s((AT0(#JCs(#S(s(&JC#Hs'~VT%Cs>jVSvCs6QWU;C$#VT%Cs?m>C$SH#?s(#KEEJ#S0>Cs'sSx(?s(%KEEJ#S0>C*U{s'y?s('KEEJ#S0VSvCs?#>C*SH#?s(*KEEJ#S0Ss(+KEEJs(*#WV<Cs%,s>j>Cs($Sx#?s(.KEEJ#S0Ss(/KEEJs'w#Fs(0KEEJ's((#Fs(1KEEJ,s()#Fs(2KEEJ/s(*#Fs(3KEEJ2s(+#l#0#s'us'ol#1:s(6#l#2=s(A#j#3C#j#4C#j#5C#j#6So#,Ms6m%#H0GS($CS,M%S,s?:#SC#0S,s?-#s'r#k##%#k##(#k##*#k##,#k#3C#k#4C#k#5C#k#6So#'U]Tu'FTu\Ds?i$s?j#U&UPV)V=l#76&#l#8s(ts(q#l#9s(|s(x#l#:s)%s(~#l#;s)/s)*#l#<s)1s)2#l#Ks#Cs#D#l#Ls#Is#J#VW@s#b#ZSXCs#cs#Ss#Qs#P#$Cs#Qs#S&SlSY)#-SBSF1SBSF4#D5%#j#AS$#7SY#Sl9)#QI#SYs#wS*+s?Es=x'FT1+s?G#CS#S3%S4S5SYSPS6S7#DSOSQSeSdS`SUS8S9S:S;S<S=S>S?S@SA+s?Is>u/$O#Ps=)Sls=($S)H#j#Ms?K#*s?L#j#NS)#'FSY+s?P#CS#S3.S4S5SISOS6S7#SQSeSdS`SUSWSVS8S9S:S;S<S=S>S?S@SA+s?RT1/$O#Ps=2SPs=1$CT1s?)$CT1s?%G$#'FSy+s?X#CS#S36S4S5SlSYS6S7#DSISOSQSeSdS`S8S9S:S;S<S=S>S?S@SA/#O3Ps=9T1s=8$S)H#j#Ms?[#*s?\#j#NS)#'FSl+s?`#CS#S3>S4S5SPSIS6S7#SOSQSeSdS`SUSWS8S9S:S;S<S=S>S?S@SA+s?bSy/$O#Ps=BSYs=AWVXS-(#j##1#$CSys?;'FV.+s?h#CS#S3s#&S4S5SyT1S6S7#DSYSPSISOSQSeS8S9S:S;S<S=S>S?S@SA/#Os##Ps=ITds=H$S)H#j#Ms?k#*s?l#j#NS)#CS#S3s#,S4S5SlSYS6S79SPSISOSQSeSdS`S8S9S:S;S<S=S>S?S@SA+s?pD/$O#Ps=PT1s=OWVXS-&#j#OC#MGCS#S3s#2S4S5SlSYS6S7?#SISOSQSeSdS`S8S9S:S;S<S=S>S?S@SA/#Os#/Ps=UT1s=T$S)D#j#NS)#'FTd+s?z#CS#S3s#8S4S5T1SlS6S7#DSPSISOSQSeSdS8S9S:S;S<S=S>S?S@SA/#Os#5Ps=[Sys=Z$S)H#j#Ms?}#*s?~#j#NS)#CS#S3s#>S4S5SYSPS6S7s#<SISOSQSeSdS`SUS8S9S:S;S<S=S>S?S@SA+s@&s?W/$O#Ps=bSls=ai#JWALS/SySlT1S#TaUWSGS3s#AS4S5SYSPS6S7SISOSQSeSdS`SUS8S9S:S;S<S=S>S?S@SAs#?OPMTsCS#S3s#BS4S5T1SlS6S7-3SPSISOSQSeSdS8S9S:S;S<S=S>S?S@SA/#Os#?Ps=eSys=d'FU|+s@,#CS#S3s#FS4S5TdSyS6S7#DSlSYSPSISOSQS8S9S:S;S<S=S>S?S@SA/#Os#CPs=iV.s=h$S)H#j#Ms@/#*s@0#j#NS)#CS#S3s#LS4S5SyT1S6S7s#)=SYSPSISOSQSeS8S9S:S;S<S=S>S?S@SA/#Os#IPs=oTds=n$S)#s#)j#Ms@5#DS)/XV9s@7$B#ZSXS)1)#HDj#=A#j#NS)#$S)D4j#NS)#U#D$S)Ms#3j#Ms@?#*s@@#k##&#k#NS)#m#+#ZVYS-s#+s##@?#ZSXCs?ws#1#TdDj#=s#?#U#Dj##s#S#$CSys?v/s#(Os#`Ps>*Sls>)/s#;Os#aPs>+T1s>*$S)#s#Qj#Ms@M#DS)&XV9s@O$SI#XWBS-s#/(#ZSXCs?~s#=#TdDj#=+#U#Dj##s#^#ZU:s#`s#_s#O/#T&$S)Ms#[j#Ms@W#*s@X#&TdSy)#-SMSG1SMSG4#D5%#j#AS$#7Sy#Td9)#-SNSMQI$Sy#S*8LIS%#S&S'Mj##/#$S)S(s#Ij#Ms@g#U#D$S)S,s#^CS#S3s$(S4S5TdSyS6S7s#AHSlSYSPSISOSQS8S9S:S;S<S=S>S?S@SA/#Os$%Ps>KV.s>J&U]Tu)#-SfSa1SfSa4#D5%#j#AS$#7Tu#U]9)#-SLSfQI$Tu#S*8LIS%#S&S'Dj#PS)#&TuU|)#1SLSf4#D5*#j#AS$#7U|#Tu9(#-SJSLQI$U|#S*'FTe+sA)#&TOTe2#.Si;#-%#O#M#CS#S3s$JS4S5V=WCS6S7*#SCS.S,S(MHS8S9S:S;S<S=S>S?S@SA6sA%(#(#6#6#(#6#(#(#(#L#+sA=s@<//O#Ps>yDs>x$S)SE#VV-CC'TOTe,#s96:CC$#6sA;(#(#(#(#L#,V/#(sBX(#6#(#(#(#(#L#,V/#:CC,#UVU7A8$#A96#R#U<DKS-U<DVT7S-D)s#3&TPTO2#.Sj;#-%#1&$4#D5%#j#AS$#7Te#TO9-#ELS/#D#0##2##4##s#.#j#QsAg#*sAh#j#RsAm#*sAn#j#SsAo#*sAp#j#TsAq#*sAr#j#UsAs#*sAt#j#VsAu#*sAv#j#WsAw#*sAx#j#NS)#j#NS)s#aXVZFS#V[DVT@FD%G#Ls9o0%##%#&U=U]2#DC#$CSf$m#$#;s,<DC#$CSm$m#$#ZV;s+MKEEJS(Ss+NKEEJs+:#Fs+OKEEJ#s+Gs+;l#0#s+5s+/l#1s*Fs+R#l#2s+`s+]#j#3C#j#6So##s7WHk###s*Ck#3C#k#6So#VT@FSF0#;WD#$SBl#7*&#l#8s,&s,##l#9s,.s,*#l#:s,3s,0#l#;s,=s,8#l#<s,?s,@#l#K89#l#L=>#ZV\S#FU=SeH#VT@U=H%G#VT@FH%%##%#&V]U=2#DC#$CSa$m#$#;s,RDC#$CSz$m#$#WT>Cs,)s,0VTq#TrAT0#s,'JCs+{Ms,$JCs,%M#JC#Ms,&JCs,'H#6s:SVT%C#>Cs+sSH#?s+}KEEJ#S0Ss+~KEEJs+j#ZV;s,#KEEJS,VSvCs#A>C(Sx#?s,&KEEJ#S0Ss,'KEEJ&#>Cs+{Sx&?s,)KEEJ#S0Ss,*KEEJs+r#Fs,+KEEJ&s,##Fs,,KEEJ,s,$#l#0#s+ns+hl#13s,/#l#28s,:#j#3C#j#4C#j#6So#%DH#s86#0Ms#R#S(#%GM##%k##%#k##(#k#3C#k#4C#k#6So#VT@FSN%G#VT@T2SNYD$%#SBSFl#72'#l#8s,hs,e#l#9s,ps,l#l#:s,us,r#l#;s-#s,z#l#<s-%s-&#l#Ks#4s#5#l#Ls#9s#:#l#=s#Ds#?#l#Xs#ks#f#j#YC#i#TWDLS/TuV.U|U3T|S#SVToSaSET]SKUVUUSB#WES3s&HS4S5TdSyS6S7HSlSYSPSISOSQS8S9S:S;S<S=S>S?S@SAs%aOPSCSw'FTO+sC1#Os$0M#CS#S3s&MS4S5U<V=S6S7%#SCS.S,S(MHS8S9S:S;S<S=S>S?S@SA/#Os$VPs@pDs@o$S)SB#'TPTO,#s;,:CC$#As$X#s$BR#TeDKS-TeD)s$?&T3TP2#.T#;#-%#1&$4#D5%#j#AS$#7TO#TP9-#ELS/#D#s$N##1##3##9#j#QsCI#*sCJ#j#RsCO#*sCP#j#SsCQ#*sCR#j#TsCS#*sCT#j#UsCU#*sCV#j#VsCW#*sCX#j#WsCY#*sCZ#)s#n-SmSz1SmSz4#D5%#j#AS$#7U=#V]9)#-SaSmQI$U=#S*8LIS%#S&S'Mj##.#'FTP+sCi#Os#*M#CS#S3s')S4S5TeU<S6S7%#SCS.S,S(MHS8S9S:S;S<S=S>S?S@SA/#Os%2PsALDsAK$S)SF#'T3TP,#s;d:CC$#As%4#s$zR#TODKS-TOD)s#9&T2T32#;s,Z-$#1%$4#D5%#j#AS$#7TP#T39,#ELS/#D#s%)##0##2##8#j#QsD$#*sD%#j#RsD*#*sD+#j#SsD,#*sD-#j#TsD.#*sD/#j#UsD0#*sD1#j#VsD2#*sD3#j#WsD4#U#D'FT3+sD8#O>M#CS#S3s'TS4S5TOTeS6S7%#SCS.S,S(MHS8S9S:S;S<S=S>S?S@SA/#Os%]PsAwDsAv$S)SN#'T2T3,#s<3:CC$#As%_#s%IR#TPDKS-TPD)s#,&TAT22#.T};#-%#1&$4#D5%#j#AS$#7T3#T29-#ELS/#D#s%U##1##3##9#j#QsDP#*sDQ#j#RsDV#*sDW#j#SsDX#*sDY#j#TsDZ#*sD[#j#UsD\#*sD]#j#VsD^#*sD_#'FT2+sDb#O<M#CS#S3s'~S4S5TPTOS6S7%#SES.S,S(MHS8S9S:S;S<S=S>S?S@SA/#Os&+PsBEDsBD$S)SM#'TAT2,#s<]:CC$#As&-#s%sR#T3DKS-T3D)s#+&TBTA2#.T=;#-%#1&$4#D5%#j#AS$#7T2#TA9-#ELS/#D#s&###1##3##9#j#QsDz#*sD{#j#RsE$#*sE%#j#SsE&#*sE'#j#TsE(#*sE)#j#UsE*#*sE+#j#VsE,#*sE-#&TeU<)#-SKSR1SKSR4#D5%#j#AS$#7U<#Te9)#-SgSKQI$U<#S*8LIS%#S&S'SCj##/#'FTA+sE=#Os#)M#CS#S3s(YS4S5T3TPS6S7%#SBS.S,S(MHS8S9S:S;S<S=S>S?S@SA/#Os&bPsB|DsB{$S)SG#'TBTA,#s=8:CC$#As&d#s&NR#T2DKS-T2D)s#8&T4TB2#.T_;#-%#1&$4#D5%#j#AS$#7TA#TB9-#ELS/#D#s&Z##1##3##9#j#QsEU#*sEV#j#RsE[#*sE\#j#SsE]#*sE^#j#TsE_#*sE`#j#UsEa#*sEb#j#VsEc#U#D'FTB+sEg#O<M#CS#S3s)'S4S5T2T3S6S7%#SFS.S,S(MHS8S9S:S;S<S=S>S?S@SA/#Os'0PsCJDsCI$S)SJ#'T4TB,#s=b:CC$#As'2#s&xR#TADKS-TAD)s#+&TCT42#.T~;#-%#1&$4#D5%#j#AS$#7TB#T49-#ELS/#D#s'(##1##3##9#j#QsF##*sF$#j#RsF)#*sF*#j#SsF+#*sF,#j#TsF-#*sF.#j#UsF/#*sF0#'FT4+sF3#O:M#CS#S3s)OS4S5TAT2S6S7%#SNSCS,S(MHS8S9S:S;S<S=S>S?S@SA/#Os'XPsCrDsCq$S)SL#'TCT4,#s>.:CC$#As'Z#s'DR#TBDKS-TBD)s#)&TQTC2#.TM;#-%#1&$4#D5%#j#AS$#7T4#TC9-#ELS/#D#s'P##1##3##9#j#QsFK#*sFL#j#RsFQ#*sFR#j#SsFS#*sFT#j#TsFU#*sFV#j#UsFW#*sFX#-ShSb1ShSb4#D5%#j#AS$#7T3#T29s$z#-SpShQI$T3#S*8LIS%#S&S'SNj##-#'FTC+sFf#Os#%M#CS#S3s*&S4S5TBTAS6S7%#SMSES,S(MHS8S9S:S;S<S=S>S?S@SA/#Os(/PsDIDsDH$S)Sf#'TQTC,#s>a:CC$#As(1#s'wR#T4DKS-T4D)s#4&TRTQ2#.Tm;#-%#1&$4#D5%#j#AS$#7TC#TQ9-#ELS/#D#s('##1##3##9#j#QsF~#*sG##j#RsG(#*sG)#j#SsG*#*sG+#j#TsG,#*sG-#j#UsG.#U#D'FTQ+sG2#O:M#CS#S3s*NS4S5T4TBS6S7%#SGSBS,S(MHS8S9S:S;S<S=S>S?S@SA/#Os(WPsDqDsDp$S)Sa#'TRTQ,#s?-:CC$#As(Y#s(CR#TCDKS-TCD)s#)&T5TR2#.U/;#-%#1&$4#D5%#j#AS$#7TQ#TR9-#ELS/#D#s(O##1##3##9#j#QsGJ#*sGK#j#RsGP#*sGQ#j#SsGR#*sGS#j#TsGT#*sGU#'FTR+sGX#O8M#CS#S3s*tS4S5TCT4S6S7%#SJSFS.S(MHS8S9S:S;S<S=S>S?S@SA/#Os(}PsE;DsE:$S)Sm#'T5TR,#s?S:CC$#As)##s(iR#TQDKS-TQD)s#'&TDT52#.UJ;#-%#1&$4#D5%#j#AS$#7TR#T59-#ELS/#D#s(u##1##3##9#j#QsGp#*sGq#j#RsGv#*sGw#j#SsGx#*sGy#j#TsGz#*sG{#-SqSn1SqSn4#D5%#j#AS$#7T4#TC9s$F#-T*SqQI$T4#S*8LIS%#S&S'SLj##-#'FT5+sH-#Os##M#CS#S3s+IS4S5TQTCS6S7%#SLSNSCS(MHS8S9S:S;S<S=S>S?S@SA/#Os)RPsElDsEk$S)Sz#'TDT5,#s@(:CC$#As)T#s)>R#TRDKS-TRD)s#2&TSTD2#.U0;#-%#1&$4#D5%#j#AS$#7T5#TD9-#ELS/#D#s)J##1##3##9#j#QsHE#*sHF#j#RsHK#*sHL#j#SsHM#*sHN#j#TsHO#U#D'FTD+sHS#O8M#CS#S3s+oS4S5TRTQS6S7%#SfSMSES(MHS8S9S:S;S<S=S>S?S@SA/#Os)xPsF6DsF5$S)U,#'TSTD,#s@N:CC$#As)z#s)dR#T5DKS-T5D)s#'&TTTS2#.U1;#-%#1&$4#D5%#j#AS$#7TD#TS9-#ELS/#D#s)p##1##3##9#j#QsHk#*sHl#j#RsHq#*sHr#j#SsHs#*sHt#'FTS+sHw#O6M#CS#S3s,7S4S5T5TRS6S7%#SaSGSBS,MHS8S9S:S;S<S=S>S?S@SA/#Os*@PsFZDsFY$S)Sg#'TTTS,#s@r:CC$#As*B#s*,R#TDDKS-TDD)s#%&T6TT2#.U#;#-%#1&$4#D5%#j#AS$#7TS#TT9-#ELS/#D#s*8##1##3##9#j#QsI3#*sI4#j#RsI9#*sI:#j#SsI;#*sI<#-T+S|1T+S|4#D5%#j#AS$#7T5#TD9s#i#-T9T+QI$T5#S*8LIS%#S&S'Szj##-#'FTT+sIJ#OAM#CS#S3s,fS4S5TDT5S6S7%#SmSJSFS.MHS8S9S:S;S<S=S>S?S@SA/#Os*oPsG-DsG,$S)SK#'T6TT,#sAE:CC$#As*q#s*[R#TSDKS-TSD)s#0&TET62#.U2;#-%#1&$4#D5%#j#AS$#7TT#T69-#ELS/#D#s*g##1##3##9#j#QsIb#*sIc#j#RsIh#*sIi#j#SsIj#U#D'FT6+sIn#O6M#CS#S3s-.S4S5TSTDS6S7%#SzSLSNSCMHS8S9S:S;S<S=S>S?S@SA/#Os+7PsGQDsGP$S)SR#'TET6,#sAi:CC$#As+9#s+#R#TTDKS-TTD)s#%&TfTE2#.T`;#-%#1&$4#D5%#j#AS$#7T6#TE9-#ELS/#D#s+/##1##3##9#j#QsJ*#*sJ+#j#RsJ0#*sJ1#'FTE+sJ4#O4M#CS#S3s-PS4S5TTTSS6S7%#U,SfSMSES(HS8S9S:S;S<S=S>S?S@SA/#Os+YPsGsDsGr$S)S{#'TfTE,#sB/:CC$#As+[#s+ER#T6DKS-T6D)s##&TgTf2#.U$;#-%#1&$4#D5%#j#AS$#7TE#Tf9-#ELS/#D#s+Q##1##3##9#j#QsJL#*sJM#j#RsJR#*sJS#-SrT,1SrT,4#D5%#j#AS$#7T6#TE9s#?#-TISrQI$T6#S*8LIS%#S&S'SRj##-#'FTf+sJa#O?M#CS#S3s-}S4S5T6TTS6S7%#SgSaSGSBS,HS8S9S:S;S<S=S>S?S@SA/#Os,*PsHDDsHC$S)Sp#'TgTf,#sB\:CC$#As,,#s+rR#TEDKS-TED)s#.&TUTg2#.Tn;#-%#1&$4#D5%#j#AS$#7Tf#Tg9-#ELS/#D#s+~##1##3##9#j#QsJy#*sJz#j#RsK##U#D'FTg+sK'#O4M#CS#S3s.CS4S5TET6S6S7%#SKSmSJSFS.HS8S9S:S;S<S=S>S?S@SA/#Os,LPsHfDsHe$S)Sh#'TUTg,#sB~:CC$#As,N#s,8R#TfDKS-TfD)s##&TvTU2#.Ug;#-%#1&$4#D5%#j#AS$#7Tg#TU9-#ELS/#D#s,D##1##3##9#j#QsK?#*sK@#'FTU+sKG#O2M#CS#S3s.cS4S5TfTES6S7%#SRSzSLSNSCMS8S9S:S;S<S=S>S?S@SA/#Os,lPsI*DsI)$S)Sb#'TvTU,#sCB:CC$#As,n#s,XR#TgDKS-TgD)A&TwTv2#.U%;#-%#1&$4#D5%#j#AS$#7TU#Tv9-#ELS/#D#s,d##1##3##9#j#QsK_#-S}S~1S}S~4#D5%#j#AS$#7TU#Tv9:#-T:S}QI$TU#S*8LIS%#S&S'Sb'FTw+sKp#&TVTw2#.U3;#-%#O#M#CS#S3s/5S4S5TUTgS6S7*#SpSgSaSGSBS,S8S9S:S;S<S=S>S?S@SA/#Os->PsIXDsIW$S)T*#'TVTw,#sCp:CC$#As-@#s-*R#TvDKS-TvD)2&TxTV2#.UK;#-%#1&$4#D5%#j#AS$#7Tw#TV9-#ELS/#D#s-6##1##3##9#'FTV+sL7#O0M#CS#S3s/SS4S5TvTUS6S7%#ShSKSmSJSFS.S8S9S:S;S<S=S>S?S@SA/#Os-\PsIvHsIu$S)Sq#'TxTV,#sD2:CC$#As-^#s-HR#TwHKS-TwHVT7S-H)@&TFTx2#.UL;#-%#1&$4#D5%#j#AS$#7TV#Tx9-#ELS/#H#0##2##4##:#)2-SsT-1SsT-4#D5%#j#AS$#7Tx#TF9)#-TJSsQI$Tx#S*8LIS%#S&S'Snj##.#'TFTx,#sDV:CC$#As.&#s-lR#TVMKS-TVMVT7S-M&U+TF2#.Uh;#-%#1&$4#D5%#j#AS$#7Tx#TF9?#ELS/#M#/##1##3#'FTF+sLx#O/M#CS#S3s08S4S5TVTwS6S7%#T8S{U,SfSMSES8S9S:S;S<S=S>S?S@SA/#Os.APsJ[S(sJZ$S)TY#'FU++sM##&U>U+2#.UM;#-%#O#M#CS#S3s0DS4S5TxTVS6S7*#T*SpSgSaSGSBS8S9S:S;S<S=S>S?S@SA/#Os.MPsJgS,sJf'ThU>,#sD~:CC$#As.N#s.8R#U+S.KS-U+S.VT7S-S.&ThU>)#&U?Th2#.Ui;#-%#1&$4#D5%#j#AS$#7U>#Th9-#ELS/#S.#1##3##5#)1-T<T[1T<T[4#D5%#j#AS$#7Th#U?9)#-TKT<QI$Th#S*8LIS%#S&S'Hk##.#j#NS)#'U>U+,#sEG:CC$#As.s#s.]R#TFS,KS-TFS,VT7S-S,)s#72s#(.UN;#-%#1&$4#D5%#j#AS$#7U+#U>9,#ELS/#S,#/##1##3#'FTh+sMi#Os#2M#CS#S3s1)S4S5U+TFS6S7%#SnSbSRSzSLSNS8S9S:S;S<S=S>S?S@SA/#Os/2PsKLSCsKK8LIS%BS&S'#j##s#-#KS-U>SCVT7S-SC&U@U?2#.Uj;#-%#1&$4#D5%#j#AS$#7Th#U?9s#9#ELS/#SC#/##1#'U@U?,#sEu:CC$#As/E#s//R#ThSEKS-U?SBVT7S-SB&U}U@)#&TiU}2#.UO;#-%#1&$4#D5%#j#AS$#7U@#U}9-#ELS/#SB#1##3#KS-U@SFVT7S-SF)2&U~Ti2#.Uk;#-%#1&$4#D5%#j#AS$#7U}#Ti9-#ELS/#SF#0##2#)0-T\T{1T\T{4#D5%#j#AS$#7Ti#U~9)#-TlT\QI$Ti#S*'FTi+sNW#O8M#CS#S3s1sS4S5U@U?S6S7%#S|SnSbSRSzSLS8S9S:S;S<S=S>S?S@SA/#Os/|PsL:SNsL98LIS%)S&S'#j##4#VT7S-SN&V#U~2#.Ul;#-%#1&$4#D5%#j#AS$#7Ti#U~9?#ELS/#SN#/#KS-TiSMVT7S-SG&V0V#)#&UAV02#.Un;#-%#1&$4#D5%#j#AS$#7V##V09-#ELS/#SG#1#VT7S-SJ)0&V1UA2#.U&;#-%#1&$4#D5%#j#AS$#7V0#UA9-#ELS/#SJ#0#)/-T]T|1T]T|4#D5%#j#AS$#7UA#V19)#-UGT]QI$UA#S*'FUA+sO;#O7M#CS#S3s2WS4S5V#U~S6S7%#T,S|SnSbSRSzS8S9S:S;S<S=S>S?S@SA/#Os0`PsLzSLsLy8LIS%)S&S'#j##4#&V>V12#.Um;#-%#1&$4#D5%#j#AS$#7UA#V19>#ELS/#SL&V2V>)#&V?V22#.Uo;#-%#1&$4#D5%#j#AS$#7V>#V29-#ELS/#Sa-U.T^1U.T^4#D5%#j#AS$#7V2#V?&U^V?)#9#D-T^T/1T^T/&TjU^4$#5&#WWFU^#TjWUfS#U_Dj#CV$#=&=)$R$#3)3,$C$#<,</$C$#)/)2$C$#UTN2UTN5$C$##&##*##.#DR3DC1DC/DC-DC+XU`.+$#XU`2+&#XU`6+(#XU`:+*#-StSuN#H1StSuN#HVUa%#$S+#SD-SuScN#M1SuScN#MWWG%#D$S+&SD$S+%SDG$#NDS,NSiS,VUa$#$S+#SDj#EC#VUaD&$S+#SDj#'S+#-ScSiN#S($S+#SD1ScSiN#S($S+#SDG&#$S+0SDj##$#-SiSjN#S,$S+#SD-SjT#N#S.$S+DSDj#'S+#NSjS.NT#S.VV^$#WWHSjT#S.ZSTS+)'D$#$S+%SDNT#SCNTLSCWV_$#D$S+%SD$S+%SD#$#NTLSE$S+#SDNT}SE$S+#SD#%#NT}SB$S+#SDj##%#NT=SB$S+#SDNT=SF$S+#SDNT~SN$S+#SDj#Z#Hj#[&#V#HDj##*#j##3#I42.#Dl#[:7#l#[?>#j#[s#)#U#Dj##s#4#1SiSjN#S,$S+#SD1SjT#N#S.UT's#+VV^s#-#WWISjT#S.ZSTS+&s#0D$#$S+%SDUT's#*WV_s#,#D$S+$SD#s#+#UT's#'$S+#SD#s#*#j###s#&UT's#%$S+#SDUT's##$S+#SDj#Z#Hj#[s#'#V#HDj##(#j##s#4#Is#5.,#Dl#[31#l#[76#j#[>#U#Dj##s#R#ZU:s#Vs#Ss#Ps#$#DNScS(VUaTt#$S+#SDm#&#NGS(UWJS(ZSXS+Tts#`%$#&TyT(USZ#ZSXCGs#f%#T#l#[s#os#l#&T(UbUSZ#N#M2%N#MVUa%#$S+#SDm#*#j#[s#}#j#\sFq#j#YC#&UbU_4s$(#5s$+#USZ#N#H2%N#HVUa%#$S+#SDk###0k##sF}#k#YC#m#/#USZs$W%G#0$sP-#$#%GT/0T/sP0#$#26DC#$CSt$m#$#.V);#DC#$CSc$m#$#0T=sP;WD#T=SBl#7s2>s2:#l#8s;Zs;W#l#9s;bs;^#l#:s;gs;d#l#;s;qs;l#l#<s;ss;t#l#K+,#l#L12#.V(,#s=dVTpsR1#,4s=f%G#.Uq,#s=iVTGsR6#0G#k##'#k##s;~#DCs#<$CSus#=m#$#;+DC#$CSi$m#$#.Ut,#s=vVTpsRC#.Uv,#s=y%G#.UT,#s=|VTGsRI#0G#k##'#k##s<5#.US,#s>&WUZsRO#Hj##T$#j#/s<5#VTGsRR&%G#k##T$#k#/s<9#JCs2KMs;mJCs;nM#JCs;oH#>Cs;YSxs8f?s;gKEEJ#S0VT%CsJ/VSvCs>4WU;C$#>Cs;^SH#?s;lKEEJ#S0>Cs;`Sxs;d?s;nKEEJ#S0Fs;oKEEJ%s;g#Fs;pKEEJ+s;h#>Cs;dSH+?s;rKEEJ#S0Ss;sKEEJ#s2RWV`Cs;k->Cs;hSH#?s;vKEEJ#S0Fs;wKEEJ&s;o#Fs;xKEEJ*s;p#l#0#s;^s;Xl#17s;{#l#2s<-s<*#j#3C#j#4C#j#6So#,Ms>J%G#0GMk##$#k##s<_##s2OS(VUBMs>P%G#k##%#k##'#k#3C#k#4C#k#6So#%s#4sA+YD#s#5s#0MT`l#72%#l#8s#3s#/#l#9s#Bs#9#l#:s<Zs<W#l#;s<bs<^#l#Fs<gs<d#l#Gs<qs<l#l#<s<ss<t#l#Ks#Ks#L#l#Ls#Ps#Q#l#=s#\s#T#%GSum#$#XVaStSus#b#%Gs%T%s%USt#$#0T_sQLWD#T_SFl#7s3Os3K#l#8s<ks<h#l#9s<ss<o#l#:s<xs<u#l#;s=&s<}#l#<s=(s=)#l#Ks#\s#]#l#Ls#as#b#VTpsS@s#l%Gs#j.UQ,#s>wVTGsSD#0G#k##'#k##s=0#2s$QDC#$CSc$m#$#;,DC#$CSj$m#$#VTpsSPs#i%Gs#g0Gs#^k##$#k##s==#.U5,#s?.WUZsSW#Hj##T$#j#/s==#VTGsSZ&%G#k##T$#k#/s=A#%+sAfYD#,'MU$l#7s#Ms#@#l#8*&#l#940#l#:s=9s=6#l#;s=As==#l#Fs=Fs=C#l#Gs=Ps=K#l#<s=Rs=S#l#K;<#l#L@A#l#>s#,s#%#%GScm#$#XWKSuScs#0#%s&+SuVWLScSi%Gs%x0SiGG)#VVb%#&UCTy2#DC#$CSi$m#$#.Ur;#DC#$CT#$m#$#UU[s=MUU[#VU9C#WT>C#s=CVTq#TrWT>Cs=Qs=EVTq#TrAT0%s=DAT0$#AT0%#AT0(#VV,CS,JCs=ES,#JC#S,s=FJC#Ms=GJCs=GS,s=HJCs=IS,#JCs=JS,#JC&H#VT%CsT6>Cs=6SH#?s=DKEEJ#S06s=CVT%C#>Cs=:SH#?s=HKEEJ#S0VT%CsKS>C#Sxs==?s=KKEEJ#S0[WMs=LKEEJ&#[WNs=MKEEJ+#>C.SH*?s=OKEEJ#S0>Cs=GSH,?s=QKEEJ#S0Ss=RKEEJs=>#UV%sTBWV<Cs:T#>C1Sx#?s=VKEEJ#S0Ss=WKEEJ1#>Cs=OU{s=K?s=YKEEJ#S0ZWOs=ZKEEJ#>Cs=RSx)?s=\KEEJ#S0Ss=]KEEJs=I#>C>Sx,?s=_KEEJ#S0Ss=`KEEJ>#Ss=aKEEJ&#Fs=bKEEJ*s=Z#Fs=cKEEJ.s=[#Fs=dKEEJ4s=\#Fs=eKEEJ8s=]#Fs=fKEEJ;s=^#l#0#s=Ls=Fl#1s#)s=i#l#2s#2s=t#j#3C#j#4C#j#5C#j#]C#0S(GGs4:#VVbs<]#%MS(%MS,#s4>#%GS.0S.sR~#$#$CS,Gk###V@%GSC0SCsS'#$##(#k##'#k##*#k##.#k##1#k##3#k#3C#k#4C#k#5C#k#]C#1TMTm-TMTm]DTmTM$#SBSFSNSMTLl#7>&#l#8s>Ss>P#l#9s>[s>W#l#:s>`s>]#l#;s>js>e#l#<s>ls>m#l#Ks#cs#d#l#Ls#is#j#l#^s#ss#o#l#>s#vs#u#l#=s$Vs$S#j#_s%n#j#Zs%r#&U_Tj2#%G#0$sSF#$#0s'SsSH#s$^#%Gs'S0s'TsSK#$##&#k##)#k##s&##m#0#%Gs&20s&3sSR#$#%Gs&30s&4sSU#$##&#k##3#k##s&-#m#,#[WPS#TjU^s()s'gs&3#-T/St1T/St4#D5%#j#AS$#7U^#TjWWQTjU^$ZSXV$s(0s(.*$#WUfS#TjHm#$#ZVcS#FTjHTh#WUfS#FH)s#'LsVOVUB$#XVZFS#V[#VT@F$%G#0$s6&#$#)s&TVUB#*&V3VA)#VUB#-VT@F#0#s6.WD#$SBl#7s5ys5u#l#8s?9s?6#l#9s?As?=#l#:s?Fs?C#l#;s?Ps?K#l#<s?Rs?S#l#Ks&Fs&G#l#Ls&Ls&M#ZV\S#FS(H1#VT@S(2%G#VT@F4%%##%#&V4V3)#VUB#AVT@SG#VT@F$%$#WD#%SBl#7s62s6.#l#8s?Ns?K#l#9s?Vs?R#l#:s?[s?X#l#;s?es?`#l#<s?gs?h#l#Ks&?s&@#l#Ls&Ds&E#l#>72#l#=s#-s#)#XWRS#Ms#1#WUfS#MHm#$#ZVcS#FMHD#'UbU_,#sMi:CC$#As79#s7#UVITiUWS#UWT#:CCHD'TyT(,#sMq:CC$#As7A#s7+WUcs7B'#'UCTy,#sMv:CC$#:CCMH$s7G$#WUcs7H$s72G$#%MsVgj##$#'VBUC,#sN#:CC$#:CCS(M$s7P$#'VdVB,#sN(:CC$#:CCSCS.$s7UH#%SCsVsk##$#:CCS,S($s7Y(#'VeVd,#sN1:CC$#:CCS.S,$s7^$#nV-%CC$#`CD#$%#E#EDj#*s7`#'VAVe,#sN8:CC$#ZU6s7dC&#2D$C%S.nV-%CC$#`CD#$%#E#EHj#*s7g#'V3VA,#sN?:CC$#:CCSESCZU6s7lC'$#H$C'SE'V4V3$C#SB'V5V4$C#SF'VCV5'VfVC,#sNJ$C#SN%SMsW7k##$#j#EC#,)sNO$C#SF'VgVf,#sNR%DsW>j#EC#'VhVg,#sNV:CC$#:CCDSG$s8'$#'VDVh,#sN[%#sWGk#a&#j#bC#:CC0/:CC1SM$s8/$#:CC*):CC+D$s82$#'V6VD,#sNf%#sWRk#a&#j#cC#$s8855&V6VD2#DC#$CU1$m#$#.UU;#DC#$CU2$m#$#JCs@HHs@MWU;Cs@;s;'>C#SHs%a?s@FKEEJ#S0Fs@GKEEJ#s@?#l#0#s@-s@'l#1(s@J#l#2s@Xs@U#j#3C#j#4C#,DsO#%#H,HsO%%#Mk##%#k#3C#k#4C#'ViWUWDsWr#TAl#7,%#l#8s@|s@y#l#9sA(sA$#l#:sA-sA*#l#;sA7sA2#l#<sA9sA:#l#K<=#l#LBs###m##s#+l#dsWWsWX#j#as#*#[STCs#?s#,#SGMDj#as#5#[STCs#Fs#9#SGS(SBZSTCs#Fs#D#SMDl#eDs#N#j#^s#J#ZSTCs#Ss#M#SNDl#^Ds#U#j#>s#X#U#Dl#>s#]s#\#U#Dl#>s#gs#f#j#=s#n#U#Dj#=s#u#nUd%s8qs#|%#`##s#xD#$##$s8rDs#s%S.sX4k##$#j#`s8u#U#s#|Ds8ws#xUD#l#=*%#j#as$,#U#Dj##s$7#WUcs8}s$0s8g$s8~s8js$(WUcs9#s$)s8jG$#%S,sXBj##$#$s9's8os$(:CCSBSE$s9)H#%SBsXGk##$#$s9,s8ts$6$s9-s8us#|ZU6s9.Cs$,s8v(D$Cs8xSE:CCSFSBZU6s91Cs$(s8y#H$Cs9(SF$Cs9)SN$Cs9*SM$Cs8~SG%SJsXSk##$#j#EC#$Cs9&SM:CCDSL$s9;s9'#%s9)sXYk#a$#j#bC#:CCs95SJ$s9@s9,#:CCs97D$s9Bs9.#k#a#)j#cC#$s9Es91s91&VjVE2#DC#$CU2$m#$#.U8;#DC#$CU$$m#$#VSvCsXn>C#SHsAH?sARKEEJ#S0SsASKEEJ#s8d6sVn6#(#6#6#6#(#6#(#6#(#6#(#(#(#L#VSvCsW4VSvCs9SWU;C$#>C#SHsA^?sAhKEEJ#S0FsAiKEEJ8sAa#l#0#sAOsAIl#1s@`sAl#l#2sAzsAw#j#3C#j#6So#%sY1D##H,sWAs9_%#Hk##%#k#3C#k#6So#WDsXpsY7WVl#7+$#l#8sBAsB>#l#9sBIsBE#l#:sBNsBK#l#;sBXsBS#l#<sBZsB[#l#Ks#0s#1#l#Ls#6s#7#m##s#El#dsXxsXy#j#as#>#[STCs9os#@#SLMDj#as#E#[STCs9zs#H#SLS(SBZSTCs9rs$e#SJDl#eDs#S#j#^s#P#ZSTCs9~s#R#SGDl#^Ds#W#j#>s#Y#U#Dl#>s#]s#\#U#Dl#>s#bs#a#j#=s#d#U#Dj#=s#g#nUd%s:6s9~%#`##s#iD#$##$s:7Ds%*%SEsYUk##$#j#`s::#U#s%EDs:<s%/UD#l#=*%#j#as#v#U#Dj##s#}#WUcs:Bs%Cs:-j##V@s%KVWW#Dj#=%#U#Dj##s$&#ZU:s$(s$'s$$)#Dj#=s$*#U#Dj##s%a#ZU:s%cs%bs%_s$.#Dj#=s%i#j#cC#j#bC#JCsBYMsBZJC#HsB[VT%CsYDLsWjVSvC#WV`Cs'q#>C&SH#?sBWKEEJ#S0>CsBOSH(?sBYKEEJ#S0VSvCsWpWU;Cs'w#>CsBSSH#?sB]KEEJ#S0FsB^KEEJ'sBV#FsB_KEEJ*sBW#l#0#sBEsB?l#12sBb#l#2s9KsBm#j#3C#j#4C#j#5C#VUBH5%M#%HS(,S(sX#%M#k##%#k##'#k#3C#k#4C#k#5C#YDTHsCQsZ1WXVkl#7.$#l#8sC;sC8#l#9sCCsC?#l#:sCHsCE#l#;sCRsCM#l#<sCTsCU#l#Ks*Hs*I#l#Ls*Ns*O#%sZ:sX2m#$#ZVlLs&DsX4s&As#.#^WYS-s&ETjSKsX5s&DTFSJSF#XVJS-SKsX6s&E'T(Ub,#sQU:CC$#As;%#s:kVUBsX;THAs;'s&@s:mWUcs;(s&I#$s;)s&9s&AG#s&@j###s&?$s;,s&7s&;$s;-s&/s&3$s;.s&)s&/ZU6s;/Cs&-s&#s&9D$Cs&%S.,s%}sQc:CCs%~#ZU6s;3Cs&*#s&&H$Cs&$SE$Cs&#SB$Cs%~SF$Cs%uSNk###s%|j#EC#$Cs&$SF$s;;s%is%sk#a#s%ej#bC#:CCs%ySM$s;?s%x#:CCs%ks%j:CCs%lD$s;B$#'VEV6,#sQv%#sZbk#a&#j#cC#$s;Hs%vs%v&VEV62#DC#$CU#$m#$#.U';#DC#$CT`$m#$#'WZViWDsZq#TBl#7s%gs%`#l#8sC{sCx#l#9sD'sD##l#:sD,sD)#l#;sD6sD1#l#<sD8sD9#l#K+,#l#L12#m##:l#dsZVsZW#j#a9#[STCs&9;#SGMDj#as#$#[STCs&As#'#SGS(SBZSTCs&As&C#SMDl#eDs#/#j#^s#-#ZSTCs&Qs#/#SNDl#^Ds#3#j#>s#5#U#Dl#>s#9s#8#U#Dl#>s#?s#>#j#=s#A#U#Dj#=s#D#nUd%s;ps&r%#`##s&wD#$##l#=#s%Ys%Wj#as#H#U#Dj##s#M#&W[Vj2#DC#$CT`$m#$#.U7;#DC#$CTn$m#$#WDsZys[@W\l#7s$ps$i#l#8sDJsDG#l#9sDRsDN#l#:sDWsDT#l#;sDasD\#l#<sDcsDd#l#K*+#l#L01#m##s%Nl#ds[%s[&#j#as%G#[STCs;xs%I#SLMDj#as%N#[STCs<'s%Q#SLS(SBZSTCs;{s&n#SJDl#eDs%\#j#^s%Y#ZSTCs<+s%[#SGDl#^Ds%`#j#>s%b#U#Dl#>s%fs%e#U#Dl#>s%ks%j#j#=s%m#U#Dj#=s%p#nUd%s<?s<+%#`##s%rD#$##l#=#s$cs$aj#as%x#U#Dj##s&##ZU:s&$s&#s%|#s$[Dj#=s&&#U#Dj##s']#ZU:s#}s'^s#{s#2#Dj#=s$##j#cC#j#bC#>CsDCSHs)h?sDMKEEJ#S0FsDNKEEJ#sDF#l#0#sD4sD.l#1s&ksDQ#l#2sD_sD\#j#3C#j#4C#%HMk##s;$#k#3C#k#4C#WDTHs[uVkl#7($#l#8sE#sD|#l#9sE+sE'#l#:sE0sE-#l#;sE:sE5#l#<sE<sE=#l#Ks+ps+q#l#Ls+us+v#ZVlLs$>THs$=8#^W]S-s$?U_SRTHsYwTFSLSN#XVKS-SRTHsYxVUDS.S#@QTy$RD#j#%R#VUDTyS#4s-2D5s-_#j#AS$#7T(#TyVUD#S#XW^T(%TyS#ZSXR)*U}$#@QT($R/#m#%#)s,o9#S.VUD#S#WW_%S.S#ZSXR52'$#VUDS,S#$R#+m#%#&S.T(USZD$Cs-r#j#CS$#4s-zs,{5s-~#USZ#DC#&9T(WVmTyT(;ZSXS$')%$#USZ-$Cs.)#m#%#&7T(WW`9S.T(ZSXS$2/%$#&S,T(USZ#$Cs.0#m#&#VTqs?{TrAT0#sECJCsE@Hs,1VT%CsZR>CsE/U{#?sE9KEEJ#S0>CsE-SH%?sE;KEEJ#S0SsE<KEEJ#s;wFsE=KEEJ#sE5sE)FsE>KEEJ'sE6#l#0#sE$sDzl#1,sEA#l#2.sEL#j#3C#j#4C#j#6So#$CDHk##s+|s;mk##$#k#3C#k#4C#k#6So#&V5V42#0#sZVYD#$T~SETvl#7-'#l#8sEusEr#l#9sE}sEy#l#:sF&sF##l#;sF0sF+#l#<sF2sF3#l#Ks+Ws+X#l#Ls+\s+]#VTps\Js,s%Gs+f,s+1sH$VTGs\M#0G#k##&#k##sF9#VTps\Qs,g%Gs,b0Gs+Wk##$#k##sF>#.U4,#sH/WUZs\X#Hj##T$#j#/sF>#VTGs\[&%G#k##T$#k#/sFB#%+sJgYD#,'MTnl#7s,Ns,A#l#8*&#l#940#l#:sF:sF7#l#;sFBsF>#l#FsFGsFD#l#GsFQsFL#l#<sFSsFT#l#Ks+Js+K#l#Ls+Ps+Q#l#=s##=#%GSim#$#XVaScSis#'#%Gs.z%s.{Sc#$#VU9Cs+RWT>C#sF<VTq#TrAT0#sF4JCsF,S(sF/JCsF2S(#JC#HsF3(sF(VT%C#VT%CsTa>C$U{#?sF.KEEJ#S0>CsF&SH&?sF0KEEJ#S0SsF1KEEJsEy#>C(Sxs+<?sF3KEEJ#S0SsF4KEEJsF3#SsF5KEEJs-%s+7FsF6KEEJ$sF.#FsF7KEEJs+;sF/#FsF8KEEJ)sF0#FsF9KEEJ-sF1#l#0#sE{sEul#14sF<#l#28sFG#j#3C#j#4C#j#5C#j#6So##sE.s&7$CMGk###V@0S,s[M#SC#0GS,##%k##%#k##(#k##+#k##sDA#k#3C#k#4C#k#5C#k#6So#&VCV52#%G#\D#TM$s+*SESBTLTwl#76'#l#8sFzsFw#l#9sG&sF~#l#:sG+sG(#l#;sG5sG0#l#<sG7sG8#l#Ks,.s,/#l#Ls,4s,5#l#=s#?s#<#%s)xD0Ds)x#$#XVLFTHUEHk##$#k#?C#%s>YD0Ds>Q#$#k###(k#?C###T$XWaFS#UCTi%DM0Ms(|#$#j#EC#&VBUC2#DC#$CSj$m#$#.Uu;#DC#$CTL$m#$#>Cs,8Sxs)6?sFyKEEJ#S0SsFzKEEJs%/#FsF{KEEJ#sFs#l#0#sFasF[l#1s)<sF~#l#2sG0sG-#j#3C#j#4C#0Hs)6#s=Q#0Ms)6#s%2#k##%#k#3C#k#4C#WDSFs)sSBl#7+$#l#8sGSsGP#l#9sG[sGW#l#:sG`sG]#l#;sGjsGe#l#<sGlsGm#l#K:;#l#L@A#'FUCZSTCs*Hs#'$#Tu[WbFTHUEHUCs#,#j#fs#7#j#?C#VSvCs?1WU;Cs(5#>C#SHsG3?sG=KEEJ#S0>CsG5Sxs(6?sG?KEEJ#S0SsG@KEEJ%#>Cs(;SHsG8?sGBKEEJ#S06s?8(#(#(#(#(#L#VSvC#WU;Cs(E#>CsGCSx#?sGMKEEJ#S0SsGNKEEJ.#FsGOKEEJ1sGG#l#0#sG5sG/l#1sFFsGR#l#2sG`sG]#j#3C#,s]$s?K%#D0Ds(C#$#%s](H,s])20H##%#k##'#k#3C#VDSFSBl#7.$#l#8sH)sH&#l#9sH1sH-#l#:sH6sH3#l#;sH@sH;#l#<sHBsHC#l#Ks#Ls#M#l#Ls#Rs#S#%V/H,V/A0H##%#m#'#YWcFTHUEH#j#fs#f#j#?C#XU`s#fT$#WdXU`s#ls#fs#9#VWes]&s+2m#$#]WfLS/s](s+4UbS{SfSM#\WgLS/s])VMUbS{TF#i#:WhS,T(s0sS{U_TjTkT;TZTzTYT8V#Ms%YU@s%Ds#wSCSEHD#l#gs%rs%q#l#hs'Ys'X#l#is+Es+x#l#js+zs+y#l#ks1VV$#l#ls1ZV$#j#ms1a#j#ns]=#V#HDj##s1r#j##s2C#Is2Ds27s2$#Dj#=s2F#j#os2W#V#HDj##s2Z#j##s3/#Is30s2}s2j#Dj#=s32#j#ps3E#V#HDj##s3L#j##s4?#Is4@s4.s3^#Dj#=s3g#ZSXS)s4Gs3~#T9Dj#=s4S#V#HDj##s4\#j##s5;#Is5<s5%s4t#Dj#=s5D#j#qs^s#V#HDnVn%s^us5t$##s5jD#$%#?###j#=s68#j#Rs^{#V#HDj##s6[#j#?s^~#YTWs_#s7/s7##Dj#=s7Q#j#Ss_%#V#HDj##s7v#j#?s_(#YTWs_)s8Ls8@#Dj#=s8p#j#Ts_+#V#HDj##s9;#j#?s_.#YTWs_/s9os9c#Dj#=s:9#j#Us_1#V#HDj##s:b#j#?s_4#YTWs_5s;<s;0#Dj#=s;d#j#Vs_7#V#HDj##s<3#j#?s_:#YTWs_;s<ms<_#Dj#=s=;#j#Ws_=#V#HDj##s=h#j#?s_@#YTWs_As>Fs>9#Dj#=s@(#j#NS)#$S)SEs>n##s>Xj#Qs_B#*s_C#j#Rs_H#*s_I#j#Ss_J#*s_K#j#Ts_L#*s_M#j#Us_N#*s_O#j#Vs_P#*s_Q#j#Ws_R#*s_S#j#NS)#U#D)s@31SaSm4#D5s>T#j#AS$#7U]#U=9(#QI#U]sAMS*8LIS%#S&S'Hk##,#k#NS)#m#@#ZVYS-s@Gs@FsAUs?6#]WiLS/IS%sA?S&S'sAV#ZSXS)sAWsAJ#S.Dj#=sAZ#j#Ms_f#V#HDj##sA^#j#?s_i#YTWs_jsAqsAc#Dj#=sB}#j#PS)#_WjLS/IS%sC,S&S'sB~sBysAv#BSISOsB}SQSeSdS`SUSWSV/#OsB|Ps]OSPs]N8LIS%sC/S&S'#m#&#l#rsC<sC;#l#ssD6sD5#)sDN1SCSE4#D5sDH#j#AS$#7SI#SP9(#QI#SIsEFS*'FSI+s_~#BSQSe#SdS`SUSWSVSwT&+s`$SY/$O#Ps]`SOs]_8LIS%(S&S'#m#1#&,SIWVmSPSI.ZSXS$sD_sDN%$#l#HsDesDc#l#=sDisDg#UT'TtnS+#$#IsE5##%#sE+#sE)8LIS%#S&S'sE8m#&#YT?IsX%&sE.S18LIS%#S&S'sE;m#%#j#HsE'#XVosEHsE)#HU#Dl#HsH)sEb#l#tsEfS+#l#usG*C#l#vsEjC#VTcSUT_ZSTCsFqsEm$#Dl#=sF+sF,#YU*sH#sH#sG~sG}sFtVTcSW#;#-sGv#VSk#GUT'#YU*sH)sH)sH(sH'sUrVTcSU#;#-sGA#1sGB$4#D5%#j#AS$#7SV#SW&#SV)#9#%QI#SV1S*YT?IsXE0#S1'FSV+s`S#BT&Tb#TaTsU\U)ToU(UY+s`USU/$O#Ps^5Sws^48LIS%(S&S'#m#=#ZSXRsG3sG4#sGTStZSXRsGUsG5#sH;UPVSksH-GUT'#=sGOYU*sHCsHCsHBsHA#VTcS`#;#nTX$Q$#?CsH8#%$#@##G-sG\#1sG]$4#D5%#j#AS$#7SV#SW&#SV)#9#%QI#SVsH=S*YT?IsX`2#S18LIS%#S&S'9m#6#YT?IsHXSD%S18LIS%#S&S'<m#%#l#BsGpsGo#l#=sGusGs#j#BsH/#$S+sH1TtUVVsH_'FT&+s`x#BTaTs#U\U)ToU(UYUXUW+s`zSV/$O#Ps^ZTbs^Y]VWLS/IS%(sF.S&S'#2sHj=sHkYU*sHdsHdsHcsHbsHeVTcSV#;#nTX$Q$#?C&#%$#@##G-(#VSk#GUT'#1sHmsHc4#D5sHd#j#AS$#7T&#Sw&#T&)#9#%QI#T&-S*YT?IsY',#S1YT?IsHyTt#S18LIS%#S&S'8m#8#j#B@#XVosHSB#HU#Dl#BsI,sI(#l#tsI.S+#HIS*S1TaTs'FTs+sa>#BU)To#U(UYUXUWUzV+Uy+sa@Tb/$O#Ps^|U\s^{8LIS%(S&S'#m#*#l#wsI:sKQ#j#xsKX#j#ysK^#V#HDj##sKe#j##sKx#IsKysKusKl#Dj#=sL##j#ZsL.#V#HDj##sL5#j##sLR#IsLSsLJsLA#Dj#=sLY#j#zsLi#V#HDj##sLp#j##sMA#IsMBsM.sM%#Dl#=sMJsMH#j#+sML#j#,sMY#j#-sM]#]STNSssM`#SfHS.SESCZSXNSfsMw#SsDl#^DsN$#j#>sN&#U#Dl#>sN*sN)#j#=sN/#U#Dj#=sN4#nUd%sW@sN@%#%##sN6D#$##$sWADsN4HIS*S1U4U5'FU5+sah#BUTUv#UtV*UsUuUrUQUq+sajUR/$O#Ps_JUSs_I8LIS%(S&S'#k##*#j#%sWJ#U#sNRDsWLsN?UD#l#=0%#l#-sNRsNP#j#+sNY#j#,sNb#V#HDj##sNf#j##sO%#IsO&sNzsNq#Dj#=sO)#j#-sO4#V#HDj##sO9#j##sOY#IsOZsOPsOG#Dj#=sO]#j#.N#V#HDj##sOj#j#?N#YTWNsP%sOx#Dl#*sPHsP3#j#{sPJ#j#(N#V#HDj##sPP#j#?N#YTWNsPdsPW#Dl#*sP`sPr#j#|sPx#j#}sQ'#V#HDj##sQ1#j##sQO#IsQPsQFsQ=#Dj#=sQX#j#~sQl#V#HDj##sQq#j##sRC#IsRDsR2sR)#Dj#=sRH#j$#sRb#V#HDj##sRg#j##sSA#IsSBsS,sS##Dj#=sSF#j$$sSd#V#HDj##sSi#j##sTK#IsTLsT2sT)#Dj#=sTP#j$%sTr#V#HDj##sTw#j##sUa#IsUbsUDsU;#Dj#=sUf#j#&N#V#HDj##sV+#j#?N#YTWNsVVsVM#Dj#=sVv#j#'Q#V#HDj##sW0#j#?Q#YTWQsWPsWG#Dl#*sX=sWe#j#ysX?#j#ZsXC#V#HDj##sXH#j##sXW#IsXXsXVsXM#Dj#=sX\#j$&sXc#V#HDj##sXj#j##sY##IsY$sX{sXr#Dj#=sY*#j$'sY6#V#HDj##sY;#j##sYY#IsYZsYQsYH#Dj#=sY^#j$(sYl#V#HDj##sYp#j##sZ7#IsZ8sZ,sZ##Dl#=sZpsZ;#j$)sZr#j$*sZv#V#HDj##sZ}#j##s[0#Is[1s[.s[%#Dj#=s[7#j$+s[A#V#HDj##s[H#j##s[a#Is[bs[[s[R#Dj#=s[h#j$,s[v#V#HDj##s[}#j##s\B#Is\Cs\8s\/#Dj#=s\I#j$-s\[#V#HDj##s\b#j##s]/#Is]0s\}s\t#Dj#=s]6#j$.s]L#V#HDj##s]P#j##s^&#Is^'s]os]f#Dj#=s^*#j$/s^B#V#HDj##s^I#j##s_##Is_$s^js^a#Dj#=s_*#j$0s_G#V#HDj##s_N#j##s`2#Is`3s_ts_k#Dj#=s`9#j$1s`[#V#HDj##s`^#j##saO#IsaPsa/sa$#Dl#@sawsaR#j$2say#j$3sa|#j$4sa~#j$5sb,#j$6sb.#j$7sb0#j$8sb2#j$9sb6#j$:sb8#j$;scN#j$<scT#j$=scU#j$>scV#j$?scW#j$@scX#j$AscY#j$BscZ#j$Csc[#j$Dsc\#j$EscY#j$FQ#j$GV$#j#OC#l$Hsccscd#l$Iscjsck#l$Jsczsc{##"). Qed.

Lemma ract_block : forall stY g2 msk mY (t0 t1 a1' a2 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stY -> active stY sc = Some g2 -> gmf st sc g2 ->
  msk = m_freed (get_meta_rec stY g2) ->
  (forall mn, m_next (get_meta_rec stY g2) = Some mn -> gmf st sc mn) ->
  m_next (get_meta_rec stY g2) <> None ->
  rmrep stY mY -> mem_inv usegs mY -> rw_cells usegs mY (spv + -144) (FRM junk) -> stk usegs mY lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mY ->
  rimplT o (ta_act sc K bail stY g2 msk) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g2)) a1' a2 (wz (sxv msk)) (Z_to_bv 64 2) a5 a6 a7) F (Z_to_bv 64 0x6d418) fc None mY (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until junk. intros TR HA GM HM GN NN MRY MIY FRY STY PEY.
  destruct (gmf_geom st stY sc g2 TR GM) as (MSY & RAY & RFY & MWY & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stY mY g2 MRY MSY) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
  destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
  pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & SCR0 & _).
  assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
  assert (EMb : m_mem (get_meta_rec stY g2) = Some b) by (rewrite EM; exact Hmem).
  assert (MSKR : 0 <= msk < 2^32) by (rewrite HM; exact RFY).
  assert (HG : bv_unsigned (Z_to_bv 64 (conc st g2)) = conc stY g2) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).
  unfold ta_act. rewrite EMb. cbn [default].
  replace (group_active_idx stY b) with (g_active_idx gh1).
  2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold RR.
  destruct (Z.land msk (mask_upto (g_active_idx gh1)) =? 0) eqn:ZR.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in ZR.
    destruct (m_next (get_meta_rec stY g2)) as [mn|] eqn:GNY; [|exfalso; apply NN; reflexivity].
    cbn [optr_eqb]. destruct (aptr_eqb mn g2) eqn:EQ; cbn [negb].
    + (* [comment removed for export] *)
      apply aptr_eqb_eq in EQ. subst mn.
      destruct (Z.eq_dec (m_sizeclass (get_meta_rec st g2)) 0) as [SCZ|SCNZ].
      * (* [comment removed for export] *)
        assert (AIE : g_active_idx gh1 = m_last_idx (get_meta_rec st g2)).
        { destruct AI1 as [E|[_ P]]; [rewrite E; apply SC0; exact SCZ| exfalso; exact (P g2 GMg SCZ)]. }
        assert (MZ : msk = 0).
        { apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
          destruct (Z.testbit msk i) eqn:Ti; [|reflexivity]. exfalso.
          assert (IL : i <= m_last_idx (get_meta_rec st g2)).
          { pose proof (tr_bits _ _ _ TR g2 i Hi) as TB. rewrite <- HM, Ti in TB. rewrite orb_true_r in TB. specialize (TB eq_refl).
            apply orb_prop in TB. destruct TB as [TB|TB]; [exact (gmf_abits _ _ _ GM i Hi TB)| exact (gmf_fbits _ _ _ GM i Hi TB)]. }
          assert (TB2 : Z.testbit (Z.land msk (mask_upto (g_active_idx gh1))) i = true).
          { rewrite Z.land_spec, Ti. unfold mask_upto. replace (2 ^ (g_active_idx gh1 + 1) - 1) with (Z.ones (g_active_idx gh1 + 1)) by (rewrite Z.ones_equiv; lia).
            rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. apply Z.ltb_lt. lia. }
          rewrite ZR, Z.bits_0 in TB2. discriminate. }
        (* [comment removed for export] *)
        cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai.
        destruct (m_avail (get_meta_rec stY g2) =? 0); unfold guard; [|apply rimplT_undef].
        cbv beta. rewrite <- HM, MZ, Z.land_0_l. cbn [Z.eqb negb]. apply rimplT_undef.
      * (* [comment removed for export] *)
        destruct (m_avail (get_meta_rec stY g2) =? 0) eqn:AV0.
        2:{ cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai, AV0. unfold guard. apply rimplT_undef. }
        apply Z.eqb_eq in AV0.
        assert (SCY : 1 <= m_sizeclass (get_meta_rec stY g2) < 48) by (rewrite ESC; pose proof (gmf_sc48 _ _ _ GM); lia).
        rewrite <- ECONC. riprefixT. eapply evt_mono.
        { eapply (ract_span_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R); [exact ZR| exact GNY| exact MWY| exact SCY| | rewrite GM1; exact GMg| exact AV0| exact MIY].
          intros o' Ho'. rewrite (tr_get_shadow _ _ _ _ TR). apply UNK. exact Ho'. }
        cbv beta. intros ms' (t0' & t1' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
        cbv zeta iota beta.
        match goal with |- rimplT _ (ta_avz _ _ ?st3 _) _ _ _ => set (stG := st3) in * end.
        assert (TRG : ta_rel sc st stG).
        { eapply ta_rel_trans; [exact TR|]. apply ta_rel_set_gai.
          - apply land31_range.
          - intros h g' Hh Hg'. rewrite Hgh1 in Hh. inversion Hh; subst h. rewrite GM1 in Hg'. rewrite GMg in Hg'. inversion Hg'; subst g'. lia. }
        rewrite (tr_conc _ _ _ g2 TR).
        eapply (ravz_block 0x6d44c stG g2 m5); [right; reflexivity| exact TRG| | exact GM| exact MR5| exact MI5| | |].
        -- unfold stG. rewrite active_set_gai. exact HA.
        -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply rdisjoint_high; [|unfold spv in *; lia].
           pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
        -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply rdisjoint_high; [|lia].
           pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
        -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
           cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply (rta_fp_grp st lo spv x b gh Hgh). rewrite <- (tr_conc _ _ _ b TR). lia.
    + (* [comment removed for export] *)
      assert (NE : mn <> g2) by (intros ->; rewrite (proj2 (aptr_eqb_eq g2 g2) eq_refl) in EQ; discriminate).
      pose proof (GN mn eq_refl) as GMn.
      destruct (gmf_geom st stY sc mn TR GMn) as (MSn & _ & _ & _ & _ & _ & _ & _ & ECONCn).
      rewrite <- ECONC. riprefixT. eapply evt_mono.
      { eapply (ract_next_walk stY mY g2 b gh1 sc msk MRY MSY SC EMb Hgh1 AI1R); [exact ZR| exact GNY| exact NE| exact MSn| exact MIY]. }
      cbv beta. intros ms' (a1'' & a2' & a3' & a4' & m5 & -> & MU & WM & MI5 & MR5).
      assert (TRN : ta_rel sc st (set_active sc (Some mn) stY)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
      rewrite ECONCn.
      eapply (ravz_block 0x6d440 (set_active sc (Some mn) stY) mn m5); [left; reflexivity| exact TRN| | exact GMn| exact MR5| exact MI5| | |].
      -- rewrite active_set_active, Z.eqb_refl. reflexivity.
      -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply rdisjoint_high; [|unfold spv in *; lia].
         intros lo' hi' [E|[]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
      -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply rdisjoint_high; [|lia].
         intros lo' hi' [E|[]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
      -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
         cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
  - (* [comment removed for export] *)
    apply Z.eqb_neq in ZR.
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (ract_skip_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R MSKR); [exact ZR| exact MIY]. }
    cbv beta. intros ms' (a1'' & a2' & a3' & a4' & ->). rewrite ECONC.
    eapply (ravz_block 0x6d440 stY g2 mY); [left; reflexivity| ..]; eassumption.
Qed.

(* [comment removed for export] *)
Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

Lemma rm_block : forall stX g1 mX (P : aptr -> Prop) (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stX -> active stX sc = Some g1 -> rnclosed stX P -> P g1 ->
  rmrep stX mX -> mem_inv usegs mX -> rw_cells usegs mX (spv + -144) (FRM junk) -> stk usegs mX lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mX ->
  rimplT o (ta_m sc K bail stX g1) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g1)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x6d3ec) fc None mX (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until junk. intros TR HA NC P1 MRX MIX FRX STX PEX.
  destruct (NC g1 P1) as (GM & mn & GN1 & Pmn).
  destruct (gmf_geom st stX sc g1 TR GM) as (MSX & RAX & RFX & MWX & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stX mX g1 MRX MSX) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  pose proof (gmf_mw _ _ _ GM) as (LI0 & FB0 & SCR0 & _).
  unfold ta_m, RR.
  set (f := m_freed (get_meta_rec stX g1)).
  destruct ((f =? mask_upto (m_last_idx (get_meta_rec stX g1))) && negb (m_freeable (get_meta_rec stX g1) =? 0)) eqn:FSK.
  - (* [comment removed for export] *)
    pose proof FSK as FSK'. apply andb_prop in FSK'. destruct FSK' as [FE FB]. apply Z.eqb_eq in FE. apply Bool.negb_true_iff in FB. apply Z.eqb_neq in FB.
    rewrite GN1.
    destruct (NC mn Pmn) as (GMn & mn2 & GN2 & Pmn2).
    destruct (gmf_geom st stX sc mn TR GMn) as (MSn & RAn & RFn & MWn & EMn & _ & _ & _ & ECONCn).
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_skip_walk stX mX g1 sc MRX MSX SC RFX MWX); [exact FSK| exact GN1| exact MSn| exact RFn| exact MIX]. }
    cbv beta. intros ms' (a1'' & a2' & m5 & -> & MU & WM & MI5 & MR5).
    assert (TRN : ta_rel sc st (set_active sc (Some mn) stX)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
    rewrite ECONCn.
    eapply (ract_block (set_active sc (Some mn) stX) mn (m_freed (get_meta_rec stX mn)) m5); try eassumption.
    + rewrite active_set_active, Z.eqb_refl. reflexivity.
    + reflexivity.
    + intros q Hq. rewrite rec_set_active in Hq. rewrite GN2 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn2)).
    + rewrite rec_set_active, GN2. discriminate.
    + eapply rw_cells_transport; [exact FRX| exact MU| exact WM|]. apply rdisjoint_high; [|unfold spv in *; lia].
      intros lo' hi' [E|[]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
    + eapply stk_transport_disjoint; [exact STX| exact MU| exact WM|]. apply rdisjoint_high; [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
    + eapply rpres_except_trans; [exact PEX|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
  - (* [comment removed for export] *)
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_act_walk stX mX g1 sc MRX MSX RFX MWX); [exact FSK| exact MIX]. }
    cbv beta. intros ms' (a1'' & a2' & ->). rewrite ECONC.
    eapply (ract_block stX g1 f mX); try eassumption.
    + reflexivity.
    + intros q Hq. rewrite GN1 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn)).
    + rewrite GN1. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rta_phase : forall (t0 t1 a0 a2 a3 a4 a5 a6 a7 : word),
  a0 = Z_to_bv 64 sc ->
  rmrep st m -> mem_inv usegs m -> stk usegs m lo spv ->
  (forall st1 m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
     ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
     rmrep st1 m' -> mem_inv usegs m' -> rw_cells usegs m' (spv + -144) (FRM junk) -> stk usegs m' lo (spv + -144) ->
     rpres_except (rta_fp st lo spv) m m' ->
     rimplT o (K st1 0) s Q (MS (RR t0' t1' a0' a1' a2' a3' a4' a5' a6' a7') F (Z_to_bv 64 0x6d504) fc None m' (seg_rom usegs))) ->
  rimplT o (try_avail sc st K bail) s Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof. try hcb. try hsb.
  intros until a7. intros A0 MR MI ST HK0.
  assert (AMS : forall g, active st sc = Some g -> meta_slot st g) by (intros g Hg; exact (gmf_slot _ _ _ (proj1 (taf_head _ _ TAF g Hg)))).
  riprefixT. eapply evt_mono.
  { eapply (ras_entry_walk st m sc lo MR SC CLO AMS); [exact A0| exact ST| exact LO| exact MI]. }
  cbv beta. intros ms' (a1x & m1 & junk & -> & FR1 & ST1 & MU1 & WM1 & MI1 & MR1).
  assert (PE1 : rpres_except (rta_fp st lo spv) m m1).
  { eapply rpres_except_of_munch_cov; [exact MU1| exact WM1|]. cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_stack. unfold spv; lia. }
  clear MU1 WM1.
  rewrite (try_avail_eq sc K bail st).
  destruct (active st sc) as [g|] eqn:HA.
  2:{ (* [comment removed for export] *)
      eapply (HK0 st m1); [| apply ta_rel_refl| exact HA| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      unfold ta_fail, try_avail. rewrite HA. reflexivity. }
  destruct (taf_head _ _ TAF g HA) as [GM GSC].
  pose proof (gmf_slot _ _ _ GM) as MSg. pose proof (gmf_avail _ _ _ GM) as RAg. pose proof (gmf_freed _ _ _ GM) as RFg.
  pose proof (rmeta_slot_bounds st m1 g MR1 MSg) as (Gpos & GC & GI & _ & _).
  unfold pw. cbn [oconc]. unfold wz.
  destruct (m_avail (get_meta_rec st g) =? 0) eqn:AV; cbn [negb].
  2:{ (* [comment removed for export] *)
      apply Z.eqb_neq in AV.
      riprefixT. eapply evt_mono.
      { eapply (rt1_fin_walk st m1 g sc MR1 MSg RAg); [exact AV| exact MI1]. }
      cbv beta. intros ms' ->.
      eapply (rfin_block st g (m_avail (get_meta_rec st g)) m1); [apply ta_rel_refl| exact HA| exact GM| reflexivity| lia| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1]. }
  apply Z.eqb_eq in AV.
  destruct (gmf_links _ _ _ GM) as (nx & pv & GN & GP).
  destruct (taf_next _ _ TAF g nx GM GN) as (GMn & SCn & PRn).
  destruct (taf_prev _ _ TAF g pv GM GP) as (GMp & NXp).
  destruct (m_freed (get_meta_rec st g) =? 0) eqn:FZ.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in FZ.
    riprefixT. eapply evt_mono.
    { eapply (rt1_deq_walk st m1 g sc MR1 MSg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. intros ms' ->.
    destruct (decide (nx = g)) as [->|NEn].
    + (* [comment removed for export] *)
      rewrite (dequeue_self_eq sc g st GN).
      replace (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (@None aptr)
        by (change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc); rewrite active_set_active, Z.eqb_refl; reflexivity).
      cbn [Z.eqb].
      riprefixT. eapply evt_mono.
      { eapply (rdeq_self_walk st m1 g sc MR1 MSg SC); [exact GN| exact MI1]. }
      cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2).
      eapply (HK0 _ m2).
      * unfold ta_fail. rewrite (try_avail_eq sc kS bS st), HA, AV, FZ. cbn [Z.eqb negb].
        rewrite (dequeue_self_eq sc g st GN).
        change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
        rewrite active_set_active, Z.eqb_refl. reflexivity.
      * eapply ta_rel_trans; [apply ta_rel_set_active|]. unfold clr.
        replace (get_meta_rec st g) with (get_meta_rec (set_active sc None st) g) by reflexivity. apply ta_rel_put_links.
      * change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
        rewrite active_set_active, Z.eqb_refl. reflexivity.
      * exact MR2.
      * exact MI2.
      * eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply rdisjoint_high; [|unfold spv in *; lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply rdisjoint_high; [|lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|exact I]]; intros x Hx; [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]].
    + (* [comment removed for export] *)
      assert (NEp : pv <> g).
      { intros ->. rewrite NXp in GN. inversion GN. subst nx. apply NEn. reflexivity. }
      rewrite (dequeue_other_eq sc g nx pv st GN GP NEn NEp HA). cbv zeta.
      match goal with |- context [active ?stq sc] => set (st1 := stq) in * end.
      assert (HA1 : active st1 sc = Some nx).
      { unfold st1. unfold active, put_meta, set_metas, set_active, upd_ctx. cbn [s_ctx ctx c_active set_active_map]. apply lookup_insert_eq. }
      rewrite HA1.
      pose proof (gmf_slot _ _ _ GMn) as MSn. pose proof (gmf_slot _ _ _ GMp) as MSp.
      riprefixT. eapply evt_mono.
      { eapply (rdeq_other_walk st m1 g sc MR1 MSg SC HA); [exact GN| exact GP| exact NEn| exact NEp| exact MSn| exact MSp| exact MI1]. }
      cbv beta. intros ms' (a1'' & m2 & -> & MU & WM & MI2 & MR2). fold st1 in MR2.
      assert (TR1 : ta_rel sc st st1).
      { unfold st1.
        lazymatch goal with |- ta_rel _ _ (put_meta _ _ ?sC) =>
          lazymatch sC with set_active _ _ ?sB =>
            lazymatch sB with put_meta _ _ ?sA =>
              apply (ta_rel_trans sc st sC); [apply (ta_rel_trans sc st sB); [apply (ta_rel_trans sc st sA); [apply ta_rel_put_next| apply ta_rel_put_prev] | apply ta_rel_set_active] |];
              unfold clr; replace (get_meta_rec st g) with (get_meta_rec sC g); [apply ta_rel_put_links|]
            end end end.
        rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
        rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
      (* [comment removed for export] *)
      assert (REC1 : forall q, q <> g -> get_meta_rec st1 q =
                 if aptr_eqb q nx then m_set_prev (Some pv) (if aptr_eqb nx pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st nx)
                 else if aptr_eqb q pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st q).
      { intros q Hq. unfold st1. rewrite (get_meta_rec_put_other _ g) by exact Hq. rewrite rec_set_active.
        rewrite get_meta_rec_put. destruct (aptr_eqb q nx) eqn:E1.
        - apply aptr_eqb_eq in E1. subst q. f_equal. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv) eqn:E2; [apply aptr_eqb_eq in E2; subst; reflexivity| reflexivity].
        - rewrite get_meta_rec_put. reflexivity. }
      eapply (rm_block st1 nx m2 (fun q => gmf st sc q /\ q <> g)); [exact TR1| exact HA1| | split; [exact GMn| exact NEn] | exact MR2| exact MI2| | |].
      * intros q [GMq NEq]. split; [exact GMq|]. rewrite (REC1 q NEq).
        destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP). destruct (taf_next _ _ TAF q qn GMq QN) as (GMqn & _ & PRqn).
        destruct (aptr_eqb q nx) eqn:E1.
        -- apply aptr_eqb_eq in E1. subst q. cbn [m_next m_set_prev].
           destruct (aptr_eqb nx pv) eqn:E2.
           ++ exists nx. cbn. split; [reflexivity|]. split; [exact GMn| exact NEn].
           ++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->.
              rewrite PRqn in GP. inversion GP. subst pv. rewrite (proj2 (aptr_eqb_eq nx nx) eq_refl) in E2. discriminate.
        -- destruct (aptr_eqb q pv) eqn:E2.
           ++ apply aptr_eqb_eq in E2. subst q. cbn. exists nx. split; [reflexivity|]. split; [exact GMn| exact NEn].
           ++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->. rewrite PRqn in GP. inversion GP. subst pv.
              rewrite (proj2 (aptr_eqb_eq q q) eq_refl) in E2. discriminate.
      * eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply rdisjoint_high; [|unfold spv in *; lia].
        pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply rdisjoint_high; [|lia].
        pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]]; intros x Hx;
          [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]| eapply rta_fp_meta; [exact MSp| lia]| eapply rta_fp_meta; [exact MSn| lia]].
  - (* [comment removed for export] *)
    apply Z.eqb_neq in FZ. rewrite GN.
    riprefixT. eapply evt_mono.
    { eapply (rt1_next_walk st m1 g sc MR1 MSg SC RFg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2). rewrite GN in MR2 |- *. unfold pw. cbn [oconc]. unfold wz.
    eapply (rm_block (set_active sc (Some nx) st) nx m2 (gmf st sc)); [| | | exact GMn| exact MR2| exact MI2| | |].
    + apply ta_rel_set_active.
    + rewrite active_set_active, Z.eqb_refl. reflexivity.
    + intros q GMq. split; [exact GMq|]. rewrite rec_set_active. destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP).
      exists qn. split; [exact QN|]. exact (proj1 (taf_next _ _ TAF q qn GMq QN)).
    + eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply rdisjoint_high; [|unfold spv in *; lia].
      intros lo' hi' [E|[]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
    + eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply rdisjoint_high; [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; hcb; unfold RCTX, Malloc.alloc_ceiling, Decode.alloc_ceiling in *; lia.
    + eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.
End PHASE.

End HCW.


