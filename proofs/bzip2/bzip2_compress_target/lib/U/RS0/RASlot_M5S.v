(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W9 ASlot_W13 ASlot_W14 ASlot_I ASlot_M0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_M5D.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_M5D.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_M5D.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_M5D.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W14 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M4P OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.ASlot_M5P OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocKit_A2 RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4 RASlot_W13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W18.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_M2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_M2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_M2.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocKit_A2 RMalloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_M2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_M2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module RASlot_M5D.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_M5D.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_W2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M2.RASlot_M0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M2.

 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  (intros MR REL; cps_intros (ar & arr & kk & Ha & Hk & ->)). pose proof MR as (WF & _). cps_pose WF as (_ & _ & _ & WA & _).
  cps_destruct (WA ar arr Ha) as (r & Hr & _). cps_destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma rmalloc_fp_widen st0 stA stB lo sp sp' a :
  sp' <= sp ->
  (forall rid r, (s_regions stA) !! rid = Some r ->
     exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rmalloc_fp st0 stA lo sp' a -> rmalloc_fp st0 stB lo sp a.
Proof.
  intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

(* [comment removed for export] *)
Lemma rregion_byte_raw st m rid r off v :
  rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) off = Known v -> m (wa (r_base r + off)) = Some (b8 v).
Proof.
  intros MR Hr Hk Ho Hc.
  destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
  cps_destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). bz_ceil.
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  cbn [ov_read_bytes] in RD.
  destruct (m (wa (r_base r + off))) as [b|] eqn:E.
  - cbn in RD. inversion RD. reflexivity.
  - rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x4413c.
Proof. intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis CLO : alloc_ceiling <= lo.
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
(* [comment removed for export] *)
Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
  mkR (Z_to_bv 64 0x2a5e4) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
      a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
      (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
      (wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6'.

(* [comment removed for export] *)
Definition rnest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
    (m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
  leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
  mem_inv rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp - 144) /\
  rw_cells rsegs m'' (errno_addr tp) [C4 errv''] /\ rauxv_ok m'' (bv_unsigned sp - 144) /\
  rmrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
  rpres_except (rmalloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
  mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
  as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
  rw_cells rsegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ rmrep st2 m4.

Definition rNFAIL_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 ->
  rimplT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x2a65c) fc None m'' (seg_rom rsegs)).

Definition rNSUCC_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 ->
  0 <= idx -> active st3 (ncls sc cnt1) = Some g3 -> slot_ok st3 g3 b3 r3 idx (nreq sc cnt1) ->
  (forall a, r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx - 4 <= a
             < r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx + get_stride (get_meta_rec st3 g3) - 4 ->
     rmalloc_fp st0 st3 lo (bv_unsigned sp - 144) a) ->
  (s_regions st0 = ∅ -> rdv pans_mem o st3 (fst b3, snd b3 + (16 + get_stride (get_meta_rec st3 g3) * idx) + -3) = 0) ->
  rimplT o (ag_tail full_lay (upd_meta mm (m_set_maplen 0) (nest_layout st3 g3 idx (ncls sc cnt1) (UNIT * size_class sc) cnt1))
              sc mm (slot_of st3 g3 idx) cnt1 (cnt1 - 1) (as_kq sc k bail)) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 idx) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x2a5e8) fc None m'' (seg_rom rsegs)).
End LEVEL.

End ACeilS1.
End RASlot_M5D.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_W2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W13.RASlot_W14 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W18 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M2.RASlot_W19 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M2.RASlot_M0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_M5S.RASlot_M5D.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv4.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma rgrp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. (intros EG; cps_intros (b & gh & Hb & Hf & Ho)). exists b, gh. rewrite EG. auto. Qed.

Lemma rmrep_st_model stT sc cnt ai ml mt p (SC : 0 <= sc < 48) (CNT : 1 <= cnt <= 32)
      (REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml) (P0 : 0 <= snd p) m :
  rmrep (stFin stT sc cnt ai ml mt p) m -> rmrep (st_model stT sc cnt ai mt p) m.
Proof.
  intros MR. eapply (rmrep_extW _ _ _ MR); try reflexivity.
  intros q. apply (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
Qed.

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
Hypothesis CLO : alloc_ceiling <= lo.
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

Lemma rnsucc_ok : rNSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof.
  intros st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC I0 HA3 SO3 SPAN3 RDV3.
  cps_destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. bz_ceil.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  cps_destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), idx; split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 idx AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  cps_pose (rmeta_slot_bounds st3 m'' mm MR'' MS3) as (Gpos & GC & GI & _).
  (* [comment removed for export] *)
  pose proof (so_mem _ _ _ _ _ _ SO3) as Hmem3. pose proof (so_reg _ _ _ _ _ _ SO3) as Hr3. pose proof (so_kind _ _ _ _ _ _ SO3) as Hk3.
  pose proof (so_mslot _ _ _ _ _ _ SO3) as MSLg. pose proof (so_fit _ _ _ _ _ _ SO3) as FIT3. pose proof (so_idx _ _ _ _ _ _ SO3) as IDX3.
  pose proof (so_b0 _ _ _ _ _ _ SO3) as B30. pose proof (so_span _ _ _ _ _ _ SO3) as SP3. pose proof (so_li _ _ _ _ _ _ SO3) as LI3.
  pose proof (mf_active _ _ MF3) as FA3. change (fact_active (strip st3)) with (fact_active st3) in FA3.
  cps_destruct (FA3 (ncls sc cnt1) g3 HA3) as (_ & GSC3 & _).
  pose proof (lf_host_stride _ (isf_lf _ _ F3) g3 b3 Hmem3 ltac:(change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3); rewrite GSC3; lia)) as STR3.
  change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in STR3. rewrite GSC3 in STR3.
  cps_pose (lf_mw _ (isf_lf _ _ F3) g3) as (MW3 & _ & _). change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in MW3.
  set (strideg := get_stride (get_meta_rec st3 g3)) in *.
  set (szc := size_class sc) in *.
  assert (FITg : 16 * szc * cnt1 + 16 <= strideg) by lia.
  assert (SZC1 : 16 * szc <= 16 * szc * cnt1) by nia.
  assert (SO_N : slot_ok st3 g3 b3 r3 idx (UNIT * size_class (ncls sc cnt1) - IB)) by (eapply slot_ok_N; [exact SO3| unfold IB; lia| unfold UNIT, IB; lia]).
  set (X := snd b3 + (16 + strideg * idx)) in *.
  set (p := (fst b3, X) : aptr).
  cps_pose (rregion_facts st3 m'' (fst b3) r3 MR'' Hr3) as (R4 & RAL & RC & RI1 & RI2). bz_ceil.
  assert (CB3 : conc st3 b3 = r_base r3 + snd b3) by (apply conc_region'; exact Hr3).
  assert (CP : conc st3 p = r_base r3 + X) by (apply conc_region'; exact Hr3).
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (XEND : X + strideg <= round_up_pg (r_len r3)).
  { unfold X. eapply Z.le_trans; [| exact SP3]. fold strideg.
    assert (strideg * idx + strideg <= strideg * (m_last_idx (get_meta_rec st3 g3) + 1)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    lia. }
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  assert (JR' : 0 <= ncls sc cnt1 < 48) by lia.
  assert (FRESH3 : forall o' v t, X <= o' < X + strideg - 4 -> (r_cells (get_shadow st3 (fst b3))) !! o' = Some (v, t) -> (t < s_tick st3)%N).
  { intros o' v t Ho Hc. eapply (ai_fresh _ _ _ _ _ AI'' I0 (fst b3) X (strideg - 4)); [| | exact Hc]; [| lia].
    exists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  (* [comment removed for export] *)
  rewrite (nest_model_eq st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SO_N STR3).
  replace (slot_of st3 g3 idx) with p by (unfold slot_of, slot_start'; rewrite Hmem3; reflexivity).
  cps_destruct (nt_tail_hyps st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)
    as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK).
  fold strideg X p in TMS, TREC, TREG, TP0, TP16, TPEND, TGN, TNOG, TOLD, TTK.
  set (stT := nt_stT st3 g3 b3 idx sc cnt1 mm) in *.
  assert (ACT3 : active st3 sc = None).
  { rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). exact ACT0. }
  assert (ACTT : active stT sc = None) by (unfold stT; rewrite ntT_active; exact ACT3).
  rewrite (ag_tail_kq_eq sc k bail stT mm p cnt1 (cnt1 - 1)); [| rewrite TREC; reflexivity| rewrite TREC; reflexivity| exact ACTT].
  cps_destruct (ntT_proj st3 g3 b3 idx sc cnt1 mm) as (TPR & TPG & TPA & TPT & TPN & TPRS & TPC & TPS). fold stT in TPR, TPG, TPA, TPT, TPN, TPRS, TPC, TPS.
  assert (URT : 0 <= usage stT sc < 2^60).
  { unfold stT. rewrite ntT_usage. pose proof (mf_usage _ _ MF3 sc) as U. exact U. }
  assert (TCONC : forall q, conc stT q = conc st3 q) by (intros q; unfold stT; apply ntT_conc).
  (* [comment removed for export] *)
  riprefixT. unfold rnest_regs. rewrite <- GE.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rnenf_walk st3 m'' o g3 b3 r3 idx (ncls sc cnt1) MR'' UA'' JR' HA3 MSLg MW3 GSC3 STR3 SO_N TK''); [exact CTR''| exact MI'']. }
  cbv beta. (intros ms'; cps_intros (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5 & -> & MU5 & WM5 & MI5 & MR5 & TK5)).
  fold strideg.
  (* [comment removed for export] *)
  assert (MWmm : mw_ok (get_meta_rec st3 mm)) by (rewrite G3; unfold mw_ok, meta0; cbn; lia).
  eapply evt_cut.
  { change (wz cnt1) with (Z_to_bv 64 cnt1).
    eapply (renfD_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' JR' SO_N TK''); [exact MS3| exact MWmm| exact C1R| exact MR5| exact TK5| exact MI5]. }
  cbv beta. (intros ms'; cps_intros (m6 & -> & MU6 & WM6 & MI6 & MR6 & TK6)).
  fold strideg in MU5, MU6, MR6, TK6 |- *.
  change (wr8 (fst b3, snd b3 + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192) (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g3 b3 idx)))
    with (nt_stW st3 g3 b3 idx mm) in MR6, TK6.
  (* [comment removed for export] *)
  set (P := conc st3 b3 + 16 + strideg * idx) in *.
  assert (EP : P = r_base r3 + X) by (unfold P, X; rewrite CB3; lia).
  eapply evt_cut.
  { replace (wz (size_class sc * UNIT)) with (Z_to_bv 64 (16 * szc)) by (unfold wz, szc, UNIT; f_equal; lia).
    replace (Z_to_bv 64 (P + 12)) with (Z_to_bv 64 (P + 12 + 16 * szc * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (cnt1 + 1)) with (Z_to_bv 64 (cnt1 + 1 - 0)) by (f_equal; lia).
    eapply (rzero_loop_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' STR3 SO_N (Z.to_nat (cnt1 + 1)) 0 szc cnt1 (nt_stW st3 g3 b3 idx mm) m6 m6);
      [lia| lia| unfold szc; lia| lia| unfold strideg in FITg; lia
      | apply (proj1 (ntW_proj st3 g3 b3 idx mm))| apply (proj1 (proj2 (ntW_proj st3 g3 b3 idx mm)))
      | exact MR6| exact TK6| exact MI6| apply munch_refl| apply wmono_refl]. }
  cbv beta. (intros ms'; cps_intros (m7 & -> & MU7 & WM7 & MI7 & MR7 & TK7 & RG7 & GR7 & PW7)).
  change (zero_hdrs (pp st3 g3 b3 idx) (16 * szc) 0 (Z.to_nat (cnt1 + 1)) (nt_stW st3 g3 b3 idx mm)) with stT in MR7, TK7, RG7, GR7.
  fold P in MU7, PW7.
  (* [comment removed for export] *)
  eapply evt_cut.
  { replace (Z_to_bv 64 P) with (Z_to_bv 64 (conc stT p)) by (rewrite TCONC, CP, EP; reflexivity).
    replace (Z_to_bv 64 (conc st3 mm)) with (Z_to_bv 64 (conc stT mm)) by (rewrite TCONC; reflexivity).
    eapply (rtail_walk stT sc cnt1 (cnt1 - 1) 0 mm p r3 SC C1R ltac:(lia) ltac:(lia) TMS TREC TREG Hk3 TP0 TP16 TPEND TGN TNOG TOLD URT ACTT TK7);
      [exact MR7| exact MI7]. }
  cbv beta. (intros ms'; cps_intros (s0x & a1x & a2y & a3x & a4z & m8 & -> & MU8 & WM8 & MI8 & MR8 & TK8)).
  (* [comment removed for export] *)
  set (W58 := ([(P - 3, P); (conc st3 mm, conc st3 mm + 40); (P - 3, P - 2); (P + 12, P + 12 + 16 * szc * cnt1 + 1)]%Z ++ rtailW stT sc mm p)).
  assert (LOWW : Forall (fun iv : Z * Z => snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x66000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928))) W58).
  { apply Forall_forall. intros [lo' hi'] HI. cbn [fst snd]. unfold W58, rtailW in HI. rewrite !TCONC, CP in HI. cbn [app In] in HI.
    pose proof (round_up_pg_ge (r_len r3)).
    destruct HI as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; inversion E; subst; unfold RCTX; lia. }
  assert (MU58 : munch W58 m'' m8).
  { intros x Hx. unfold W58 in Hx. rewrite outside_app' in Hx. destruct Hx as [H4x H8].
    rewrite (MU8 x H8). cbn [outside] in H4x. cps_destruct H4x as (H5 & H6a & H6b & H7 & _).
    rewrite (MU7 x) by (cbn; auto). rewrite (MU6 x) by (cbn; auto). rewrite (MU5 x) by (cbn; auto). reflexivity. }
  assert (WM58 : wmono rsegs m'' m8).
  { eapply wmono_trans; [exact WM5|]. eapply wmono_trans; [exact WM6|]. eapply wmono_trans; [exact WM7| exact WM8]. }
  assert (DJhigh : forall A n, alloc_ceiling <= A -> disjoint_from W58 A n).
  { intros A n HA. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [H _]. lia. }
  assert (DJimg : forall A n, 0x10000 <= A -> A + n <= 0x66000 -> (A + n <= RCTX \/ RCTX + 928 <= A) -> disjoint_from W58 A n).
  { intros A n H1 H2 H3. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [_ H]. unfold RCTX in *. first [ solve [clear - AR IS H1 H2 H3 H; lia] | lia ]. }
  assert (FR8 : rw_cells rsegs m8 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact FR''. }
  assert (ST8 : stk rsegs m8 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR8 : rw_cells rsegs m8 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU58| exact WM58|]. rewrite EA. apply DJimg; [lia| cbn; lia| unfold RCTX; cbn; lia]. }
  set (stF := st_model stT sc cnt1 (cnt1 - 1) mm p).
  assert (MRF : rmrep stF m8) by (exact (rmrep_st_model stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 m8 MR8)).
  eapply evt_cut. { unfold rFRM in FR8. eapply (ras_ret0 sp gp tp); [exact MRF| exact MI8| exact FR8| exact ST8| exact CLO| lia]. }
  cbv beta. (intros ms'; cps_intros (a1w & a2w & -> & ST9)). apply evt_done.
  apply HK.
  (* [comment removed for export] *)
  fold strideg in MU7, PW7. fold P in MU7, PW7.
  cps_destruct (smg_proj stT sc cnt1 (cnt1 - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10).
  fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
  rewrite TPR in PF1. rewrite TPA in PF4. rewrite TPT in PF5. rewrite TPN in PF6. rewrite TPRS in PF7.
  assert (CTXT : ctx stT = ctx st3) by (unfold stT; apply ntT_ctx).
  rewrite CTXT in PF8, PF9, PF10.
  assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK8]; reflexivity).
  assert (MSF : meta_slot stF mm) by (apply (proj1 (smg_meta_slot stT sc cnt1 (cnt1 - 1) mm p mm)); exact TMS).
  assert (CF : forall q, conc stF q = conc st3 q) by (intros q; unfold stF; rewrite (smg_conc stT sc cnt1 (cnt1 - 1) mm p q); apply TCONC).
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR'' as (WF3 & _). cps_pose WF3 as (RS0 & WR3 & DJ3 & _).
  assert (STRF : get_stride (get_meta_rec stF mm) = 16 * szc) by (exact (ntF_stride st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)).
  (* [comment removed for export] *)
  assert (HOLD2 : forall q rq, (s_regions st2) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. cps_destruct (mrel_regions _ _ MREL'' q rq Hq) as (r' & Hr' & K' & B' & L'). exists r'. rewrite PF1. auto. }
  assert (HOLD3 : forall q rq, (s_regions st3) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. exists rq. rewrite PF1. repeat split; auto. lia. }
  assert (INSPAN : forall a, r_base r3 + X - 4 <= a < r_base r3 + X + strideg - 4 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3). apply SPAN3. unfold X in Ha. lia. }
  assert (INMETA : forall a, conc st3 mm <= a < conc st3 mm + 40 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. left. do 3 right. cps_destruct (rmeta_chunk_facts stF m8 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
    exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite CF in L0, H0'. lia. }
  assert (INCTX : forall a, RCTX <= a < RCTX + 928 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a) by (intros a Ha; left; right; right; left; exact Ha).
  (* [comment removed for export] *)
  assert (HDR0N : cell_read (get_shadow st3 (fst b3)) (X + strideg - 4) = Known 0).
  { pose proof (mf_hdr0 _ _ MF3 g3 b3 (idx + 1) Hmem3 ltac:(lia)) as H.
    unfold sstart_of in H. rewrite Hmem3 in H. cbn [default from_option id snd] in H. fold strideg in H. unfold IB, UNIT in H.
    replace (X + strideg - 4) with (snd b3 + 16 + strideg * (idx + 1) - 4) by (unfold X; lia). exact H. }
  assert (M6A : m6 (wa (r_base r3 + (X + strideg - 4))) = Some (b8 0)).
  { apply (rregion_byte_raw (nt_stW st3 g3 b3 idx mm) m6 (fst b3) r3 (X + strideg - 4) 0 MR6).
    - rewrite (proj1 (ntW_proj st3 g3 b3 idx mm)). exact Hr3.
    - exact Hk3.
    - lia.
    - rewrite (ntW_cell_read_other st3 g3 b3 idx (ncls sc cnt1) sc mm SC JR' (X + strideg - 4)) by (unfold X; lia). exact HDR0N. }
  assert (PE67 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m6 m7).
  { intros a Ha NC. split; [| intros W; apply WM7; exact W].
    destruct (arith_prog_dec a (P + 12) (16 * szc) cnt1 ltac:(lia)) as [(j & Hj & Ea)|NA].
    - destruct (Z_lt_le_dec a (P + strideg - 4)) as [LT|GE'].
      + exfalso. apply NC. apply INSPAN. lia.
      + assert (J16 : 16 * szc * j <= 16 * szc * cnt1) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (Ea' : a = r_base r3 + (X + strideg - 4)) by lia.
        rewrite Ea', M6A.
        apply (rregion_byte_raw stT m7 (fst b3) r3 (X + strideg - 4) 0 MR7); [rewrite TPR; exact Hr3| exact Hk3| lia|].
        assert (EJ : 16 * szc * j = 16 * szc * cnt1) by lia.
        replace (X + strideg - 4) with (X + 12 + cnt1 * (16 * szc)) by lia.
        unfold stT. apply (ntT_cell_read_zero st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R TK''). lia.
    - apply PW7. rewrite wa_unsigned by lia. intros j Hj. specialize (NA j Hj). lia. }
  assert (PE08 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m8).
  { eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE04|]. intros a Ha. exact (rmalloc_fp_mono st0 st2 stF lo (bv_unsigned sp) a HOLD2 Ha). }
    eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE''|]. intros a Ha. exact (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3 Ha). }
    eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU5| exact WM5|]. intros a Ha NC. cbn. split; [|exact I]. intros Xa; apply NC. apply INSPAN. lia. }
    eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros Xa; apply NC; [apply INMETA; lia| apply INSPAN; lia]. }
    eapply rpres_except_trans. { exact PE67. }
    eapply rpres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. unfold rtailW. rewrite !TCONC, CP. cbn.
    split; [|split; [|split; [|split; [|exact I]]]]; intros Xa; apply NC; [apply INCTX; unfold RCTX in *; lia| apply INMETA; lia| apply INSPAN; lia| apply INCTX; unfold RCTX in *; lia]. }
  (* [comment removed for export] *)
  assert (UAF : unk_agree stF o m8).
  { intros rid rr off h Hrr Kr Ho Hc NG. rewrite PF1 in Hrr.
    cps_destruct (WR3 _ _ Hrr) as (R0 & _ & _ & RCr & _). bz_ceil.
    cps_destruct (rregion_facts st3 m'' rid rr MR'' Hrr) as (_ & _ & _ & RI1r & RI2r). specialize (RI1r ltac:(lia)). specialize (RI2r ltac:(lia)).
    cps_destruct (rmeta_chunk_facts st3 m'' mm MR'' MS3) as (_ & _ & _ & _ & _ & GRG & _). pose proof (GRG rid rr Hrr Kr) as GRr.
    assert (NG3 : ~ grp_hdr_cov st3 rid off).
    { intros CV. apply NG. unfold stF. apply (smg_grp_hdr_cov_old stT sc cnt1 (cnt1 - 1) mm p TP0 rid off TGN).
      eapply rgrp_hdr_cov_same; [exact TPG| exact CV]. }
    destruct (N.eq_dec rid (fst b3)) as [->|NE].
    - rewrite Hr3 in Hrr. inversion Hrr; subst rr.
      destruct (ntF_unknown st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N TK'' off h ltac:(lia) Hc) as [CV|(Hc3 & NH & NZ)].
      { exfalso. apply NG. exact CV. }
      rewrite <- (UA'' (fst b3) r3 off h Hr3 Kr Ho Hc3 NG3).
      assert (NHC : ~ (X <= off < X + 12)).
      { intros Hx. apply NG. unfold stF. change (fst b3) with (fst p). apply (smg_grp_hdr_cov stT sc cnt1 (cnt1 - 1) mm p SC). unfold p. cbn [snd]. lia. }
      transitivity (m7 (wa (r_base r3 + off))). { apply MU8. rewrite wa_unsigned by lia. unfold rtailW. rewrite !TCONC, CP. cbn. unfold RCTX. first [ solve [clear - AR IS SC RI2 Ho GRr NHC; lia] | lia ]. }
      transitivity (m6 (wa (r_base r3 + off))). { apply PW7. rewrite wa_unsigned by lia. intros j Hj E. apply NZ. exists j. split; [exact Hj|]. lia. }
      transitivity (m5 (wa (r_base r3 + off))). { apply MU6. rewrite wa_unsigned by lia. cbn. first [ solve [clear - AR IS CB3 Ho GRr NH; lia] | lia ]. }
      apply MU5. rewrite wa_unsigned by lia. cbn. first [ solve [clear - AR IS CB3 NH; lia] | lia ].
    - assert (Hc3 : cell_read (get_shadow st3 rid) off = Unknown h).
      { rewrite <- (ntF_shadow_other st3 g3 b3 idx sc cnt1 mm rid NE). exact Hc. }
      rewrite <- (UA'' rid rr off h Hrr Kr Ho Hc3 NG3).
      pose proof (lr_lo_group rr Kr) as LR1. pose proof (lr_lo_group r3 Hk3) as LR2.
      assert (NE' : fst b3 <> rid) by (intros E; apply NE; symmetry; exact E).
      pose proof (round_up_pg_ge (r_len r3)) as RU0.
      destruct (DJ3 _ _ _ _ Hr3 Hrr NE') as [D|D].
      all: transitivity (m7 (wa (r_base rr + off))); [apply MU8; rewrite wa_unsigned by (first [ solve [clear - AR IS SC RQ FIT C1R ENR FIT3 XEND Ho RI2r GRr LR1 D B30 SK LR2; lia] | lia ]); unfold rtailW; rewrite !TCONC, CP; cbn [outside]; unfold RCTX; (first [ solve [clear - AR IS SC RQ FIT C1R ENR FIT3 XEND Ho RI2r GRr LR1 D B30 SK LR2; lia] | lia ])|].
      all: transitivity (m6 (wa (r_base rr + off))); [apply MU7; rewrite wa_unsigned by lia; cbn [outside]; lia|].
      all: transitivity (m5 (wa (r_base rr + off))); [apply MU6; rewrite wa_unsigned by (first [ solve [clear - AR IS RQ FIT C1R ENR FIT3 CB3 XEND Ho GRr LR1 D B30 SK LR2; lia] | lia ]); cbn [outside]; (first [ solve [clear - AR IS RQ FIT C1R ENR FIT3 CB3 XEND Ho GRr LR1 D B30 SK LR2; lia] | lia ])|].
      all: apply MU5; rewrite wa_unsigned by lia; cbn [outside]; lia. }
  assert (RSP3 : ret_span st3 (ncls sc cnt1) idx (fst b3) X (strideg - 4)).
  { exists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  unfold ras_post2.
  do 14 eexists. exists m8, errv''. split; [reflexivity|].
  split; [exact MI8|]. split; [exact ST9|]. split; [exact ERR8|].
  split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m8); [exact MRF| exact AUX| exact PE08| exact CLO| lia]|].
  split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE08|].
  split. { split.
    - intros q rq Hq. rewrite <- REG1 in Hq. cps_destruct (amr_regions _ _ _ REL q rq Hq) as (r' & H' & K' & B' & L' & _).
      cps_destruct (HOLD2 q r' H') as (r'' & H'' & K'' & B'' & L''). exists r''. split; [exact H''|]. split; [rewrite K''; exact K'|]. split; [rewrite B''; exact B'|]. lia.
    - rewrite PF6. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
    - rewrite PF7, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
  split. { unfold brk_link_ps in BL'' |- *. rewrite PF8. destruct (c_brk (ctx st3)) as [| |brid boff]; auto. rewrite CF. exact BL''. }
  split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
  split. { constructor.
    - intros c' Hc'. unfold stF. rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p c'). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold stT. rewrite ntT_active. rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
    - intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
    - rewrite PF5, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
    - intros _ rid' S len RSP o' v t Ho Hc.
      cps_destruct (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) as (-> & -> & ->).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho.
      unfold p in Hc, Ho. cbn [fst snd] in Hc, Ho. rewrite PF5.
      unfold stF, stT, p in Hc. rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') in Hc by (fold szc; lia).
      eapply FRESH3; [| exact Hc]. lia.
    - intros E0 _ rid' S len RSP o' Ho.
      cps_destruct (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) as (-> & -> & ->).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho. unfold p in Ho. cbn [snd] in Ho.
      cps_destruct (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 o' ltac:(lia)) as (V1 & V2 & V3).
      unfold p. cbn [fst]. unfold stF, stT, p. split; [| split].
      + rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') by (fold szc; lia). exact V1.
      + rewrite (ntF_span_hav st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' SO_N o') by lia. exact V2.
      + rewrite (ntF_havp st3 g3 b3 idx sc cnt1 mm). exact V3. }
  split. { rewrite PF9. exact CTR''. }
  right. split; [lia|]. exists mm, p, r3.
  split; [unfold stF; rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p sc), Z.eqb_refl; reflexivity|].
  split; [unfold stF, stT, p, X; apply (nt_slot_ok st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N STR3 ltac:(fold szc; lia) G3 MS3 TK'' FRESH3 req); lia|].
  rewrite STRF. unfold p. cbn [fst snd]. split.
  + intros a Ha. apply INSPAN. lia.
  + intros E0. replace (X + (16 + 16 * szc * 0) + -3) with (X + 13) by lia.
    cps_destruct (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 (X + 13) ltac:(lia)) as (V1 & V2 & V3).
    unfold stF, stT. apply (ntF_rdv13 st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N o V1 V2 V3).
Qed.
End LEVEL.

End ACeilS1.
