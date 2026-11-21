(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W9.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require RMallocRep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require RMallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM21.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require RMallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM22.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM02.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM03.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require RASlot_W2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require RASlot_W4.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM05.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM20.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_M5F.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import F_malloc_entry. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W9. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06. Import MM06. Import MM06.ASlot_W18. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01. Import MM01. Import MM01.ASlot_M0. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM02. Import MM02. Import MM02.ASlot_M5D.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RASlot_W2. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RASlot_W4. Import PM14. Import PM14.RASlot_W18. Import PM15. Import PM15.RASlot_W19. Import PM03.RASlot_M0. Import PM05. Import PM05.RASlot_M2. Import PM08. Import PM08.RASlot_M5D.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01. Import MM01.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rlowW (spv : Z) (iv : Z * Z) : Prop :=
  (0 <= fst iv /\ snd iv <= ATOP /\ (snd iv <= 0x10000 \/ 0x51000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928)))
  \/ iv = (spv - 144, spv).

Lemma rlowW_meta spv st m' q : rmrep st m' -> meta_slot st q -> rlowW spv (conc st q, conc st q + 40).
Proof.
  intros MR MS. destruct (rmeta_slot_bounds st m' q MR MS) as (Gpos & GC & GI & _). left. atop_facts. cbn [fst snd]. lia.
Qed.

Definition rmetaW (spv : Z) (st : mstate) (iv : Z * Z) : Prop :=
  (exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (RCTX + 16, RCTX + 24) \/ iv = (spv - 144, spv).

Lemma rfailW_shape st mt spv :
  meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (rmetaW spv st) (rfailW st mt spv).
Proof.
  intros MS FL. unfold rfailW.
  constructor; [right; right; reflexivity|].
  constructor; [left; exists mt; auto|].
  constructor; [right; left; reflexivity|].
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; [|constructor].
  destruct (FL h eq_refl) as [MSh FP].
  constructor; [left; exists h; auto|].
  destruct (m_prev (get_meta_rec st h)) as [p|] eqn:HP; [|constructor].
  constructor; [left; exists p; auto| constructor].
Qed.

Lemma rfailW_low st mt m' spv :
  rmrep st m' -> meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (rlowW spv) (rfailW st mt spv).
Proof.
  intros MR MS FL. eapply Forall_impl; [| exact (rfailW_shape st mt spv MS FL)].
  intros [lo hi] [(q & MSq & E1 & E2)|[E|E]]; [cbn in E1, E2; subst; eapply rlowW_meta; eassumption| inversion E; subst; left; unfold RCTX; cbn; lia| inversion E; subst; right; reflexivity].
Qed.

Lemma rlowW_disjoint spv W a n : Forall (rlowW spv) W -> ATOP <= a -> (a + n <= spv - 144 \/ spv <= a) -> disjoint_from W a n.
Proof. intros FW Ha Hs. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(H1 & H2 & H3)|E]; [cbn in *; lia| inversion E; subst; lia]. Qed.

Lemma rlowW_disjoint_img spv W a n : Forall (rlowW spv) W -> 0x10000 <= a -> a + n <= 0x51000 -> (a + n <= RCTX \/ RCTX + 928 <= a) ->
  ATOP <= spv - 144 -> disjoint_from W a n.
Proof. intros FW H1 H2 H3 H4. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(X1 & X2 & X3)|E]; [cbn in *; atop_facts; lia| inversion E; subst; atop_facts; lia]. Qed.

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
Hypothesis ST : stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp).
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rnfail_ok : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof.
  intros st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC.
  destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. atop_facts.
  pose proof (rerrno_lit5 tp TP) as EA.
  destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), (-1); split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 (-1) AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  pose proof (rmeta_slot_bounds st2 m4 mm MR4 MSL) as (Gpos & GC & GI & _).
  pose proof (lf_freelist _ (isf_lf _ _ F3)) as FFL. change (fact_freelist (strip st3)) with (fact_freelist st3) in FFL.
  assert (FL : forall h, c_free_meta_head (ctx st3) = Some h ->
            meta_slot st3 h /\ h <> mm /\ exists p, m_prev (get_meta_rec st3 h) = Some p /\ meta_slot st3 p /\ p <> mm).
  { intros h Hh. destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp). destruct (NFL h Hh) as [NE1 NE2].
    change (meta_slot (strip st3) h) in MSh. change (get_meta_rec (strip st3) h) with (get_meta_rec st3 h) in MEMh, NXh, HP.
    change (meta_slot (strip st3) p) in MSp.
    split; [exact MSh|]. split; [exact NE1|]. exists p. split; [exact HP|]. split; [exact MSp|]. intros ->. apply NE2. exact HP. }
  rewrite as_free_meta_eq. cbn [as_kq].
  riprefixT. unfold rnest_regs.
  eapply evt_cut.
  { rewrite <- GE. unfold rFRM in FR''. replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) in FR'' by lia.
    eapply (rfailm1_walk st3 mm MS3 FL); [exact MR''| exact MI''| exact FR''| lia]. }
  cbv beta. intros ms' (a1x & s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7).
  assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW st3 mm (bv_unsigned sp))).
  { eapply (rfailW_low st3 mm m'' _ MR'' MS3). intros h Hh. destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _).
    split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
  assert (ST7 : stk (run_segments psegs rc_inp rc_sp rc_mb) m7 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]].
    replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR7 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m7 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
  eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
  cbv beta. intros ms' (a1y & a2y & -> & ST8). apply evt_done.
  set (stF := as_fm_st st3 mm) in *.
  destruct (fm_proj st3 mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (FS : Forall (rmetaW (bv_unsigned sp) st3) (rfailW st3 mm (bv_unsigned sp))).
  { apply (rfailW_shape st3 mm _ MS3). intros h Hh; destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
  assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
  { eapply rpres_except_trans.
    - eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr.
      destruct (mrel_regions _ _ MREL'' rid r Hr) as (r' & Hr' & K' & B' & L'). exists r'. rewrite PF1. auto.
    - eapply rpres_except_trans.
      + eapply rpres_except_mono; [exact PE''|]. intros a Ha. eapply (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia)); [| exact Ha].
        intros rid r Hr. exists r. rewrite PF1. repeat split; auto. lia.
      + eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
        intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
        * cbn in E1, E2. subst lo' hi'. left. do 3 right.
          assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
          destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
          exists rid0, r0. split; [exact H0|]. split; [exact K0|].
          assert (EC : conc stF q = conc st3 q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
        * inversion E; subst. left. right. right. left. unfold RCTX in *. atop_facts. lia.
        * inversion E; subst. left. left. lia. }
  apply HK. unfold ras_post2.
  do 14 eexists. exists m7, errv''. split; [reflexivity|].
  split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
  split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
  split; [exact MR7|].
  split; [eapply ticks_ok_same; [rewrite PF2; reflexivity| rewrite PF6; reflexivity| exact TK'']|].
  split. { eapply (unk_agree_xfer o st3 m'' stF m7 UA'').
    - exact PF2.
    - intros rid r Hk Hr. rewrite PF1 in Hr. exact Hr.
    - intros b. rewrite PF3. tauto.
    - intros rid r off h Hr Hk Ho Hc NG.
      pose proof MR'' as (WF3 & _). pose proof WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). atop_facts.
      destruct (rregion_facts st3 m'' rid r MR'' Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
      pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
      + cbn in E1, E2. subst lo' hi'.
        destruct (rmeta_chunk_facts st3 m'' q MR'' MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
      + inversion E; subst. unfold RCTX in Ha. lia.
      + inversion E; subst. lia. }
  split; [exact PE07|].
  split. { split.
    - intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _).
      destruct (mrel_regions _ _ MREL'' rid r' H') as (r'' & H'' & K'' & B'' & L''). exists r''. rewrite PF1. repeat split; auto; [congruence| congruence| lia].
    - rewrite PF7. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
    - rewrite PF8, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
  split. { unfold brk_link_ps in BL'' |- *. rewrite PF11. destruct (c_brk (ctx st3)) as [| |brid boff]; auto.
           unfold conc, get_region. rewrite PF1. exact BL''. }
  split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
  split. { constructor.
    - intros c' Hc'. rewrite PF9, (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
    - intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
    - rewrite PF6, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
    - intros H; exfalso; lia.
    - intros _ H; exfalso; lia. }
  split; [rewrite PF12; exact CTR''|].
  left. reflexivity.
Qed.
End LEVEL.
End CANSEC1.
End RASlot_M5F.

Module RF_ntf_G.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM21. Import PM21.RF_get_meta. Import PM20. Import PM20.RF_ntf_A. Import PM10. Import PM10.RF_ntf_E.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x16430) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x161a8) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -96)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

Lemma rntf_nest_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g p base1 g1 : aptr) (ghp gh1 : ghdr) (ar1 : area) (b3 lo8 hi8 off16 lo : Z),
  let mr := get_meta_rec st g in
  let mr1 := get_meta_rec st g1 in
  let idx1 := Z.land b3 31 in
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g -> mw_ok mr -> m_maplen mr = 0 -> m_mem mr = Some p ->
  (s_groups st) !! p = Some ghp ->
  (forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p - 4) [b8 0; b8 b3; b8 lo8; b8 hi8] ->
  0 <= b3 < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> off16 = lo8 + 256 * hi8 ->
  base1 = aadd p (- (UNIT * off16) - UNIT) ->
  (s_groups st) !! base1 = Some gh1 -> g_meta gh1 = Some g1 -> meta_slot st g1 -> m_mem mr1 = Some base1 ->
  0 <= m_avail mr1 < 2^32 -> 0 <= m_freed mr1 < 2^32 -> 0 <= m_last_idx mr1 < 32 -> 0 <= m_freeable mr1 < 2 ->
  0 <= m_sizeclass mr1 < 64 -> 0 <= m_maplen mr1 < 2^40 ->
  (s_areas st) !! (area_of g1) = Some ar1 -> a_check ar1 = c_secret (ctx st) -> 0 <= c_secret (ctx st) < 2^64 ->
  c_init_done (ctx st) = 1 ->
  idx1 <= m_last_idx mr1 -> Z.testbit (m_avail mr1) idx1 = false -> Z.testbit (m_freed mr1) idx1 = false ->
  (m_sizeclass mr1 < 48 -> size_class (m_sizeclass mr1) * idx1 <= off16 < size_class (m_sizeclass mr1) * (idx1 + 1)) ->
  (48 <= m_sizeclass mr1 -> m_sizeclass mr1 = 63) ->
  (m_maplen mr1 <> 0 -> off16 <= m_maplen mr1 * 256 - 1) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rnest_call_post sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (grp_del st g p) g p (conc st g1) idx1 fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16404) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
         AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC HID Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1. pose proof sec_range as SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_maplen _ MW) as M12.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
  pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).
  destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
  assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
  { rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
  rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
  pose proof MS1 as (a & ara & k & Ha & Hkk & Eg).
  destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
  destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
  assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  assert (Hao : area_of g1 = a).
  { rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
  assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
  { rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
  assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
  unfold RCTX, AREA_HDR, META_SIZE, NSLOTS in *. atop_facts.
  assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.
  change (frozen (conc st p mod 16 = 0)) in P16m.
  change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
  clear HGm AAL RBAL RgBAL SpA BbA.
  destruct GB as (GB0 & GB1 & GB2 & _). destruct G1B as (G1B0 & G1B1 & G1B2 & _).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
  rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
    pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
    pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
    pose proof (rmrep_ctx_secret_read st mX MR) as RC;
    pose proof (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
    pose proof (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
    pose proof (bytes_at_read (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
  end.
  rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
  unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
  rewrite Hao, (conc_region' st a rg Hrg) in RA. unfold RCTX in RC. unfold rsecw in RC. rewrite HID, Z.mul_1_r in RC.
  change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
  change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
  change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
  replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
  replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
  replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
  rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.
  st1.
  eapply evt_cut.
  { eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
            (m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
            (m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) SECRET).
    all: lazymatch goal with
         | |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
         | |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
         | |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
         | |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
         | |- ov_read_bytes _ _ (wa 327176) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
         | |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
         | |- rw_cells _ _ (conc _ _) _ => exact MM
         | |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
         | |- _ => idtac
         end.
    all: clear - Cp Sp0 Sp1 RB0 RBC P16m Bb0 HBc HAeq G1B0 G1B1 B3 LO8 HI8 O16 AV1 FR1 SECR LI1 FB1 SC1 ML1 Hidx Hav Hfr Hsc Hsc63 Hml;
         first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
               | lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }
  intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
  replace (ret_pc (Z_to_bv 64 0x1641c)) with (Z_to_bv 64 0x1641c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  st1.
  unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
  st1.
  clear CH MM RG RA RC R4 R2.
  pose proof MR as (_ & _ & _ & _ & GR0 & _). destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rw_cells_store_ok_at (run_segments psegs rc_inp rc_sp rc_mb) mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
  clear RWp.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) MR Hp UNK (length_le8 _)) as MR2
  end.
  rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
  apply (rmrep_grp_del_eq st _ g p) in MR2.
  st1. st1.
  apply evt_done. unfold rnest_call_post. do 14 eexists.
  split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
           cbv delta [mkR]. unfold RCTX. reflexivity. }
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + eapply rfree_fp_group; [exact Hp | lia]. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.

Lemma rntf_nest_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) (st0 st : mstate) (g : aptr) (lo : Z),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> meta_slot st g -> fm_facts st g ->
  conc st g = conc st0 g ->
  s1 = Z_to_bv 64 RSSP_GUARD ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a0 a1)
      (MS (mkR (Z_to_bv 64 0x16430) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st0 g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16430) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  atop_facts.
  st1. st1. st1.
  rewrite <- Hcg.
  eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
    first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | atop_facts; lia].
Qed.
End CANSEC1.
End RF_ntf_G.
