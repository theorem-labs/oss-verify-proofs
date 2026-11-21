(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
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
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W9.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM21.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM22.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM02.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM03.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM05.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RF_enframe.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM18.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM20.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM14.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RASlot_W2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RASlot_W4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_M1.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W9. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01. Import MM01. Import MM01.ASlot_M0. Import MM01.ASlot_M1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. Import PM05. Import PM05.RASlot_W9. Import PM03.RASlot_M0.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01. Import MM01.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : RISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

Lemma rta_slot_ok : exists b r,
  m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ slot_ok st' g b r k req
  /\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
  /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
               < r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
        free_slot_addr st0 a).
Proof.
  pose proof (isf_mf _ _ F) as MF.
  pose proof (gmf_cls _ _ _ GM) as GSC.
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
  assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
  assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
  assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
  { rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }
  assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| exact LBK]).
  assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
  { apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  destruct (FM g b Hmem) as (FM1 & FM2 & _).
  assert (KLI : k <= m_last_idx (get_meta_rec st g)).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
    cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
  assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; exact TBst])) as FC.
  cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
  { pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
    exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
  pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
  pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
  unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
  destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
  assert (P2k : 0 < 2 ^ k <= msk).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE'). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. exact LE'. }
  exists b, r.
  split; [exact Hmem|]. split; [exact Hr|].
  split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); exact Hr|]. split; [exact Hk|].
  split; [| split; [exact ST'|]].
  - pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4).
    assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; exact ST').
    constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      rewrite ?ST2; fold mr; rewrite ?EM, ?EL, ?EF, ?ES, ?EP, ?STX.
    + exact Hmem.
    + unfold st'. cbn. rewrite (tr_regions _ _ _ TR). exact Hr.
    + exact Hk.
    + exact B0.
    + exact B16.
    + lia.
    + lia.
    + exact SPAN.
    + unfold UNIT in S16. lia.
    + unfold UNIT in SMOD. exact SMOD.
    + lia.
    + exact RQ.
    + lia.
    + intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
      destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _). exact (NOGRP b' gh1 Hb1 Hf').
    + unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). exact K4.
    + intros off O0 OF.
      assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
      assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
    + unfold st'. cbn. rewrite (tr_slots _ _ _ TR). exact SSL.
    + unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSL]. apply (tr_areas _ _ _ TR).
    + unfold msk, mr in *. lia.
    + unfold mr. lia.
    + lia.
    + lia.
    + left. lia.
  - intros a Ha. rewrite ST' in Ha.
    destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
    assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; exact Hmem).
    destruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
    exists g, b, r, k. split; [exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); exact Hr|]. split; [exact Hk|]. split; [lia|].
    split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
    + pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; exact TB0].
    + assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
        by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
      assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
      lia.
Qed.
End TASLOT.

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

Lemma rerrno_lit : errno_addr tp = 0x72edc.
Proof. subst tp. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rhk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' -> stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m' ->
  rimplT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
  unfold as_k. replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
  cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
  pose proof rerrno_lit as EA. pose proof (RAS_STACK_ge sc) as ASG.
  pose proof (isf_mf _ _ F0) as MF.
  set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
  subst msk.
  destruct (rta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
    as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA).
  fold st' in Hr', SO, STR, FSA.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
  assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).
  assert (FPC : forall a, rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 st' lo (bv_unsigned sp) a).
  { intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - left. left. exact X.
    - left. right. right. left. exact X.
    - left. do 3 right. destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
      exists rid0, r0. rewrite REGX. split; [exact H0|]. split; [exact K0|]. lia.
    - do 3 right. left. destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct ER as [_ EG EGR _ _ _ _ _].
      destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
      exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
      pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
  assert (PE' : rpres_except (rmalloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply rpres_except_mono; [exact PE| exact FPC]).
  assert (NIMG : forall a, 0x10000 <= a < 0x94000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a).
  { intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - atop_facts. lia.
    - exact (Hc X).
    - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
    - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _). destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
      pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
  apply HK. unfold ras_post2.
  exists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
  split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| unfold RCTX; lia]. }
  split. { eapply rauxv_ok_pres; [exact AUX| exact PE| |].
           - intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
             + lia. + unfold RCTX in X. atop_facts. lia.
             + destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). atop_facts. lia.
             + destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). atop_facts. lia.
           - intros a Ha. apply NIMG; unfold RAUXV_CELL, RCTX in *; lia. }
  split; [exact MR'|].
  split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
  split. {
    intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
    assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
    { revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
    assert (NG0 : ~ grp_hdr_cov st rid off).
    { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
      destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
    rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
    refine (proj1 (PE (r_base rr + off) _ _)).
    { destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). atop_facts. lia. }
    intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). lia.
    - destruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
    - destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid rr Hrr Kr); lia.
    - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct (N.eq_dec (fst bq) rid) as [E|NE].
      + apply NG0. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
      + pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
  split; [exact PE'|].
  split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
           intros rid rr Hrr. exists rr. rewrite REGX. repeat split; auto. lia. }
  split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
           unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. exact BL. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { constructor.
    - intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
    - intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). exact Ha.
    - unfold st'. cbn. apply (tr_tick _ _ _ TR).
    - intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
      unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
      destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
      exact (AC rid sh o' v t Esh Hc).
    - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate. }
  split. { unfold st', ctx. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
           pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
  right. split; [lia|]. exists g3, b, r.
  split; [unfold st'; rewrite active_upd_meta; exact HA|]. split; [exact SO|]. split.
  - intros a Ha. do 2 right. left. apply FSA. exact Ha.
  - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed.
End LEVEL.
End CANSEC1.
End RASlot_M1.

Module RASlot_W17.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import F_malloc_entry. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM01. Import MM01. Import MM01.ASlot_W17.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM21.RF_mm_syscalls. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RF_enframe. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. Import PM18. Import PM18.RMallocKit_A3. Import PM20. Import PM20.RF_ntf_A. Import PM14. Import PM14.RF_malloc_bigw. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RASlot_W2. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RASlot_W4.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rmm_call_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x1a7cc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) s3 (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                   (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a7ac) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros. unfold rmmap_entry.
  step. step. step. step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

Lemma rmm_ret_fail_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1a8f4) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a7cc) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  apply evt_done. reflexivity.
Qed.

Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= ATOP.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

Lemma rmm_ret_ok_walk :
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) F fc m,
  rmrep st2 m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1a824) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ munch [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
      /\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a7cc) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until m. intros MR MI.
  pose proof (munch_refl [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold RCTX, RMLOCK in *. atop_facts.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
  clear K.
  step.
  rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
  rmeta_open G MUa WMa.
  step.
  step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
  step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
  rewrite (divu_word 4080 size) by lia.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
  set (d := 4080 / size) in *.
  pose proof MR as (_ & (CX1 & _) & _). unfold rctx_head_cells, rsecw in CX1. rewrite HC in CX1. unfold RCTX in CX1.
  step. rewrite (sx32_wz_sxv c) by lia.
  step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
  step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).
  assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
  { unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
    change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia. }
  step.
  lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
    [ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
    | clear MUa WMa H ] end.
  set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.
  pose proof (rw_cells_store_ok_at (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (602744 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
  clear CX1.
  st1.
  rewrite le4_swrap_succ by lia.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold RCTX in MR4 end.
  clear MR3.
  rraw_store_finish0 (602752 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
  assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
  { unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
  rewrite <- E4 in MR4.
  assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 602744) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1a824) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ munch [(G, G + 40); (602752 + 12, 602752 + 16)]%Z m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
      /\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 602744) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a810) fc None mX (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))) end.
  { intros a2v mn Hmn ->.
    assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).
    step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
    replace (cnt + -1) with (cnt - 1) by lia.
    assert (AI : mm_ai cnt size = (if mn =? 0 then 0 else mn - 1)).
    { unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
      destruct (Z.ltb_spec cnt d) as [LT|GE].
      - replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
        destruct (Z.eqb_spec d 0) as [E0|NE0].
        + rewrite E0. reflexivity.
        + replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
                  = Z_to_bv 64 (mm_ai cnt size)).
    { rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
      destruct (Z.eqb_spec mn 0) as [E0|NE0].
      - rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
      - rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
        change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
        destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    rewrite EA2.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR4| exact C4']. }
  if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
  -
    eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  -
    step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End MMOK.
End CANSEC1.
End RASlot_W17.
