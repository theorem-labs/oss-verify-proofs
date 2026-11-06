(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W9.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_M5D.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RASlot_M3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RASlot_M0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module RASlot_M1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M0.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
(* [comment removed for export] *)
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
Proof using LBK. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

Lemma rta_slot_ok : exists b r,
  m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ slot_ok st' g b r k req
  /\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
  /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
               < r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
        free_slot_addr st0 a).
Proof using ER F FIT GM K0 LBK MSK RQ SC TR.
  pose proof (isf_mf _ _ F) as MF.
  pose proof (gmf_cls _ _ _ GM) as GSC.
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  (* [comment removed for export] *)
  destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
  assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
  assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
  assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
  { rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }
  (* [comment removed for export] *)
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
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rerrno_lit : errno_addr tp = 0x337ec.
Proof using ERR HK TP. subst tp. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rhk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m' ->
  rimplT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom psegs)).
Proof using AC AUX BL CLO ER ERR F0 FIT HK LO MR RQ SC TK TP UA.
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
  (* [comment removed for export] *)
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
  assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (NIMG : forall a, 0x10000 <= a < 0x55000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a).
  { intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - unfold alloc_ceiling in CLO. lia.
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
             + lia. + unfold RCTX in X. unfold alloc_ceiling in CLO. lia.
             + destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). unfold alloc_ceiling in CLO. lia.
             + destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in *. lia.
           - intros a Ha. apply NIMG; unfold RAUXV_CELL, RCTX in *; lia. }
  split; [exact MR'|].
  split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
  split. { (* [comment removed for export] *)
    intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
    assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
    { revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
    assert (NG0 : ~ grp_hdr_cov st rid off).
    { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
      destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
    rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
    refine (proj1 (PE (r_base rr + off) _ _)).
    { destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). unfold alloc_ceiling in RC. lia. }
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
  split. { (* [comment removed for export] *) constructor.
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


End CeilWrap.
End RASlot_M1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_entry.
Module RASlot_M5D.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_M2.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  intros MR REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
  destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
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
  destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  cbn [ov_read_bytes] in RD.
  destruct (m (wa (r_base r + off))) as [b|] eqn:E.
  - cbn in RD. inversion RD. reflexivity.
  - rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x337ec.
Proof using . intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

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
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
(* [comment removed for export] *)
Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
  mkR (Z_to_bv 64 0x16400) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
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
  mem_inv psegs m'' /\ stk psegs m'' lo (bv_unsigned sp - 144) /\
  rw_cells psegs m'' (errno_addr tp) [C4 errv''] /\ rauxv_ok m'' (bv_unsigned sp - 144) /\
  rmrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
  rpres_except (rmalloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
  mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
  as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
  rw_cells psegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
  rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ rmrep st2 m4.

Definition rNFAIL_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  rnest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 ->
  rimplT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x16478) fc None m'' (seg_rom psegs)).

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
        F (Z_to_bv 64 0x16404) fc None m'' (seg_rom psegs)).
End LEVEL.


End CeilWrap.
End RASlot_M5D.

(* [comment removed for export] *)
Module RASlot_M5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W12 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_M2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3 RASlot_M5D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Hypothesis IHf : ralloc_slot_stmt2 f.

Hypothesis NFAIL : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Hypothesis NSUCC : rNSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.

Lemma rhnest_ok : rHNEST_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof using AR CLO ER IHf LO MR NFAIL NSUCC SC TP.
  clear A0 FIT RQ.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R SMc.
  destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  pose proof (RAS_STACK_nest sc (ncls sc cnt1) SCJ ltac:(lia)) as RSN. pose proof (RAS_STACK_ge (ncls sc cnt1)) as ASGj.
  unfold ag_nest. cbv zeta. fold (nreq sc cnt1). fold (ncls sc cnt1).
  pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _).
  unfold rcnt_state.
  (* [comment removed for export] *)
  riprefixT.
  eapply evt_cut.
  { replace (wz (size_class sc * UNIT * cnt1)) with (wz (size_class sc * 16 * cnt1)) by (unfold UNIT; reflexivity).
    eapply (rnest_call_walk (size_class sc) cnt1 SZR C1R ltac:(unfold UNIT in SMc; lia)). exact MI3. }
  cbv beta. intros ms' (a2x & a3x & a4x & ->).
  replace (size_to_class (size_class sc * 16 * cnt1 + 12)) with (ncls sc cnt1) by (unfold ncls; rewrite ENR; reflexivity).
  replace (wz (size_class sc * 16 * cnt1 + 12)) with (wz (nreq sc cnt1)) by (rewrite ENR; reflexivity).
  apply evt_done.
  assert (AUX4 : rauxv_ok m3 (bv_unsigned sp - 144)).
  { eapply rauxv_ok_weaken; [exact AUX3| split; [unfold alloc_ceiling; lia| lia]]. }
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp - 144) by (subst sp'; rewrite unsigned_lit by lia; lia).
  eapply (ralloc_slot_stmtL f IHf R _ bail o s' Q (Z_to_bv 64 0x16400) sp' gp tp) with (st0 := st0) (lo := lo) (sc := ncls sc cnt1) (req := nreq sc cnt1);
    rewrite ?SP'.
  - (* [comment removed for export] *) split; [exists LB; split; [exact AR| exact IS2]|]. split; [exact ER2|]. split; [exact AC2|]. split; [lia|]. split; [lia|]. exact NFIT.
  - exact MR3.
  - exact TK3.
  - exact UA3.
  - exact BL2.
  - exact AUX4.
  - replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact ST3.
  - exact CLO.
  - lia.
  - exact ERR3.
  - exact MI3.
  - exact TP.
  - reflexivity.
  - unfold wz. reflexivity.
  - (* [comment removed for export] *)
    intros st3 idx s'' ms'' PO LEAF.
    destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & ut3 & ut4 & ut5 & ut6 & m'' & errv'' & -> & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA'' & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & RES).
    rewrite ?SP' in *.
    (* [comment removed for export] *)
    assert (FR'' : rw_cells psegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply (rframe_keep_ER st0 st m MR ER st3 m'' lo (bv_unsigned sp - 144) m3 m''); [exact MR''| exact PE''| | lia| unfold alloc_ceiling; lia].
      replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact FR3. }
    assert (PSM2 : ps_m s'' = ps_m s) by (etransitivity; [exact PSM''| exact PSM]).
    assert (PSF2 : ps_fa s'' = ps_fa s) by (etransitivity; [exact PSF''| exact PSF]).
    assert (PSO2 : ps_so s'' = ps_so s) by (etransitivity; [exact PSO''| exact PSO]).
    assert (NCX : rnest_ctx f o s ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m st0 st lo sc st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o) by (repeat (split; [assumption|]); assumption).
    cbv beta.
    assert (IR : -1 <= idx < 32).
    { destruct RES as [->|(I0 & g3 & b3 & r3 & HA3 & SO3 & _)]; [lia|]. pose proof (so_idx _ _ _ _ _ _ SO3). pose proof (so_li _ _ _ _ _ _ SO3). lia. }
    replace (ret_pc (Z_to_bv 64 0x16400)) with (Z_to_bv 64 0x16400) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    riprefixT. eapply evt_cut.
    { eapply (rnest_ret_walk (Z_to_bv 64 0x16400) sp' gp tp) with (idx := idx); [exact IR| exact MI'']. }
    cbv beta. intros ms' ->. apply evt_done.
    replace sp' with (Z_to_bv 64 (bv_unsigned sp + -144)) by reflexivity.
    destruct RES as [->|(I0 & g3 & b3 & r3 & HA3 & SO3 & SPAN3 & RDV3)].
    + change (-1 <? 0) with true. change (-1 =? -1) with true. cbv iota.
      apply (NFAIL st1 st2 mm cnt1 st3 m3 m'' s' s'' errv'' junk oo o). exact NCX.
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (idx =? -1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite HA3. cbv iota beta.
      apply (NSUCC st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o g3 b3 r3); [exact NCX| exact I0| exact HA3| exact SO3| exact SPAN3| exact RDV3].
Qed.
End LEVEL.


End CeilWrap.
End RASlot_M5.

(* [comment removed for export] *)
Module RASlot_M5F.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W18 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W18 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W19 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_M2 RASlot_M5D.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rlowW (spv : Z) (iv : Z * Z) : Prop :=
  (0 <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x55000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928)))
  \/ iv = (spv - 144, spv).

Lemma rlowW_meta spv st m' q : rmrep st m' -> meta_slot st q -> rlowW spv (conc st q, conc st q + 40).
Proof using .
  intros MR MS. destruct (rmeta_slot_bounds st m' q MR MS) as (Gpos & GC & GI & _). left. unfold alloc_ceiling. cbn [fst snd]. lia.
Qed.

Definition rmetaW (spv : Z) (st : mstate) (iv : Z * Z) : Prop :=
  (exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (RCTX + 16, RCTX + 24) \/ iv = (spv - 144, spv).

Lemma rfailW_shape st mt spv :
  meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (rmetaW spv st) (rfailW st mt spv).
Proof using .
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
Proof using .
  intros MR MS FL. eapply Forall_impl; [| exact (rfailW_shape st mt spv MS FL)].
  intros [lo hi] [(q & MSq & E1 & E2)|[E|E]]; [cbn in E1, E2; subst; eapply rlowW_meta; eassumption| inversion E; subst; left; unfold alloc_ceiling, RCTX; cbn; lia| inversion E; subst; right; reflexivity].
Qed.

Lemma rlowW_disjoint spv W a n : Forall (rlowW spv) W -> alloc_ceiling <= a -> (a + n <= spv - 144 \/ spv <= a) -> disjoint_from W a n.
Proof using . intros FW Ha Hs. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(H1 & H2 & H3)|E]; [cbn in *; lia| inversion E; subst; lia]. Qed.

Lemma rlowW_disjoint_img spv W a n : Forall (rlowW spv) W -> 0x10000 <= a -> a + n <= 0x55000 -> (a + n <= RCTX \/ RCTX + 928 <= a) ->
  alloc_ceiling <= spv - 144 -> disjoint_from W a n.
Proof. intros FW H1 H2 H3 H4. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(X1 & X2 & X3)|E]; [cbn in *; unfold alloc_ceiling in *; lia| inversion E; subst; unfold alloc_ceiling in *; lia]. Qed.

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
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rnfail_ok : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof using AR AUX CLO ER ERR HK IS LO MR RQ SC TP.
  intros st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC.
  destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof (rerrno_lit5 tp TP) as EA.
  destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), (-1); split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 (-1) AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  pose proof (rmeta_slot_bounds st2 m4 mm MR4 MSL) as (Gpos & GC & GI & _).
  (* [comment removed for export] *)
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
  assert (ST7 : stk psegs m7 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]].
    replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR7 : rw_cells psegs m7 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
  eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
  cbv beta. intros ms' (a1y & a2y & -> & ST8). apply evt_done.
  (* [comment removed for export] *)
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
        * inversion E; subst. left. right. right. left. unfold RCTX in *. lia.
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
    - intros b. rewrite PF3. tclose.
    - intros rid r off h Hr Hk Ho Hc NG.
      pose proof MR'' as (WF3 & _). pose proof WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC.
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


End CeilWrap.
End RASlot_M5F.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W13.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W14.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMallocKit_A3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RASlot_W13.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W13 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

(* [comment removed for export] *)
Lemma rnenf_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
  0 <= c_mmap_counter (ctx st) < 2^32 -> mem_inv psegs m1 ->
  evt psegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x16430) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 (RSIZE_CLASSES + j * 2)) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x16430) fc None m' (seg_rom psegs)
      /\ munch [(P - 3, P)]%Z m1 m' /\ wmono psegs m1 m' /\ mem_inv psegs m'
      /\ rmrep (enf0_st st g b idx) m' /\ ticks_ok (enf0_st st g b idx))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 j) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16404) fc None m1 (seg_rom psegs)).
Proof using HA J MR MSL MW SCg SO STR TK UA.
  intros until fc. intros CTR MI.
  (nelimp (enf_facts st g b r idx j SO) 13%nat; intros Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  pose proof (size_class_range j J) as SZR.
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  (nelim (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0) 13%nat; intros x3 x2 x1 WRs Y E3 E2 E1 CB R4 PEND RC RI1)
.
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND. 
  (nelimp (rmeta_chunk_facts st m1 g MR MSL) 7%nat; intros MM G0 GC GI1 GI2 GDJ GRG).
  unfold alloc_ceiling in RC, GC.
  set (G := conc st g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  pose proof (bytes_at_read psegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read psegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read psegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  (nelimp MW 4%nat; intros LI0 FB0 SCR0 ML0).
  (nelimp MR 4%nat; intros WF' CX GL _). destruct CX as (CH & _). unfold rctx_head_cells in CH.
  unfold RSIZE_CLASSES, RMLOCK, RCTX in *.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  step. step.
  (* [comment removed for export] *)
  pose proof (rsize_classes_read m1 j MI J) as SCRD. unfold RSIZE_CLASSES in SCRD.
  replace (67680 + 2 * j) with (67680 + j * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st m1 j (wa (342928 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
  replace (wa (342928 + 80 + 8 * j)) with (Z_to_bv 64 (342920 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  step.
  (* [comment removed for export] *)
  step.
  eapply evt_mono.
  { eapply (renframe_walk (Z_to_bv 64 0x16430) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
              (pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
         | |- _ => idtac end.
    all: try (rewrite (unsigned_lit G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
    - exact (so_maplen _ _ _ _ _ _ SO). }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  (nelim PO 18%nat; intros w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' -> EM MI').
  set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
  pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
  replace (fold_off off0 0) with 0 in EM |- * by lia.
  rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
  replace (ret_pc (Z_to_bv 64 0x16430)) with (Z_to_bv 64 0x16430) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - N < 2^31) by lia.
  assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
  assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
  assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
  (nelim (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4) 5%nat; intros MRr TKr CONCr FSTr SNDr)
. clear T1 T3 T0 TN T4.
  rewrite Z.mul_0_r, Z.add_0_r in MRr.
  change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
  fold P in MRr, EM. rewrite <- EM in MRr.
  destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.
  (* [comment removed for export] *)
  assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
  { rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
    replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
  assert (MU : munch [(P - 3, P)]%Z m1 m').
  { rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono psegs m1 m').
  { rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
  nexists 14%nat. exists m'.
  split; [unfold P, G; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
(* [comment removed for export] *)
Lemma rnoov16 (zb0 zb zs zx zi zc : Z) :
  zb0 = 16 * (zb0 / 16) -> zb = 16 * (zb / 16) -> zs = 16 * (zs / 16) ->
  ~ (zb0 <= zb + (16 + zs * zx) + (16 + zi * (16 * zc) - 4) < zb0 + 9).
Proof using N P.
  intros zE0 zE1 zE2 zC.
  assert (zE3 : zs * zx = 16 * ((zs / 16) * zx)) by (rewrite zE2 at 1; ring).
  rewrite zE3 in zC. replace (zi * (16 * zc)) with (16 * (zi * zc)) in zC by ring.
  set (zX := (zs / 16) * zx) in zC. set (zY := zi * zc) in zC.
  set (zq0 := zb0 / 16) in zE0. set (zq1 := zb / 16) in zE1.
  rewrite zE0, zE1 in zC. clearbody zX zY zq0 zq1. lia.
Qed.

Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof using N P. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.

(* [comment removed for export] *)
Lemma renfD_walk :
  forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mt : aptr) (cnt : Z) mC,
  meta_slot st mt -> mw_ok (get_meta_rec st mt) -> 1 <= cnt <= 32 ->
  rmrep (enf0_st st g b idx) mC -> ticks_ok (enf0_st st g b idx) -> mem_inv psegs mC ->
  evt psegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (P + 12)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x16458) fc None m' (seg_rom psegs)
      /\ munch [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC m' /\ wmono psegs mC m' /\ mem_inv psegs m'
      /\ rmrep (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))) m'
      /\ ticks_ok (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16430) fc None mC (seg_rom psegs)).
Proof using J MR SO TK.
  intros until mC. intros MST MWT CR MRC TKC MIC.
  (nelimp (enf_facts st g b r idx j SO) 13%nat; intros Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  (nelimp (rregion_facts st m1 (fst b) r MR Hr) 5%nat; intros R4 RAL RC RI1 RI2). unfold alloc_ceiling in RC.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  set (st0' := enf0_st st g b idx) in *.
  assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  (nelimp (rmeta_slot_bounds st0' mC mt MRC MST0) 5%nat; intros Tpos TC TI _ _).
  change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
  (nelimp (rmeta_chunk_facts st0' mC mt MRC MST0) 7%nat; intros _ _ _ _ _ GDJ _).
  assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
  assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
  rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
  pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl psegs mC) as WM.
  (nelimp MWT 4%nat; intros LI0 FB0 SCR0 ML0). pose proof (meta_word_range _ MWT) as MWR.
  unfold alloc_ceiling in TC.
  (* [comment removed for export] *)
  rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
  rmeta_open (conc st mt) MUt WMt.
  step.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
  set (w := meta_word (get_meta_rec st mt)) in *.
  rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
  rewrite (meta_word_mod4096 st g b idx j _ MWT).
  step.
  lazymatch goal with H : rw_cells psegs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
    [ eapply rmrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
      unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
    | clear MUt WMt H ] end.
  set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
  assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).
  (* [comment removed for export] *)
  pose proof (land31_range idx) as L31.
  assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
  { change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
    rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
      [| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
    change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
  destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
    by (unfold wa; f_equal; unfold P; lia).
  step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit cnt), swrap32_small by lia.
  step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
  step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.
  (* [comment removed for export] *)
  (nelimp MR5 6%nat; intros _ _ _ _ _ SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
  pose proof (wr_at_store_ok psegs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
  assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
  cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
  assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
  specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
  replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
  rewrite <- (lor_192 (Z.land idx 31)) by lia.
  rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit P) by (unfold P; lia).
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.
(* [comment removed for export] *)
Lemma rzero_loop_walk : forall k (i szc cnt : Z) stz mC0 mC
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  Z.of_nat k = cnt + 1 - i -> 0 <= i <= cnt -> 1 <= szc -> 0 <= cnt < 4096 -> 16 + 16 * szc * cnt <= stride ->
  s_regions stz = s_regions st -> s_groups stz = s_groups st ->
  rmrep stz mC -> ticks_ok stz -> mem_inv psegs mC ->
  munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 mC -> wmono psegs mC0 mC ->
  evt psegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (cnt - 1)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x16728) fc None m' (seg_rom psegs)
      /\ munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 m' /\ wmono psegs mC0 m' /\ mem_inv psegs m'
      /\ rmrep (zero_hdrs (pp st g b idx) (16 * szc) i k stz) m' /\ ticks_ok (zero_hdrs (pp st g b idx) (16 * szc) i k stz)
      /\ s_regions (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_regions st /\ s_groups (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_groups st
      /\ (forall x, (forall j, i <= j <= cnt -> bv_unsigned x <> P + 12 + 16 * szc * j) -> m' x = mC x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt + 1 - i)) (Z_to_bv 64 (P + 12 + 16 * szc * i)) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16458) fc None mC (seg_rom psegs)).
Proof using MR STR SO.   (* [comment removed for export] *)
  induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
  { exfalso. lia. }
  (nelimp (enf_facts st g b r idx j SO) 13%nat; intros Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
  (nelimp (rregion_facts st m1 (fst b) r MR Hr) 5%nat; intros R4 RAL RC RI1 RI2). unfold alloc_ceiling in RC.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  (* [comment removed for export] *)
  assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
  (nelimp MRz 6%nat; intros WFz _ _ _ _ SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
  pose proof (wr_at_store_ok psegs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
  unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
  specialize (MR2 Hr' Hk ltac:(lia)).
  assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
            ~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
  { intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). (nelimp WF 5%nat; intros _ _ _ _ GWF).
    (nelim (GWF b0 gh Hb0) 6%nat; intros r0 _ _ _ _ M16).
    destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
    assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
    assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
    assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).
    clear M16 B16 SMOD. exact (rnoov16 _ _ _ _ _ _ E0 E1 E2 CONTRA). }   (* [comment removed for export] *)
  specialize (MR2 NOG ltac:(lia)). clear NOG.
  replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
    assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
    [ intros u Hu Hux;
      rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
      destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
      exfalso; lia
    | apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
      apply (wmono_write psegs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
      lazymatch goal with HI : mem_inv psegs mX |- _ =>
        apply (mem_inv_store psegs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
        [| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
      end;
      clear SOK;
      let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
  end.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
    replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    eapply evt_mono.
    { (eapply (IH (i + 1) szc cnt);
      [ lia | lia | exact SZC | exact CNT | exact FIT
      | rewrite s_regions_wr8; exact RGz
      | rewrite s_groups_wr8; exact GRz
      | exact MR2
      | apply ticks_ok_wr8; exact TKz
      | assumption | exact MU | exact WM ]). }
    cbv beta. intros ms' nelH_; (nelim nelH_ 10%nat; intros m' -> X1 X2 X3 X4 X5 X6 X7 PW).
    eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. split; [exact X7|].
    intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
  - (* [comment removed for export] *)
    assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
    apply evt_done. eexists. split; [reflexivity|].
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
    split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
    intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.


End CeilWrap.
End RASlot_W13.

(* [comment removed for export] *)
Module RASlot_W14.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9.ASlot_W3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac step ::= step1.  Local Ltac stepz ::= step1.  (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof using .
  intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
  rewrite (mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal. 
Qed.

Lemma unsigned_mod32_add_not a b : 0 <= b < 2^64 ->
  (bv_unsigned (wz (sxv a)) + Z.lxor b 18446744073709551615) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
  intros Hb. rewrite zb_lxor_ones by lia. rewrite (wz_unsigned (sxv a)) by (apply sxv_range).
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l.
  replace (a + (18446744073709551615 - b)) with ((a - 1 - b) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma unsigned_mod32_swrap_add_not a b :
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
  pose proof (sxv_range b) as RB.
  rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
  replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia.
  unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
  assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
  clearbody x y. Z.div_mod_to_equations. nia.
Qed.
Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof using .
  intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite <- !Z.land_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition rtailW : list (Z * Z) :=
  [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z.

(* [comment removed for export] *)
Lemma rtail_walk :
  forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
  rmrep stT mC -> mem_inv psegs mC ->
  evt psegs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
                   s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x16880) fc None m' (seg_rom psegs)
      /\ munch rtailW mC m' /\ wmono psegs mC m' /\ mem_inv psegs m'
      /\ rmrep (stFin stT sc cnt ai ml mt p) m' /\ ticks_ok (stFin stT sc cnt ai ml mt p))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16728) fc None mC (seg_rom psegs)).
Proof using ACT AI CNT GNONE Hk Hr ML MST NOGRP OLD12 P0 P16 PEND REC SC TK UR.
  intros until mC. intros MR MI.
  pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl psegs mC) as WM. unfold rtailW in MU.
  (nelimp (rmeta_slot_bounds stT mC mt MR MST) 5%nat; intros Gpos GC GI G4 _). fold G in Gpos, GC, GI, G4.
  (nelimp (rregion_facts stT mC (fst p) r MR Hr) 5%nat; intros R4 RAL RC RI1 RI2). unfold alloc_ceiling in RC.
  assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
  (nelimp (AV_FR_range stT cnt ai mt p CNT AI P0) 3%nat; intros AVR FRR AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.
  (* [comment removed for export] *)
  destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
  unfold RCTX, RMLOCK, alloc_ceiling in *.
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read (stA stT p) mC sc (wa (342928 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
  change (usage (stA stT p) sc) with (usage stT sc) in RDU.
  replace (wa (342928 + 464 + 8 * sc)) with (Z_to_bv 64 (342920 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
  step. clear RDU.
  (* [comment removed for export] *)
  step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.
  (* [comment removed for export] *)
  pose proof MRA as (_ & (_ & _ & USG & _) & _).
  pose proof (u64arr_store_ok psegs _ _ (usages (stA stT p)) sc (wa (342928 + 464 + 8 * sc)) USG
                ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
  replace (wa (342928 + 464 + 8 * sc)) with (Z_to_bv 64 (342920 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
  rraw_store_finish0 (342928 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
  assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
  assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRA TKA.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia. rewrite ASlot_W14.sllw2_word by lia.
  step.
  set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
  rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
  rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
  replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
  rmeta_open G MUa WMa.
  (* [comment removed for export] *)
  step. step.
  assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
  { subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
  rewrite (sx32_congr v3 AV V3).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite ASlot_W14.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
  step. step.
  set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
  assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
  { subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
  (* [comment removed for export] *)
  step. step.
  lazymatch goal with H : rw_cells psegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
      unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
      change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
      rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
      rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
      replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
    | clear MUa WMa; rename H into CH1 ] end.
  assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
  assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRB TKB MSTB.
  (* [comment removed for export] *)
  (nelimp MRC 6%nat; intros WFC _ _ _ _ SHC). (nelimp WFC 5%nat; intros _ _ DJ _ WG).
  destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    (nelim (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) 3%nat; intros hb LHB HB) end.
  destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HDR : rw_cells psegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
    [ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
    | clear HB LHB ] end.
  (nelimp (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) 7%nat; intros _ _ _ _ _ GRG _).
  pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl psegs mX) as WMb end.
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  step.
  pose proof (byte_range y8) as Y8.
  step. unfold zxb.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia.
  replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
  step.
  pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
  rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
  rewrite (land224_m32 (bv_unsigned y8)) by lia.
  pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].
  (* [comment removed for export] *)
  set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
  step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells psegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    rename H into HDR2;
    assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
    | assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
      [ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
        [ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
        | rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
      | ] ] end.
  { (* [comment removed for export] *)
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
    destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
    - unfold RCTX in X1. lia.
    - unfold RMLOCK in X2. lia.
    - unfold RNEED_LOCKS in X3. lia.
    - unfold RPAGE_SIZE in X4. lia.
    - change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
      (nelim (rarea_conc stT ak ar WFC Hak) 8%nat; intros rga Hra Ca Sa0 Sa1 _ NK _).
      assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
      pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
    - change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
      (nelim (rgroup_conc stT b gh WFC Hb) 7%nat; intros rb Hrb Cb Kb Sb0 Sb1 _).
      destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
      + rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
      + pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
    - change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
      destruct (N.eq_dec q (fst p)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
                    ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
    - unfold RGOT_SSP in X5. lia.
    - unfold RSSP_GUARD in X6. lia. }
  clear MRC MRC2 MUb WMb HDR2.
  assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
  assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear TKC MSTC.
  (* [comment removed for export] *)
  pose proof MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
  rmchunk MRD MSTD CH.
  change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
  unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
  change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
  set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
  rmeta_open G MUc WMc.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
  replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
  rewrite (unsigned_lit W), EW, land_pg_mask by lia.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
  replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. step. step. step.
  rewrite ?(unsigned_lit (mask_upto ai)) by lia.
  (* [comment removed for export] *)
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  lazymatch goal with H : u64arr psegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read psegs mX (342928 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (342928 + 80 + 8 * sc)) H
                  (actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
  change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
  replace (wa (342928 + 80 + 8 * sc)) with (Z_to_bv 64 (343008 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. step. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells psegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
      eapply rw_cells_congr; [| | | exact H]
    | clear MUc WMc; rename H into CH3 ] end.
  { unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
    change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
    unfold wz. rewrite !app_nil_r.
    rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
    2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
        rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
        fold AV. Z.div_mod_to_equations. lia. }
    do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
  { reflexivity. }
  { cbn. tclose. }
  assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
  clear MRD TKD MSTD.
  (* [comment removed for export] *)
  clear CH3.
  lazymatch goal with H : u64arr psegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_store_ok psegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (342928 + 80 + 8 * sc)) H
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
  replace (wa (342928 + 80 + 8 * sc)) with (Z_to_bv 64 (343008 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
  st1.
  replace (Z_to_bv 64 (343008 + 8 * sc + 0)) with (Z_to_bv 64 (343008 + 8 * sc)) in SOK by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
  unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
  rraw_store_finish0 (342928 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. nexists 6%nat. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MRF| exact TKE].
Qed.
End TAIL.


End CeilWrap.
End RASlot_W14.

(* [comment removed for export] *)
Module RASlot_M5S.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W13 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M4P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M5P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4 RASlot_W13 RASlot_W14 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W18 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W19 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_M2 RASlot_M5D.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rgrp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. intros EG nelH_; (nelim nelH_ 5%nat; intros b gh Hb Hf Ho). exists b, gh. rewrite EG. auto. Qed.

Lemma rmrep_st_model stT sc cnt ai ml mt p (SC : 0 <= sc < 48) (CNT : 1 <= cnt <= 32)
      (REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml) (P0 : 0 <= snd p) m :
  rmrep (stFin stT sc cnt ai ml mt p) m -> rmrep (st_model stT sc cnt ai mt p) m.
Proof using .
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
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rnsucc_ok : rNSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof using AR AUX CLO ER ERR FIT HK IS LO MR RQ SC TP.
  intros st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC I0 HA3 SO3 SPAN3 RDV3.
  destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA'' (* [comment removed for export] *)
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  (nelim (nest_class sc SC cnt1 C1R SMc) 6%nat; intros ENR JR FITN SCJ NRR NFIT).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), idx; split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 idx AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  (nelimp (rmeta_slot_bounds st3 m'' mm MR'' MS3) 4%nat; intros Gpos GC GI _).
  (* [comment removed for export] *)
  pose proof (so_mem _ _ _ _ _ _ SO3) as Hmem3. pose proof (so_reg _ _ _ _ _ _ SO3) as Hr3. pose proof (so_kind _ _ _ _ _ _ SO3) as Hk3.
  pose proof (so_mslot _ _ _ _ _ _ SO3) as MSLg. pose proof (so_fit _ _ _ _ _ _ SO3) as FIT3. pose proof (so_idx _ _ _ _ _ _ SO3) as IDX3.
  pose proof (so_b0 _ _ _ _ _ _ SO3) as B30. pose proof (so_span _ _ _ _ _ _ SO3) as SP3. pose proof (so_li _ _ _ _ _ _ SO3) as LI3.
  pose proof (mf_active _ _ MF3) as FA3. change (fact_active (strip st3)) with (fact_active st3) in FA3.
  (nelim (FA3 (ncls sc cnt1) g3 HA3) 3%nat; intros _ GSC3 _).
  pose proof (lf_host_stride _ (isf_lf _ _ F3) g3 b3 Hmem3 ltac:(change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3); rewrite GSC3; lia)) as STR3.
  change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in STR3. rewrite GSC3 in STR3.
  (nelimp (lf_mw _ (isf_lf _ _ F3) g3) 3%nat; intros MW3 _ _). change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in MW3.
  set (strideg := get_stride (get_meta_rec st3 g3)) in *.
  set (szc := size_class sc) in *.
  assert (FITg : 16 * szc * cnt1 + 16 <= strideg) by lia.
  assert (SZC1 : 16 * szc <= 16 * szc * cnt1) by nia.
  assert (SO_N : slot_ok st3 g3 b3 r3 idx (UNIT * size_class (ncls sc cnt1) - IB)) by (eapply slot_ok_N; [exact SO3| unfold IB; lia| unfold UNIT, IB; lia]).
  set (X := snd b3 + (16 + strideg * idx)) in *.
  set (p := (fst b3, X) : aptr).
  (nelimp (rregion_facts st3 m'' (fst b3) r3 MR'' Hr3) 5%nat; intros R4 RAL RC RI1 RI2). unfold alloc_ceiling in RC.
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
  (nelim (nt_tail_hyps st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3) 10%nat; intros TMS TREC TREG TP0 TP16 TPEND TGN TNOG TOLD TTK)
.
  fold strideg X p in TMS, TREC, TREG, TP0, TP16, TPEND, TGN, TNOG, TOLD, TTK.
  set (stT := nt_stT st3 g3 b3 idx sc cnt1 mm) in *.
  assert (ACT3 : active st3 sc = None).
  { rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). exact ACT0. }
  assert (ACTT : active stT sc = None) by (unfold stT; rewrite ntT_active; exact ACT3).
  rewrite (ag_tail_kq_eq sc k bail stT mm p cnt1 (cnt1 - 1)); [| rewrite TREC; reflexivity| rewrite TREC; reflexivity| exact ACTT].
  (nelim (ntT_proj st3 g3 b3 idx sc cnt1 mm) 8%nat; intros TPR TPG TPA TPT TPN TPRS TPC TPS). fold stT in TPR, TPG, TPA, TPT, TPN, TPRS, TPC, TPS.
  assert (URT : 0 <= usage stT sc < 2^60).
  { unfold stT. rewrite ntT_usage. pose proof (mf_usage _ _ MF3 sc) as U. exact U. }
  assert (TCONC : forall q, conc stT q = conc st3 q) by (intros q; unfold stT; apply ntT_conc).
  (* [comment removed for export] *)
  riprefixT. unfold rnest_regs. rewrite <- GE.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rnenf_walk st3 m'' o g3 b3 r3 idx (ncls sc cnt1) MR'' UA'' JR' HA3 MSLg MW3 GSC3 STR3 SO_N TK''); [exact CTR''| exact MI'']. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 21%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m5 -> MU5 WM5 MI5 MR5 TK5).
  fold strideg.
  (* [comment removed for export] *)
  assert (MWmm : mw_ok (get_meta_rec st3 mm)) by (rewrite G3; unfold mw_ok, meta0; cbn; lia).
  eapply evt_cut.
  { change (wz cnt1) with (Z_to_bv 64 cnt1).
    eapply (renfD_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' JR' SO_N TK''); [exact MS3| exact MWmm| exact C1R| exact MR5| exact TK5| exact MI5]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 7%nat; intros m6 -> MU6 WM6 MI6 MR6 TK6).
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
  cbv beta. intros ms' nelH_; (nelim nelH_ 10%nat; intros m7 -> MU7 WM7 MI7 MR7 TK7 RG7 GR7 PW7).
  change (zero_hdrs (pp st3 g3 b3 idx) (16 * szc) 0 (Z.to_nat (cnt1 + 1)) (nt_stW st3 g3 b3 idx mm)) with stT in MR7, TK7, RG7, GR7.
  fold P in MU7, PW7.
  (* [comment removed for export] *)
  eapply evt_cut.
  { replace (Z_to_bv 64 P) with (Z_to_bv 64 (conc stT p)) by (rewrite TCONC, CP, EP; reflexivity).
    replace (Z_to_bv 64 (conc st3 mm)) with (Z_to_bv 64 (conc stT mm)) by (rewrite TCONC; reflexivity).
    eapply (rtail_walk stT sc cnt1 (cnt1 - 1) 0 mm p r3 SC C1R ltac:(lia) ltac:(lia) TMS TREC TREG Hk3 TP0 TP16 TPEND TGN TNOG TOLD URT ACTT TK7);
      [exact MR7| exact MI7]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 12%nat; intros s0x a1x a2y a3x a4z m8 -> MU8 WM8 MI8 MR8 TK8).
  (* [comment removed for export] *)
  set (W58 := ([(P - 3, P); (conc st3 mm, conc st3 mm + 40); (P - 3, P - 2); (P + 12, P + 12 + 16 * szc * cnt1 + 1)]%Z ++ rtailW stT sc mm p)).
  assert (LOWW : Forall (fun iv : Z * Z => snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x55000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928))) W58).
  { apply Forall_forall. intros [lo' hi'] HI. cbn [fst snd]. unfold W58, rtailW in HI. rewrite !TCONC, CP in HI. cbn [app In] in HI.
    pose proof (round_up_pg_ge (r_len r3)).
    destruct HI as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; inversion E; subst; unfold RCTX; lia. }
  assert (MU58 : munch W58 m'' m8).
  { intros x Hx. unfold W58 in Hx. rewrite outside_app' in Hx. destruct Hx as [H4x H8].
    rewrite (MU8 x H8). cbn [outside] in H4x. (nelim H4x 5%nat; intros H5 H6a H6b H7 _).
    rewrite (MU7 x) by (cbn; auto). rewrite (MU6 x) by (cbn; auto). rewrite (MU5 x) by (cbn; auto). reflexivity. }
  assert (WM58 : wmono psegs m'' m8).
  { eapply wmono_trans; [exact WM5|]. eapply wmono_trans; [exact WM6|]. eapply wmono_trans; [exact WM7| exact WM8]. }
  assert (DJhigh : forall A n, alloc_ceiling <= A -> disjoint_from W58 A n).
  { intros A n HA. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [H _]. lia. }
  assert (DJimg : forall A n, 0x10000 <= A -> A + n <= 0x55000 -> (A + n <= RCTX \/ RCTX + 928 <= A) -> disjoint_from W58 A n).
  { intros A n H1 H2 H3. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [_ H]. unfold RCTX in *. lia. }
  assert (FR8 : rw_cells psegs m8 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact FR''. }
  assert (ST8 : stk psegs m8 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR8 : rw_cells psegs m8 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU58| exact WM58|]. rewrite EA. apply DJimg; [lia| cbn; lia| unfold RCTX; cbn; lia]. }
  set (stF := st_model stT sc cnt1 (cnt1 - 1) mm p).
  assert (MRF : rmrep stF m8) by (exact (rmrep_st_model stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 m8 MR8)).
  eapply evt_cut. { unfold rFRM in FR8. eapply (ras_ret0 sp gp tp); [exact MRF| exact MI8| exact FR8| exact ST8| exact CLO| lia]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 4%nat; intros a1w a2w -> ST9). apply evt_done.
  apply HK.
  (* [comment removed for export] *)
  fold strideg in MU7, PW7. fold P in MU7, PW7.
  (nelim (smg_proj stT sc cnt1 (cnt1 - 1) mm p) 10%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10).
  fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
  rewrite TPR in PF1. rewrite TPA in PF4. rewrite TPT in PF5. rewrite TPN in PF6. rewrite TPRS in PF7.
  assert (CTXT : ctx stT = ctx st3) by (unfold stT; apply ntT_ctx).
  rewrite CTXT in PF8, PF9, PF10.
  assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK8]; reflexivity).
  assert (MSF : meta_slot stF mm) by (apply (proj1 (smg_meta_slot stT sc cnt1 (cnt1 - 1) mm p mm)); exact TMS).
  assert (CF : forall q, conc stF q = conc st3 q) by (intros q; unfold stF; rewrite (smg_conc stT sc cnt1 (cnt1 - 1) mm p q); apply TCONC).
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR'' as (WF3 & _). (nelimp WF3 4%nat; intros RS3 WR3 DJ3 _).
  assert (STRF : get_stride (get_meta_rec stF mm) = 16 * szc) by (exact (ntF_stride st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)).
  (* [comment removed for export] *)
  assert (HOLD2 : forall q rq, (s_regions st2) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. (nelim (mrel_regions _ _ MREL'' q rq Hq) 5%nat; intros r' Hr' K' B' L'). exists r'. rewrite PF1. auto. }
  assert (HOLD3 : forall q rq, (s_regions st3) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. exists rq. rewrite PF1. repeat split; auto. lia. }
  assert (INSPAN : forall a, r_base r3 + X - 4 <= a < r_base r3 + X + strideg - 4 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3). apply SPAN3. unfold X in Ha. lia. }
  assert (INMETA : forall a, conc st3 mm <= a < conc st3 mm + 40 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. left. do 3 right. destruct (rmeta_chunk_facts stF m8 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
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
    (nelim (WR3 _ _ Hrr) 5%nat; intros R0 _ _ RCr _). unfold alloc_ceiling in RCr.
    (nelim (rregion_facts st3 m'' rid rr MR'' Hrr) 5%nat; intros _ _ _ RI1r RI2r). specialize (RI1r ltac:(lia)). specialize (RI2r ltac:(lia)).
    (nelim (rmeta_chunk_facts st3 m'' mm MR'' MS3) 7%nat; intros _ _ _ _ _ GRG _). pose proof (GRG rid rr Hrr Kr) as GRr.
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
      transitivity (m7 (wa (r_base r3 + off))). { apply MU8. rewrite wa_unsigned by (clear - R0 Ho RCr; lia). unfold rtailW. rewrite !TCONC, CP. cbn. unfold RCTX. clear - Ho RI1r RI2r GRr NHC SC; lia. }
      transitivity (m6 (wa (r_base r3 + off))). { apply PW7. rewrite wa_unsigned by (clear - R0 Ho RCr; lia). intros j Hj E. apply NZ. exists j. split; [exact Hj|]. clear - E EP Hj; lia. }
      transitivity (m5 (wa (r_base r3 + off))). { apply MU6. rewrite wa_unsigned by (clear - R0 Ho RCr; lia). cbn. clear - GRr Ho EP NH B30 SK; lia. }
      apply MU5. rewrite wa_unsigned by (clear - R0 Ho RCr; lia). cbn. clear - EP NH B30 SK; lia.
    - assert (Hc3 : cell_read (get_shadow st3 rid) off = Unknown h).
      { rewrite <- (ntF_shadow_other st3 g3 b3 idx sc cnt1 mm rid NE). exact Hc. }
      rewrite <- (UA'' rid rr off h Hrr Kr Ho Hc3 NG3).
      pose proof (lr_lo_group rr Kr) as LR1. pose proof (lr_lo_group r3 Hk3) as LR2.
      assert (NE' : fst b3 <> rid) by (intros E; apply NE; symmetry; exact E).
      pose proof (round_up_pg_ge (r_len r3)) as RU3.
      destruct (DJ3 _ _ _ _ Hr3 Hrr NE') as [D|D].
      all: transitivity (m7 (wa (r_base rr + off))); [apply MU8; rewrite wa_unsigned by (clear - R0 Ho RCr; lia); unfold rtailW; rewrite !TCONC, CP; cbn [outside]; unfold RCTX; clear - Ho RI1r RI2r SC GRr D LR1 LR2 B30 SK XEND FITg SZC1 SZR; lia|].
      all: transitivity (m6 (wa (r_base rr + off))); [apply MU7; rewrite wa_unsigned by (clear - R0 Ho RCr; lia); cbn [outside]; clear - Ho D LR1 LR2 B30 SK XEND EP FITg SZC1 SZR; lia|].
      all: transitivity (m5 (wa (r_base rr + off))); [apply MU6; rewrite wa_unsigned by (clear - R0 Ho RCr; lia); cbn [outside]; clear - Ho GRr D LR1 LR2 B30 SK XEND EP FITg SZC1 SZR; lia|].
      all: apply MU5; rewrite wa_unsigned by (clear - R0 Ho RCr; lia); cbn [outside]; clear - Ho D LR1 LR2 B30 SK XEND EP FITg SZC1 SZR; lia. }
  assert (RSP3 : ret_span st3 (ncls sc cnt1) idx (fst b3) X (strideg - 4)).
  { exists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  unfold ras_post2.
  nexists 14%nat. exists m8, errv''. split; [reflexivity|].
  split; [exact MI8|]. split; [exact ST9|]. split; [exact ERR8|].
  split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m8); [exact MRF| exact AUX| exact PE08| exact CLO| lia]|].
  split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE08|].
  split. { split.
    - intros q rq Hq. rewrite <- REG1 in Hq. (nelim (amr_regions _ _ _ REL q rq Hq) 6%nat; intros r' H' K' B' L' _).
      (nelim (HOLD2 q r' H') 5%nat; intros r'' H'' K'' B'' L''). exists r''. split; [exact H''|]. split; [rewrite K''; exact K'|]. split; [rewrite B''; exact B'|]. lia.
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
      (nelim (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) 3%nat; intros -> -> ->).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho.
      unfold p in Hc, Ho. cbn [fst snd] in Hc, Ho. rewrite PF5.
      unfold stF, stT, p in Hc. rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') in Hc by (fold szc; lia).
      eapply FRESH3; [| exact Hc]. lia.
    - intros E0 _ rid' S len RSP o' Ho.
      (nelim (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) 3%nat; intros -> -> ->).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho. unfold p in Ho. cbn [snd] in Ho.
      (nelim (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 o' ltac:(lia)) 3%nat; intros V1 V2 V3).
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
    (nelim (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 (X + 13) ltac:(lia)) 3%nat; intros V1 V2 V3).
    unfold stF, stT. apply (ntF_rdv13 st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N o V1 V2 V3).
Qed.
End LEVEL.


End CeilWrap.
End RASlot_M5S.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W15.
Module RASlot_W15.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15.F_malloc_bigw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition rseqW : list (Z * Z) := [(RCTX + 848, RCTX + 913)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rbounce_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
  mem_inv psegs m ->
  evt psegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x165a0) fc None m' (seg_rom psegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch rseqW m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ rmrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162ec) fc None m (seg_rom psegs)).
Proof using SC.
  intros until m. intros MR SEQ BR USR MI.
  pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl psegs m) as WM. unfold rseqW in MU.
  unfold RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
    rmrep stX mX -> stX = account_bounce sc st -> mem_inv psegs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
    munch [(342928 + 848, 342928 + 913)]%Z m mX -> wmono psegs m mX ->
    evt psegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 342920) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x165a0) fc None m' (seg_rom psegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch [(342928 + 848, 342928 + 913)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ rmrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 342920) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1659c) fc None mX (seg_rom psegs))).
  { intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
    pose proof (rmrep_seq_read stX mX (wa (342928 + 912)) MRX eq_refl) as RDS.
    replace (wa (342928 + 912)) with (Z_to_bv 64 (342920 + 920)) in RDS by (unfold wa; f_equal; lia).
    assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
    { rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
      destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
    rewrite SQX in RDS.
    step. rewrite ?zxb_b8 by lia. clear RDS.
    apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { (* [comment removed for export] *)
    assert (HO : sc_in_seq_range sc = false).
    { unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
      - replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      - rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
        replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
    step. step.
    eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
    - unfold account_bounce. rewrite HO. reflexivity.
    - unfold is_bouncing. rewrite HO. reflexivity. }
  rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
  destruct (Z.lt_ge_cases sc 7) as [L7|G7].
  { exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
  rewrite Z.mod_small in K by lia.
  assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc + -7)) by lia.
  pose proof (rmrep_bounces_read st m (sc - 7) (wa (342928 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
  replace (wa (342928 + 880 + (sc - 7))) with (Z_to_bv 64 (342920 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
  pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
  step. rewrite ?zxb_b8 by lia. clear RDB.
  pose proof MR as (_ & (_ & _ & _ & US & _) & _).
  pose proof (u8arr_read psegs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (342920 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
                ltac:(unfold wa, RCTX; f_equal; lia)) as RDU. clear US.
  step. rewrite ?zxb_b8 by lia. clear RDU.
  (* [comment removed for export] *)
  step. step.
  set (nos := 100 <=? bounces st (sc - 7)).
  assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
  assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
  { rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    change (bv_wrap 64 100) with 100.
    destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
  rewrite A3. clear A3.
  assert (AB : account_bounce sc st =
    (if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
     then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
     else st)) by (unfold account_bounce; rewrite IN; reflexivity).
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
  { eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }
  (* [comment removed for export] *)
  pose proof (rmrep_seq_read st m (wa (342928 + 912)) MR eq_refl) as RDS.
  replace (wa (342928 + 912)) with (Z_to_bv 64 (342920 + 920)) in RDS by (unfold wa; f_equal; lia).
  step. rewrite ?zxb_b8 by lia. clear RDS.
  step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
  step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
  { (* [comment removed for export] *)
    apply Z.ltb_lt in K2.
    apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.andb_false_r. exact MR. }
  apply Z.ltb_ge in K2.
  assert (AB2 : account_bounce sc st =
    (if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
  { rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  clear AB K1 K2.
  pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _).
  pose proof (u8arr_store_ok psegs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (342920 + (sc + -7) + 888)) BA
                ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear BA.
  (* [comment removed for export] *)
  step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish0 (342928 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. step. st1. rewrite (le1_lit 150) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish0 (342928 + 880 + (sc - 7)) [b8 150] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rseq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m0 m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> mem_inv psegs m ->
  munch rseqW m0 m -> wmono psegs m0 m ->
  evt psegs (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x165cc) fc None m' (seg_rom psegs)
      /\ munch rseqW m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m' /\ rmrep (step_seq st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 (wz (c_seq (ctx st))) a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x165a0) fc None m (seg_rom psegs)).
Proof using .
  intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
  set (q := c_seq (ctx st)) in *.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & _).
  unfold RCTX, RMLOCK in *. unfold ctx_tail_cells in C6.
  replace (342928 + 912) with 343840 in C6 by reflexivity. replace (342928 + 848) with 343776 in US by reflexivity.
  (* [comment removed for export] *)
  assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv psegs mj ->
    munch [(342928 + 848, 342928 + 913)]%Z m0 mj -> wmono psegs m0 mj ->
    evt psegs (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 342920) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x165cc) fc None m' (seg_rom psegs)
      /\ munch [(342928 + 848, 342928 + 913)]%Z m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 342920) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x165c4) fc None mj (seg_rom psegs))).
  { intros mj stj ns NS MRj CTj MIj MUj WMj.
    pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (342928 + 912) with 343840 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at psegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (342920 + 920)) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    (* [comment removed for export] *)
    step. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    rraw_store_finish0 (342928 + 912) [b8 ns] MUj WMj SOK.
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned q) by lia.
    eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr psegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
    pose proof (munch_refl [(342928 + 848, 342928 + 880)]%Z m) as MUz. pose proof (wmono_refl psegs m) as WMz.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (UZ : u8arr psegs mX 343776 (zeros 32));
    [ apply (u8arr_of_rw_cells psegs mX 343776 32);
      lazymatch goal with H : rw_cells psegs mX 343776 _ |- _ =>
        apply (rw_cells_congr psegs mX 343776 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells, RCTX in C6.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono psegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRz : rmrep stz mX);
    [ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia];
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
    | clear MUc WMc ] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono psegs m0 ?mX, MIc : mem_inv psegs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed.
(* [comment removed for export] *)
Lemma rmm_seq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
  mem_inv psegs m ->
  evt psegs (fun ms' => exists (t0' t1' a3' a6' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 (Z_to_bv 64 31) a6' a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x165cc) fc None m' (seg_rom psegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch rseqW m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ rmrep (step_seq (account_bounce sc st)) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162ec) fc None m (seg_rom psegs)).
Proof using SC.
  intros until m. intros MR SEQ BR USR MI.
  eapply evt_cut; [eapply rbounce_walk; eassumption|].
  cbv beta. intros ms' (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR').
  assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
  { unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
    destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
  rewrite <- SEQ'.
  eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
  cbv beta. intros ms'' (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'').
  do 6 eexists. split; [reflexivity|]. subst a3'.
  repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.


End CeilWrap.
End RASlot_W15.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W11.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W16.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module RASlot_W16.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W11 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W16.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

(* [comment removed for export] *)
Definition rmmc_post (ra sp gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (res : Z * Z) : machine_state -> Prop :=
  fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (wz (snd res)) s4 s5 s6 s7 s8 (wz (fst res)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x166b0) fc None m (seg_rom psegs).

(* [comment removed for export] *)
Lemma rj2c_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc m (c1 u1 : Z),
  1 <= c1 <= 32 -> 0 <= u1 < 2^61 ->
  evt psegs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 s6 s7 (wz size) s10 s11 t3 t4 t5 t6 F fc m
               (mm_final size req u1 c1 nos))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) a4 a5 a6 a7
             (Z_to_bv 64 req) s3 s4 s5 s6 s7 (wz size) (wz c1) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16654) fc None m (seg_rom psegs)).
Proof using RQ SZ.
  intros until u1. intros CR UR.
  assert (SCR : 16 <= size * c1 < 2^24) by nia.
  pose proof (zb_b2z_range nos) as NR.
  unfold rmmc_post.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned size), (wz_unsigned c1) by lia.
  step. step. step. step. step. step.
  rewrite !land_4095_word. rewrite ?(unsigned_lit (size * c1)) by lia.
  replace (-16 + - (size * c1)) with (- (size * c1 + 16)) by lia.
  set (nd0 := round_up_pg (size * c1 + 16)).
  pose proof (round_up_pg_alt (size * c1 + 16)) as RU. pose proof (round_up_pg_range (size * c1 + 16) ltac:(lia)) as RUR.
  replace (size * c1 + Z.land (- (size * c1 + 16)) 4095 + 16) with nd0 by lia.
  fold nd0 in RUR.
  assert (EF : mm_final size req u1 c1 nos = (if negb nos && (c1 <=? 7) then mm_small size req u1 c1 nd0 else (c1, nd0))).
  { unfold mm_final, UNIT. reflexivity. }
  (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
  { (* [comment removed for export] *)
    apply evt_done. rewrite EF. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]). cbn [negb andb fst snd].
    do 9 eexists. reflexivity. }
  replace nos with false in EF |- * by (destruct nos; cbn in KN; [lia| reflexivity]). cbn [negb andb] in EF.
  (* [comment removed for export] *)
  step. step. if_cases K7; zify_cond K7; rewrite ?(wz_unsigned c1), ?unsigned_lit in K7 by lia.
  { (* [comment removed for export] *)
    apply evt_done. rewrite EF. replace (c1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
    do 9 eexists. reflexivity. }
  replace (c1 <=? 7) with true in EF by (symmetry; apply Z.leb_le; lia).
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (Z.land_comm 4095), land_4095_word. rewrite ?(unsigned_lit req) by lia.
  replace (-20 + - req) with (- (req + 20)) by lia.
  set (rq' := round_up_pg (req + 20)).
  pose proof (round_up_pg_alt (req + 20)) as RU2. pose proof (round_up_pg_range (req + 20) ltac:(lia)) as RUR2.
  replace (req + Z.land (- (req + 20)) 4095 + 20) with rq' by lia. fold rq' in RUR2.
  assert (ES : mm_small size req u1 c1 nd0 = (if (rq' <? size + 16) || ((4 * PGSZ <=? rq') && (u1 <? 2 * c1)) then (1, rq') else (c1, nd0))).
  { unfold mm_small, IB, UNIT. replace (req + 4 + 16) with (req + 20) by lia. reflexivity. }
  rewrite ES in EF. clear ES. unfold PGSZ in EF. 
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (size + 16)), ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    replace (rq' <? size + 16) with false in EF by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in EF.
    step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
    step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + (* [comment removed for export] *)
      apply evt_done. rewrite EF. replace (4 * 4096 <=? rq') with false by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd].
      do 9 eexists. reflexivity.
    + replace (4 * 4096 <=? rq') with true in EF by (symmetry; apply Z.leb_le; lia). cbn [andb] in EF.
      (* [comment removed for export] *)
      step. rewrite (wz_unsigned c1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite swrap32_small by lia.
      step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned u1), ?unsigned_lit in K3 by lia.
      * (* [comment removed for export] *)
        step. step. step.
        apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
        do 9 eexists. reflexivity.
      * apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
        do 9 eexists. reflexivity.
  - (* [comment removed for export] *)
    replace (rq' <? size + 16) with true in EF by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in EF.
    step. step. step.
    apply evt_done. rewrite EF. cbn [fst snd]. do 9 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rred_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (cnt u1 : Z),
  1 <= cnt <= 32 -> 0 <= u1 < 2^61 ->
  evt psegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
      ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
                   (Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x16654) fc None m (seg_rom psegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5 a6 a7
             (Z_to_bv 64 req) (wz cnt) s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x165e0) fc None m (seg_rom psegs)).
Proof using SC SZ.
  intros until u1. intros CR UR.
  assert (SCR : 16 <= size * cnt < 2^24) by nia.
  pose proof (zb_b2z_range nos) as NR. pose proof (ASlot_W16.land3_range sc) as L3.
  (* [comment removed for export] *)
  assert (J28 : forall (a5' a6' a7' t0' s9' : word) (c : Z), c = mm_cnt_red sc size cnt u1 nos ->
    evt psegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
      ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
                   (Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x16654) fc None m (seg_rom psegs))
    (MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
             (Z_to_bv 64 req) (wz c) s4 s5 s6 s7 (wz size) s9' s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16650) fc None m (seg_rom psegs))).
  { intros a5' a6' a7' t0' s9' c ->. step. apply evt_done. do 5 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2, swrap32_small by lia. change (2 ^ 2) with 4.
  step. if_cases KU; zify_cond KU; rewrite ?(wz_unsigned u1), ?unsigned_lit in KU by lia.
  { eapply J28. unfold mm_cnt_red. replace (u1 <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
  { eapply J28. unfold mm_cnt_red. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]).
    rewrite Bool.andb_false_r. reflexivity. }
  assert (EN : nos = false) by (destruct nos; cbn in KN; [lia| reflexivity]).
  assert (ER : mm_cnt_red sc size cnt u1 nos =
    (if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
     else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
     else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
     else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
     else cnt)).
  { unfold mm_cnt_red. rewrite EN. replace (u1 <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  unfold PGSZ in ER.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 3) with 32768.
  step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
  - (* [comment removed for export] *)
    replace (Z.land sc 3 =? 1) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
    step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
    + (* [comment removed for export] *)
      replace (Z.land sc 3 =? 2) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
      (* [comment removed for export] *)
      step. step. step.
      step. if_cases KC; zify_cond KC.
      * (* [comment removed for export] *)
        rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
        destruct (Z.ltb_spec (Z.land sc 3) 1) as [A1|A1]; destruct (Z.ltb_spec 32768 (size * cnt)) as [LT|GE]; cbn [Z.b2z Z.land] in KC; try (exfalso; apply KC; reflexivity); [].
        assert (E0 : Z.land sc 3 = 0) by lia.
        step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [exfalso; lia|].
        step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [| exfalso; lia].
        apply evt_done. rewrite ER, E0. cbn [Z.eqb andb]. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
        do 5 eexists. reflexivity.
      * (* [comment removed for export] *)
        assert (NC : ~ (Z.land sc 3 = 0 /\ 32768 < size * cnt)).
        { intros [E0 LT]. rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
          replace (Z.land sc 3 <? 1) with true in KC by (symmetry; apply Z.ltb_lt; lia).
          replace (32768 <? size * cnt) with true in KC by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z true)) with 1 in KC. lia. }
        clear KC. step. step.
        step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
        { (* [comment removed for export] *)
          apply evt_done. rewrite ER. replace (Z.land sc 3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
          do 5 eexists. reflexivity. }
        rewrite KD in ER |- *. cbn [Z.eqb andb] in ER.
        replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia).
        (* [comment removed for export] *)
        step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [exfalso; lia|].
        step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 1) with 8192.
        step. if_cases KQ; zify_cond KQ; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KQ by lia.
        -- eapply J28. rewrite ER. replace (2 * 4096 <? size * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        -- step. eapply (J28 _ _ _ _ _ 5). rewrite ER. replace (2 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + (* [comment removed for export] *)
      rewrite KB in ER |- *. cbn [Z.eqb andb] in ER.
      step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
      step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
      * (* [comment removed for export] *)
        replace (4 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
        step. step. step.
        step. if_cases KG; zify_cond KG.
        { exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
        clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
        apply evt_done. rewrite ER. do 5 eexists. reflexivity.
      * (* [comment removed for export] *)
        step. step. apply evt_done. rewrite ER. replace (4 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
        do 5 eexists. reflexivity.
  - (* [comment removed for export] *)
    rewrite KA in ER |- *. cbn [Z.eqb andb] in ER.
    step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
    + (* [comment removed for export] *)
      replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
      step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
      step. step. step.
      step. if_cases KG; zify_cond KG.
      { exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
      clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
      apply evt_done. rewrite ER. do 5 eexists. reflexivity.
    + (* [comment removed for export] *)
      step. step. apply evt_done. rewrite ER. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      do 5 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rusage1_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (u0 : Z),
  rmrep st m -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
  evt psegs (fun ms' => exists (a5' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz (mm_usage1 st sc u0)) a1 a2 a3 a4 a5' a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x165e0) fc None m (seg_rom psegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) a1 a2 a3 a4 (Z_to_bv 64 31) a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x165cc) fc None m (seg_rom psegs)).
Proof using SC.
  intros until u0. intros MR UR USR. unfold RMLOCK, RCTX in *.
  pose proof (land_upper sc 1 ltac:(lia) ltac:(lia)) as L1R.
  (* [comment removed for export] *)
  step. if_cases K; unfold bv_lts in K; rewrite !signed_lit_small in K by lia.
  { apply Z.ltb_lt in K. apply evt_done. unfold mm_usage1. replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
    eexists. reflexivity. }
  apply Z.ltb_ge in K.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia.
  step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit (Z.land sc 1)) in KO by lia.
  { (* [comment removed for export] *)
    assert (ODD : Z.even sc = false).
    { rewrite even_of_land1. apply Z.eqb_neq. exact KO. }
    apply evt_done. unfold mm_usage1. rewrite ODD. cbn [andb]. eexists. reflexivity. }
  assert (EV : Z.even sc = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact KO).
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read st m (sc + 1) (wa (342928 + 464 + 8 * (sc + 1))) MR ltac:(lia) eq_refl) as RDU.
  replace (wa (342928 + 464 + 8 * (sc + 1))) with (Z_to_bv 64 (342920 + 8 * sc + 480)) in RDU by (unfold wa; f_equal; lia).
  pose proof (USR (sc + 1)) as U1R.
  step. clear RDU. step. rewrite (wz_unsigned (usage st (sc + 1))), (wz_unsigned u0) by lia.
  apply evt_done. unfold mm_usage1. rewrite EV. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  eexists. unfold wz. rewrite (Z.add_comm (usage st (sc + 1)) u0). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rmmc_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a6 a7 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (cnt u0 : Z),
  rmrep st m -> 1 <= cnt <= 32 -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
  evt psegs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (wz size) s10 s11 t3 t4 t5 t6 F fc m
               (mm_final size req (mm_usage1 st sc u0) (mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos) nos))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) (Z_to_bv 64 31) a6 a7
             (Z_to_bv 64 req) (wz cnt) s4 s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (wz size) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x165cc) fc None m (seg_rom psegs)).
Proof using RQ SC SZ.
  intros until u0. intros MR CR UR USR.
  assert (U1R : 0 <= mm_usage1 st sc u0 < 2^61).
  { unfold mm_usage1. pose proof (USR (sc + 1)). destruct (_ && _); lia. }
  eapply evt_cut. { eapply (rusage1_walk _ _ _ _ t0 t1 t2 s1); [exact MR| exact UR| exact USR]. }
  cbv beta. intros ms' (a5' & ->).
  eapply evt_cut. { eapply (rred_walk _ _ _ _ t0 t1 t2 s1); [exact CR| exact U1R]. }
  cbv beta. intros ms'' (a5'' & a6'' & a7'' & t0'' & s3'' & ->).
  assert (CRR : 1 <= mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos <= 32).
  { unfold mm_cnt_red. destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia. }
  eapply evt_mono. { eapply rj2c_walk; [exact CRR| exact U1R]. }
  cbv beta. unfold rmmc_post. intros ms3 (t0x & a0' & a1' & a2' & a3' & a4' & a5x & a6x & a7x & ->).
  do 9 eexists. reflexivity.
Qed.
End MMC.


End CeilWrap.
End RASlot_W16.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_malloc_bigw.
Module RASlot_W17.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W17.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RF_ntf_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_bigw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac step ::= step1.  Local Ltac stepz ::= step1.  (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma rmm_call_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt psegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x166d0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) s3 (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                   (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom psegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x166b0) fc None m (seg_rom psegs)).
Proof using .
  intros. unfold rmmap_entry.
  step. step. step. step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rmm_ret_fail_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt psegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x167f8) fc None m (seg_rom psegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x166d0) fc None m (seg_rom psegs)).
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
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

(* [comment removed for export] *)
Lemma rmm_ret_ok_walk :
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) F fc m,
  rmrep st2 m -> mem_inv psegs m ->
  evt psegs (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x16728) fc None m' (seg_rom psegs)
      /\ munch [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x166d0) fc None m (seg_rom psegs)).
Proof using CNT CR HC MST ND NDA REC SC SZ XA XA2.
  intros until m. intros MR MI.
  pose proof (munch_refl [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold alloc_ceiling, RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
  clear K.
  (* [comment removed for export] *)
  step.
  rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
  rmeta_open G MUa WMa.
  step.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
  step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
  rewrite (divu_word 4080 size) by lia.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
  set (d := 4080 / size) in *.
  (* [comment removed for export] *)
  pose proof MR as (_ & (CX1 & _) & _). unfold rctx_head_cells in CX1. rewrite HC in CX1. unfold RCTX in CX1.
  step. rewrite (sx32_wz_sxv c) by lia.
  (* [comment removed for export] *)
  step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
  step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).
  (* [comment removed for export] *)
  assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
  { unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
    change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia. }
  step.
  lazymatch goal with H : rw_cells psegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
    [ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tclose];
      unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
    | clear MUa WMa H ] end.
  set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.
  (* [comment removed for export] *)
  pose proof (rw_cells_store_ok_at psegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (342920 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
  clear CX1.
  st1.
  rewrite le4_swrap_succ by lia.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold RCTX in MR4 end.
  clear MR3.
  rraw_store_finish0 (342928 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
  assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
  { unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
  rewrite <- E4 in MR4.
  assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
    evt psegs (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 342920) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x16728) fc None m' (seg_rom psegs)
      /\ munch [(G, G + 40); (342928 + 12, 342928 + 16)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 342920) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16714) fc None mX (seg_rom psegs))) end.
  { intros a2v mn Hmn ->.
    assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).
    (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
    eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End MMOK.


End CeilWrap.
End RASlot_W17.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_malloc_core.
Module RF_malloc_big.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15.F_malloc_bigw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14.F_malloc_big OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_bigw.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Lemma rmrep_ext : forall st st' m,
  rmrep st m ->
  s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
  s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_reserved st' = s_reserved st ->
  rmrep st' m.
Proof using .
  intros st st' m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact EA| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof using G0.
  unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
  rewrite G0. reflexivity.
Qed.

Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof using n rid.
  intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof using c st3. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof using c n rid.
  intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma rbf_regions : s_regions stF = s_regions st3. Proof using g n rid. reflexivity. Qed.
Lemma rbf_areas : s_areas stF = s_areas st3. Proof using g n rid. reflexivity. Qed.
Lemma rbf_reserved : s_reserved stF = s_reserved st3. Proof using g n rid. reflexivity. Qed.
Lemma rbf_next : s_next_rid stF = s_next_rid st3. Proof using g n rid. reflexivity. Qed.
Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof using GN n.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite GN. reflexivity.
Qed.
Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof using c n. reflexivity. Qed.
Lemma rbf_shadow q : get_shadow stF q = get_shadow stM q.
Proof using c g n rid st3. reflexivity. Qed.
Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma rbf_ctx : ctx stF = ctx stM.
Proof using HC g n rid. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof using HC stM. rewrite rbf_ctx. reflexivity. Qed.

Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof using G0 GN HC n.
  intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
  - exact rbf_ctx.
  - intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by exact NE; reflexivity].
  - rewrite rbf_groups, rbm_groups. reflexivity.
Qed.

Lemma rticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. intros H; exact H. Qed.

(* [comment removed for export] *)
Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof using NR.
  unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
  replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
  cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof using n.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
  unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

(* [comment removed for export] *)
Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
  a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x55000 <= a).
Proof using .
  intros MR RF. pose proof MR as (WF & _). (nelimp WF 3%nat; intros _ WR _).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
  - lia. - lia. - lia. - lia.
  - (nelim (rarea_conc st ak ar WF Hak) 10%nat; intros ra Hra Ca Sa0 Sa1 _ NK RB0 RBAL RBC).
    (nelim (WR _ _ Hra) 5%nat; intros _ _ _ _ RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold alloc_ceiling in RBC.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - (nelim (rgroup_conc st b gh WF Hb) 9%nat; intros rb Hrb Cb Kb Sb0 Sb1 _ RB0 RBC).
    (nelim (WR _ _ Hrb) 5%nat; intros _ _ _ _ RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold alloc_ceiling in RBC.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - (nelim (WR _ _ Hq) 5%nat; intros _ _ _ RC RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold alloc_ceiling in RC. lia.
  - lia. - lia.
Qed.

(* [comment removed for export] *)
Lemma rwrapper_munch_keeps st m m' (spv lo : Z) :
  rmrep st m -> munch [(spv - 80, spv); (0x337ec, 0x337ec + 4)] m m' -> wmono psegs m m' -> alloc_ceiling <= spv - 80 ->
  rmrep st m'.
Proof.
  intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
  intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; lia.
Qed.

Lemma rpres_except_of_munch_nw C W m m' :
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
  intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. unfold wview. rewrite E. auto.
Qed.

(* [comment removed for export] *)
Lemma rfp_below_ceiling K st3 stx m lo spv a :
  rmrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (ralloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof.
  intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try heap_lia_pruned.
  - rewrite unsigned_lit in X by lia. unfold alloc_ceiling in H2. lia.
  - unfold RCTX, alloc_ceiling in *. lia.
  - pose proof MR as (WF & _). (nelimp WF 3%nat; intros _ WR _). (nelim (WR q rq Hq) 5%nat; intros _ _ _ RC _). lia.
Qed.

Lemma rbig_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof using . intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

Lemma rregion_facts_hi : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  r_base r + round_up_pg (r_len r) <= 0x23000 \/ 0x55000 <= r_base r.
Proof.
  intros st m rid r (WF & _) Hr. (nelimp WF 3%nat; intros _ WR _).
  (nelim (WR rid r Hr) 5%nat; intros RB0 RBAL RL0 RBC RFr).
  (nelim (rreserved_disjoint _ _ RFr) 4%nat; intros _ _ _ D). exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
  forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
  mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
  ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).


Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved).
Proof using .
  intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (MallocFacts_inv4.areach_ampre_proof _ _ AR)|].
  unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

Lemma rbig_spec : rbig_stmt.
Proof using AM AMP.
  pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
  intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
  intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
  rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).
  (* [comment removed for export] *)
  riprefixT. unfold alloc_ceiling in CLO. subst tp. unfold RATP in ERR1. rewrite unsigned_lit in ERR1 by lia.
  unfold RMLOCK.
  step. step. step. step. step. step. step. step. step.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST1 | unfold RATP; rewrite unsigned_lit by lia; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
    | reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | rewrite F_mm_syscalls.alloc_ceiling_val; lia
    | rewrite SP'; unfold RATP; rewrite unsigned_lit by lia; lia | unfold RATP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (211088 + -164, 211088 + -164 + 4)] m1 m2 -> wmono psegs m1 m2 ->
            rw_cells psegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
  { intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
    - eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| unfold alloc_ceiling; lia].
      eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
    - eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    - eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch; [exact MU| exact WM|].
      intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia.
    - eapply unk_agree_munch; [exact UA1| exact MU| |].
      + intros rid r Hr Hk. (nelimp (rregion_facts st1 m1 rid r MR1 Hr) 4%nat; intros R1 _ R2 _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. unfold alloc_ceiling in R2. cbn. lia.
      + intros rid r Hr. (nelimp (rregion_facts st1 m1 rid r MR1 Hr) 4%nat; intros R1 _ R2 _). unfold alloc_ceiling in R2. lia. }
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (nelim PO 22%nat; intros v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 m2 -> MU2 WM2 MI2 ST2 ERR2 He).
    cbn [mmap_val]. destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e He) as [-> ->]. cbn [negb].
    apply rimplT_ret.
    unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
    (nelim (FRAME m2 MU2 WM2) 5%nat; intros FR2 MR2 AUX2 PE2 UA2).
    replace (ret_pc (Z_to_bv 64 0x15d48)) with (Z_to_bv 64 0x15d48) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    eapply evt_cut. { eapply rbig_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
    intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
    exists m2, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). nexists 14%nat. split; [reflexivity|].
    split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
    split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR2|]. split; [exact AUX2|]. split; [exact PE2|].
    split; [apply mrel_same; reflexivity|]. split; [exact BL|]. repeat split; reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (nelim PO 22%nat; intros v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 m2 -> MU2 WM2 MI2 ST2 ERR2 AOK).
    cbn [mmap_val].
    destruct (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
    2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    (nelim (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) 5%nat; intros X0 XA XC XRF ISE). rewrite ISE.
    unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
    (nelim (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) 5%nat; intros FR2 MR2 AUX2 PE2 UA2).
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
    assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
    pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) st1).
    { eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
    set (L := mmap_len (n + IB + UNIT)).
    assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
    pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
    unfold F_mm_syscalls.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
    assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. unfold alloc_ceiling in XC. unfold IB, UNIT in LG.
    set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : rmrep st2 mz).
    { rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
        rewrite <- ?EL; [unfold alloc_ceiling; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    fold mz in ST2 |- *.
    (* [comment removed for export] *)
    pose proof MR1 as (WF1 & _). (nelimp WF1 3%nat; intros RS1 WR1 _).
    assert (XI : xa + L <= 0x10000 \/ 0x55000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa L = true).
      { apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv psegs mz).
    { unfold mz. apply (mem_inv_zeros psegs m2 xa L); try heap_lia_pruned; [exact MI2 | intros w Hw; apply ref_ro_addr_false; heap_lia_pruned | unfold TASK_SIZE; pose proof (@ceil_hi ACEIL); unfold alloc_ceiling in *; heap_lia_pruned]. }
    assert (FRz : rw_cells psegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
    { eapply rrw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
    assert (UAz : unk_agree st2 o mz).
    { eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
      rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
      - right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
        unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
      - left. split; [exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; exact X|].
        intros off h Ho Hc NG. (nelim (WR1 q r Hq1) 5%nat; intros B0 _ _ BC _). unfold alloc_ceiling in BC.
        pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
        pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; lia. }
    (* [comment removed for export] *)
    riprefixT.
    replace (ret_pc (Z_to_bv 64 0x15d48)) with (Z_to_bv 64 0x15d48) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (mf_ctx _ _ MF) as FC. (nelim FC 6%nat; intros FC1 FC2 FC3 FC4 FC5 FC6).
    change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
    eapply evt_cut.
    { eapply (rbig_seq_walk sp gp (Z_to_bv 64 211088)) with (st := st2) (lo := lo);
        [exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| unfold alloc_ceiling; lia| exact MIz]. }
    intros ms1 nelH_; (nelim nelH_ 10%nat; intros wa0 wa1 m3 -> MU3 WM3 MI3 ST3 FR3 MR3).
    apply evt_done.
    (* [comment removed for export] *)
    assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono psegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono psegs m2 xa L); try heap_lia_pruned; exact Hw).
    assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUX2| exact MUz| exact WMz|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUXz| exact MU3| exact WM3|]. unfold RAUXV_CELL, RCTX.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
    assert (ERRz : rw_cells psegs mz (211088 + -164) [C4 errv]).
    { eapply rrw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (ERR3 : rw_cells psegs m3 (211088 + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold RCTX. cbn. lia. }
    assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; exact Hq).
    assert (BL2 : brk_link_ps (step_seq st2) s).
    { eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
      intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      apply Hconc2. cbn. (nelim PT1 8%nat; intros _ _ _ _ _ _ P7 _). rewrite Hb in P7. exact P7. }
    assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
    eapply AM.
    { apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
    { exact MR3. }
    { exact TK2'. }
    { exact BL2. }
    { rewrite SP'. eapply rauxv_ok_weaken; [exact AUX3| unfold alloc_ceiling; lia]. }
    { rewrite SP'. exact ST3. }
    { unfold alloc_ceiling; lia. }
    { rewrite SP'. unfold RAM_STACK. lia. }
    { unfold RATP. rewrite unsigned_lit by lia. exact ERR3. }
    { exact MI3. }
    { reflexivity. }
    intros st3 mo s' ms' PO3 BL3.
    (nelim PO3 28%nat; intros u0 u1 u2 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 m4 errv4 -> MI4 ST4 ERR4 AUX4 PE4 MR4 TK4 PSM PSF PSO REL).
    rewrite SP' in ST4, AUX4, PE4. unfold RATP in ERR4. rewrite unsigned_lit in ERR4 by lia.
    replace (ret_pc (Z_to_bv 64 0x15e3c)) with (Z_to_bv 64 0x15e3c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells psegs m4 (bv_unsigned sp + -48) cs) end.
    { eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [exact MR4| lia| unfold alloc_ceiling; lia]. }
    assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
    assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { (nelim (amr_regions _ _ _ REL rid _ RR2) 6%nat; intros r' Hr' K' B' L' G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
    assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
    assert (PT3 : ptrs_in (fun q => q <> rid) st3).
    { apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
    pose proof MR4 as (WF4 & _ & (ML4 & _) & _). (nelimp WF4 4%nat; intros RS4 WR4 DJ4 _).
    assert (RS3 : s_reserved st3 = ref_reserved) by exact RS4.
    (* [comment removed for export] *)
    assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
              (forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
              rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
    { intros stF RSF HFP.
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
        do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold RCTX in *.
        split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold RCTX; lia| right; right; left; unfold RCTX; lia]. }
      eapply rpres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
      do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |exact X].
      { transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
      intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
      transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      rewrite Est2, rnr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
    destruct mo as [g|].
    + (* [comment removed for export] *)
      apply rimplT_ret.
      destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
      pose proof (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
      set (G := conc st3 g) in *.
      assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; unfold alloc_ceiling in GC; lia).
      assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
      { intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
        (nelim PT3 10%nat; intros _ _ _ _ _ _ _ _ _ P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
      { intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
        (nelim PT3 10%nat; intros _ _ _ _ _ _ _ _ P9 _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (SHN3 : (s_shadow st3) !! rid = None).
      { rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. exact FRs. }
      assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
      { rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. reflexivity. }
      eapply evt_cut.
      { eapply (rbig_succ_walk st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(unfold alloc_ceiling; lia) sp gp (Z_to_bv 64 211088));
          [exact HG| exact FR4| exact ST4| lia| exact MI4]. }
      intros ms5 nelH_; (nelim nelH_ 11%nat; intros a0' a1' m7 -> MU7 WM7 MI7 ST7 FR7 MR7 TK7).
      apply evt_done. cbn [rcoreQ].
      set (stF := big_final st3 g rid n).
      rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
      change (pw st3 (Some g)) with (pw stF (Some g)).
      exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. nexists 17%nat.
      split; [reflexivity|].
      assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
      split; [exact MRF|].
      split; [exact TK7|].
      assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
      assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
      { intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
      split.
      { (* [comment removed for export] *)
        assert (UA3 : unk_agree (step_seq st2) o m3).
        { eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
          assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
          split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          intros off h Ho Hc NG. pose proof MRz as (WFz & _). (nelimp WFz 3%nat; intros _ WRz _).
          (nelim (WRz q r Hq2) 5%nat; intros B0 _ _ BC RFq). (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). unfold alloc_ceiling in BC.
          apply MU3. rewrite wa_unsigned by lia. cbn. unfold RCTX. lia. }
        assert (UA4 : unk_agree st3 o m4).
        { eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
          assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
          { destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
            - (nelim (amr_regions _ _ _ REL q r2 E) 6%nat; intros r' Hr' K' _ _ G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
            - exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
          split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
          intros off h Ho Hc NG. (nelim (WR4 q r Hq) 5%nat; intros B0 _ _ BC RFq). unfold alloc_ceiling in BC.
          refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
          intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
          - lia.
          - rewrite unsigned_lit in X by lia. (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). lia.
          - unfold RCTX in X. (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). lia.
          - assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
            pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
          - pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). lia. }
        eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
        destruct (N.eq_dec q rid) as [->|NE].
        - right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
          change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
          rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
          exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
        - left. split; [exact Hq|]. split; [apply rbf_shadow_other; exact NE|].
          split. { intros off nelH_; (nelim nelH_ 5%nat; intros b gh Hb Hf Ho). exists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
                   rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
          intros off h Ho Hc NG. (nelim (WR4 q r Hq) 5%nat; intros B0 _ _ BC RFq). (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). unfold alloc_ceiling in BC.
          pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
          apply MU7; rewrite wa_unsigned by lia; cbn; unfold RCTX; lia. }
      split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
      assert (ERR8 : rw_cells psegs m7 (211088 + -164) [C4 errv4]).
      { eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold RCTX. lia. }
      split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR8|].
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
      assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
      { eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_trans.
        { eapply rpres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
          - left. right; right; right. exists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
          - do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
          - left. right; right; left. unfold RCTX in *. lia. }
        apply rpres_except_refl. }
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| unfold alloc_ceiling; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          (nelim (amr_regions _ _ _ REL q rq Hq2) 6%nat; intros r' Hr' K' B' L' _).
          exists r'. split; [|repeat split; auto]. exact Hr'.
        - change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE18]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
      split. { intros a Ha. do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      split. { unfold u32. Z.div_mod_to_equations. lia. }
      assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by lia; Z.div_mod_to_equations; lia).
      pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
      assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; lia).
      rewrite <- big_ml_eq in RU by lia.
      split.
      { (* [comment removed for export] *) constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
        - reflexivity.
        - exact RR3.
        - reflexivity.
        - lia.
        - reflexivity.
        - lia.
        - lia.
        - rewrite <- EL. lia.
        - lia.
        - rewrite RU. Z.div_mod_to_equations. lia.
        - lia.
        - lia.
        - lia.
        - intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
          destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
          rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
        - change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
          rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - intros off Ho Hfit. Z.div_mod_to_equations. lia.
        - unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
        - exact MSL.
        - lia.
        - lia.
        - lia.
        - lia.
        - right. repeat split; lia. }
      split. { intros _. unfold F_malloc_enframe.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
               cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      split; [exact MRELF|].
      split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
      repeat split; assumption.
    + (* [comment removed for export] *)
      cbn [pw oconc].
      riprefixT.
      eapply evt_cut.
      { apply rbig_fail2a_walk. exact ML4. }
      intros ms2 ->. apply evt_done.
      eapply rimplT_munmap.
      { eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
          [ rewrite unsigned_lit by lia; exact ST4 | rewrite unsigned_lit by lia; exact ERR4 | exact MI4 | reflexivity | unfold IB, UNIT; f_equal; lia
          | lia | rewrite ELm; lia | unfold IB, UNIT; lia | rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; rewrite unsigned_lit by lia; lia | rewrite ELm; left; unfold alloc_ceiling in *; lia
          | rewrite ELm, unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ]. }
      intros ans2 ms3 PM. unfold rmunmap_post in PM.
      (nelim PM 22%nat; intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m6 -> MU6 WM6 MI6 ST6 ERR6 He6).
      rewrite (munmap_answer_ok_range ans2 He6). apply rimplT_ret.
      rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
      replace (ret_pc (Z_to_bv 64 0x15f14)) with (Z_to_bv 64 0x15f14) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells psegs m6 (bv_unsigned sp + -48) cs) end.
      { eapply rrw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. unfold alloc_ceiling in *. lia. }
      eapply evt_cut. { eapply rbig_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
      intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
      set (stF := drop_region rid st3).
      assert (MRF : rmrep stF m6).
      { eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
        rewrite <- EL in Hout.
        assert (A1 : a < alloc_ceiling /\ (a + 1 <= 211088 + -164 \/ 211088 + -164 + 4 <= a) /\ (a < xa \/ xa + L <= a)).
        { destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
            [unfold RMLOCK, alloc_ceiling in *; lia| unfold RLIBC, alloc_ceiling in *; lia| unfold RGOT_SSP, alloc_ceiling in *; lia| unfold RSSP_GUARD, alloc_ceiling in *; lia|].
          (nelim (WR4 q rq Hq) 5%nat; intros _ _ _ RC RFq). (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). pose proof (lr_lo_ge rq).
          split; [lia|]. split; [lia|].
          destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
          destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
        unfold alloc_ceiling in A1.
        apply MU6; rewrite wa_unsigned by lia; cbn; lia. }
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [|split; [exact Kq|exact Xa]].
        unfold stF. rewrite rdr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
      assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
      { eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
        split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; rewrite unsigned_lit by lia; lia|].
        do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      exists m6, (F_mm_syscalls.rg_errno ans2 errv4). nexists 14%nat. split; [reflexivity|].
      split; [exact MRF|]. split; [apply rticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
      split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR6|].
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| unfold alloc_ceiling; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          (nelim (amr_regions _ _ _ REL q rq Hq2) 6%nat; intros r' Hr' K' B' L' _).
          exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by exact NE. exact Hr'.
        - unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
          change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE16]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      split; [exact MRELF|].
      split.
      { eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
        (nelim PT3 8%nat; intros _ _ _ _ _ _ P7 _). rewrite Hb in P7. exact P7. }
      repeat split; assumption.
Qed.
End BIG.


End CeilWrap.
End RF_malloc_big.

(* [comment removed for export] *)
Module RASlot_M4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W11 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W16 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W17 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W18 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M4P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15.F_malloc_bigw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14.F_malloc_big.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W11 RASlot_W14 RASlot_W15 RASlot_W16 RASlot_W17 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W18 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W19 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_M2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3 RASlot_M5D RASlot_M5F RASlot_M5S RF_malloc_big.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rhmm_ok : rHMM_stmt k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof using A1 AR AUX CLO ER FIT HK LO MR RQ SC TP.
  clear A0 F0 IS AC TK UA BL ST MI ERR.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R BIGc.
  (nelim CT 23%nat; intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2) as URall. change (fact_usage (strip st2)) with (fact_usage st2) in URall.
  (nelimp (mf_ctx _ _ MF2) 6%nat; intros FC1 FC2 FC3 FC4 FC5 FC6).
  change (ctx (strip st2)) with (ctx st2) in FC1, FC2, FC3, FC4. change (bounces (strip st2)) with (bounces st2) in FC5. change (unmap_seq (strip st2)) with (unmap_seq st2) in FC6.
  pose proof (size_class_range sc SC) as SZR.
  unfold rcnt_state.
  replace (size_class sc * UNIT * cnt1) with (UNIT * size_class sc * cnt1) by lia.
  replace (size_class sc * UNIT) with (UNIT * size_class sc) by lia.
  set (size := UNIT * size_class sc) in *.
  assert (SZ : 16 <= size < 2^18) by (subst size; unfold UNIT; lia).
  rewrite A1. rewrite (ag_mmap_eq sc req k bail st2 mm cnt1).
  set (stS := step_seq (account_bounce sc st2)).
  set (nos := is_bouncing sc st2).
  set (u1 := mm_usage1 stS sc (usage st2 sc)).
  set (cR := mm_cnt_red sc size cnt1 u1 nos).
  assert (CRR : 1 <= cR <= 32) by (subst cR; apply mm_cnt_red_range; exact C1R).
  destruct (mm_final size req u1 cR nos) as [c nd] eqn:EF.
  (nelim (mm_final_props size req u1 cR nos c nd CRR ltac:(lia) ltac:(lia) ltac:(subst size; unfold UNIT; lia) EF) 4%nat; intros CR NDM NDR NDC).
  assert (NDB : 16 <= nd < 2^40).
  { pose proof (round_up_pg_props (req + 20) ltac:(lia)). pose proof (round_up_pg_props (size * c + 16) ltac:(apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia| lia])).
    assert (size * c <= 2^18 * 32) by (apply Z.mul_le_mono_nonneg; lia). destruct NDC as [[Ec En]|[LE En]]; rewrite En; lia. }
  cbv beta iota.
  (* [comment removed for export] *)
  riprefixT.
  eapply evt_cut. { eapply (rmm_seq_walk sc SC); [exact MR3| exact FC4| exact FC5| exact FC6| exact MI3]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 12%nat; intros u0 u1' wa3 wa6 wa7 m4 -> -> MU4 WM4 MI4 MR4).
  fold nos stS in MR4 |- *.
  (* [comment removed for export] *)
  (nelim (stS_shape sc st2) 3%nat; intros fS ES HS). fold stS in ES.
  assert (US : forall i, usage stS i = usage st2 i) by (intros i; unfold usage; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (proj2 (HS _))); reflexivity).
  eapply evt_cut.
  { replace (wz (size + 16)) with (wz (size + 16)) by reflexivity.
    eapply (rmmc_walk sc size req nos SC SZ RQ) with (st := stS) (m := m4); [exact MR4| exact C1R| apply URall| intros i; rewrite US; apply URall]. }
  cbv beta. unfold rmmc_post. intros ms' nelH_; (nelim nelH_ 10%nat; intros v0 va0 va1 va2 va3 va4 va5 va6 va7 ->).
  fold u1. fold cR. rewrite ?EF. cbn [fst snd].
  (* [comment removed for export] *)
  assert (FR4 : rw_cells psegs m4 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [exact FR3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ST4 : stk psegs m4 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ERR4 : rw_cells psegs m4 (errno_addr tp) [C4 errv']).
  { eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4|]. rewrite EA. unfold rseqW, RCTX. cbn. lia. }
  assert (PE04 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4).
  { eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_of_munch; [exact MU4| exact WM4|].
    intros a Ha NC. unfold rseqW. cbn. split; [|exact I]. intros X. apply NC. left. right. right. left. unfold RCTX in *. lia. }
  assert (AUX4 : rauxv_ok m4 (bv_unsigned sp)).
  { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. unfold rseqW, RAUXV_CELL, RCTX, RLIBC. constructor; [cbn; lia| constructor]. }
  (nelimp (rmeta_slot_bounds st2 m3 mm MR3 MSL) 4%nat; intros Gpos GC GI _).
  (* [comment removed for export] *)
  eapply evt_cut. { eapply rmm_call_walk. }
  cbv beta. intros ms' ->.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -144) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lia | rewrite SP'; lia | exact CLO
    | rewrite SP', EA; lia | rewrite TP; unfold RATP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  (* [comment removed for export] *)
  assert (REGS : s_regions stS = s_regions st2) by (rewrite ES; reflexivity).
  assert (SHS : s_shadow stS = s_shadow st2) by (rewrite ES; reflexivity).
  assert (GRS : s_groups stS = s_groups st2) by (rewrite ES; reflexivity).
  assert (ARS : s_areas stS = s_areas st2) by (rewrite ES; reflexivity).
  assert (TKS' : s_tick stS = s_tick st2) by (rewrite ES; reflexivity).
  assert (NRS : s_next_rid stS = s_next_rid st2) by (rewrite ES; reflexivity).
  assert (RSS : s_reserved stS = s_reserved st2) by (rewrite ES; reflexivity).
  assert (RECS : forall q, get_meta_rec stS q = get_meta_rec st2 q) by (intros q; rewrite ES; reflexivity).
  assert (ACTS : forall c', active stS c' = active st2 c') by (intros c'; unfold active; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (HS _)); reflexivity).
  assert (BRKS : c_brk (ctx stS) = c_brk (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (HS _))))).
  assert (CTRS : c_mmap_counter (ctx stS) = c_mmap_counter (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (HS _)))))).
  assert (FMHS : c_free_meta_head (ctx stS) = c_free_meta_head (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (proj2 (HS _))))))).
  assert (CONCS : forall q, conc stS q = conc st2 q) by (intros q; unfold conc, get_region; rewrite REGS; reflexivity).
  assert (MSLS : meta_slot stS mm) by (eapply meta_slot_same_areas; [exact ARS| exact MSL]).
  assert (TKS : ticks_ok stS) by (eapply ticks_ok_same; [exact SHS| exact TKS'| exact TK3]).
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR as (WF & _). (nelimp WF 4%nat; intros RS0 WR0 DJ0 _).
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (nelim PO 22%nat; intros v0' v1 v2 v3 v4' v5 v6 v7 v8 v9 v10 v11 v12 v13 m6 -> MU6 WM6 MI6 ST6 ERR6 He).
    cbn [mmap_val]. unfold mm_after. fold stS. destruct (mmap_answer_ok_err (live_ranges stS) nd e He) as [-> ->]. cbn [negb].
    rewrite as_free_meta_eq. cbn [as_kq].
    rewrite SP' in MU6, ST6. rewrite EA in MU6.
    replace (ret_pc (Z_to_bv 64 0x166d0)) with (Z_to_bv 64 0x166d0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (FR6 : rw_cells psegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rwrapper_munch_keeps stS m4 m6 (bv_unsigned sp - 144) lo MR4); [| exact WM6| unfold alloc_ceiling; lia].
      eapply munch_weaken; [| exact MU6]. intros y; cbn; lia. }
    (* [comment removed for export] *)
    pose proof (lf_freelist _ (isf_lf _ _ F2)) as FFL. change (fact_freelist (strip st2)) with (fact_freelist st2) in FFL.
    assert (FL : forall h, c_free_meta_head (ctx stS) = Some h ->
              meta_slot stS h /\ h <> mm /\ exists p, m_prev (get_meta_rec stS h) = Some p /\ meta_slot stS p /\ p <> mm).
    { intros h Hh. rewrite FMHS in Hh. (nelim (FFL h Hh) 8%nat; intros MSh MEMh NXh p HP MSp MEMp NXp).
      change (meta_slot (strip st2) h) in MSh. change (get_meta_rec (strip st2) h) with (get_meta_rec st2 h) in MEMh, NXh, HP.
      change (meta_slot (strip st2) p) in MSp. change (get_meta_rec (strip st2) p) with (get_meta_rec st2 p) in MEMp, NXp.
      split; [eapply meta_slot_same_areas; [exact ARS| exact MSh]|].
      split; [intros ->; rewrite G0 in NXh; apply NXh; reflexivity|].
      exists p. rewrite RECS. split; [exact HP|]. split; [eapply meta_slot_same_areas; [exact ARS| exact MSp]|].
      intros ->. rewrite G0 in NXp. apply NXp. reflexivity. }
    riprefixT.
    eapply evt_cut. { eapply rmm_ret_fail_walk. }
    cbv beta. intros ms' ->.
    eapply evt_cut. { rewrite <- (CONCS mm). subst sp'. unfold rFRM in FR6. eapply (rfailm2_walk stS mm MSLS FL); [exact MR6| exact MI6| exact FR6| lia]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 9%nat; intros s6x m7 junk' -> FR7 MU7 WM7 MI7 MR7).
    assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW stS mm (bv_unsigned sp))).
    { eapply (rfailW_low stS mm m6 _ MR6 MSLS). intros h Hh. (nelim (FL h Hh) 6%nat; intros MSh _ p HP MSp _).
      split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
    assert (ST7 : stk psegs m7 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [exact ST6| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]]. }
    assert (ERR7 : rw_cells psegs m7 (errno_addr tp) [C4 (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e))]).
    { eapply rw_cells_transport; [exact ERR6| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
    eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 4%nat; intros a1y a2y -> ST8). apply evt_done.
    (* [comment removed for export] *)
    set (stF := as_fm_st stS mm) in *.
    (nelim (fm_proj stS mm) 13%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10 PF11 PF12 _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
    assert (FS : Forall (rmetaW (bv_unsigned sp) stS) (rfailW stS mm (bv_unsigned sp))).
    { apply (rfailW_shape stS mm _ MSLS). intros h Hh; (nelim (FL h Hh) 6%nat; intros MSh _ p HP MSp _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
    assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
    { eapply rpres_except_trans.
      - eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr. exists r. rewrite PF1, REGS. repeat split; auto; lia.
      - eapply rpres_except_trans.
        + eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros X; apply NC; left; [left; lia| right; left; rewrite unsigned_lit by lia; lia].
        + eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
          intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          * cbn in E1, E2. subst lo' hi'. left. do 3 right.
            assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
            destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
            exists rid0, r0. split; [exact H0|]. split; [exact K0|].
            assert (EC : conc stF q = conc stS q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
          * inversion E; subst. left. right. right. left. unfold RCTX in *. lia.
          * inversion E; subst. left. left. lia. }
    apply HK. unfold ras_post2.
    nexists 14%nat. exists m7, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
    split; [exact MR7|].
    split; [eapply ticks_ok_same; [rewrite PF2; exact SHS| rewrite PF6; exact TKS'| exact TK3]|].
    split. { eapply (unk_agree_xfer o st2 m3 stF m7 UA3).
      - rewrite PF2. exact SHS.
      - intros rid r Hk Hr. rewrite PF1, REGS in Hr. exact Hr.
      - intros b. rewrite PF3, GRS. split; intros X; exact X.
      - intros rid r off h Hr Hk Ho Hc NG.
        pose proof MR3 as (WF3 & _). (nelimp WF3 4%nat; intros _ WR3 DJ3 _). (nelim (WR3 _ _ Hr) 5%nat; intros R0 _ _ RC _). unfold alloc_ceiling in RC.
        (nelim (rregion_facts st2 m3 rid r MR3 Hr) 5%nat; intros _ _ _ RI1 RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
        transitivity (m6 (wa (r_base r + off))).
        { apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
          pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          - cbn in E1, E2. subst lo' hi'. rewrite CONCS in Ha.
            assert (MSq2 : meta_slot st2 q) by (eapply meta_slot_same_areas; [symmetry; exact ARS| exact MSq]).
            (nelim (rmeta_chunk_facts st2 m3 q MR3 MSq2) 7%nat; intros _ _ _ _ _ GRG _). destruct (GRG rid r Hr Hk); lia.
          - inversion E; subst. unfold RCTX in Ha. lia.
          - inversion E; subst. lia. }
        transitivity (m4 (wa (r_base r + off))).
        { apply MU6. rewrite wa_unsigned by lia. cbn. lia. }
        apply MU4. rewrite wa_unsigned by lia. unfold rseqW, RCTX. cbn. lia. }
    split; [exact PE07|].
    split. { split; [| rewrite PF7, NRS, <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite PF8, RSS, (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
             intros rid r Hr. rewrite <- REG1 in Hr. (nelim (amr_regions _ _ _ REL rid r Hr) 6%nat; intros r' H' K' B' L' _). exists r'. rewrite PF1, REGS. auto. }
    split. { unfold brk_link_ps in *. rewrite PF11, BRKS. destruct (c_brk (ctx st2)) as [| |rid off]; auto.
             unfold conc, get_region. rewrite PF1, REGS. exact BL2. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite PF9, ACTS, (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ARS. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF6, TKS', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split; [rewrite PF12, CTRS; exact FC1|].
    left. reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (nelim PO 22%nat; intros v0' v1 v2 v3 v4' v5 v6 v7 v8 v9 v10 v11 v12 v13 m6 -> MU6 WM6 MI6 ST6 ERR6 AOK).
    cbn [mmap_val]. unfold mm_after. fold stS.
    destruct (mmap_answer_ok (live_ranges stS) nd xa) eqn:VOK. 2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    (nelim (mmap_answer_ok_addr (live_ranges stS) nd xa ltac:(lia) AOK VOK) 5%nat; intros X0 XA XC XRF ISE). rewrite ISE.
    rewrite SP' in MU6, ST6.
    assert (RU : round_up_pg nd = nd) by (unfold round_up_pg; change (PGSZ - 1) with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia).
    rewrite RU in XC, XRF.
    assert (FR6 : rw_cells psegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rmrep_transport_high stS m4 m6); [exact MR4| exact MU6| exact WM6| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid stS). set (r0 := {| r_kind := RKGroup; r_base := xa; r_len := nd |}).
    set (stN := set_next_rid (N.succ rid) (set_regions (<[rid:=r0]> (s_regions stS)) stS)).
    assert (EstN : stN = fst (new_region RKGroup xa nd stS)) by reflexivity.
    pose proof (mf_ptrs _ _ MF2) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) stS).
    { rewrite ES. apply ptrs_in_upd_ctx_scalar; try (intros cc; (nelimp (HS cc) 14%nat; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?); assumption).
      eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. rewrite NRS. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; rewrite NRS; lia)) as [FRr FRs].
    unfold F_mm_syscalls.mmap_raw in ST6 |- *. cbn [negb] in ST6 |- *. rewrite mmap_len_round_up, RU in ST6 |- *.
    unfold alloc_ceiling in XC.
    set (mz := apply_zeros m6 [(wa xa, Z_to_bv 64 nd)]) in *.
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + nd <= a) -> mz (wa a) = m6 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + nd -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : rmrep stN mz).
    { rewrite EstN. eapply (rmrep_new_region stS m6 mz xa nd RKGroup MR6 PT1 ltac:(rewrite SHS; exact FRs) X0 XA ltac:(lia));
        rewrite ?mmap_len_round_up, ?RU; [unfold alloc_ceiling; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    pose proof MR6 as (WF6 & _). (nelimp WF6 4%nat; intros RS6 WR6 DJ6 _).
    assert (XI : xa + nd <= 0x10000 \/ 0x55000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa nd = true).
      { apply ranges_free_intro. intros b kk HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS6. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv psegs mz).
    { unfold mz. apply (mem_inv_zeros psegs m6 xa nd); try lia; [exact MI6 | intros w Hw; apply ref_ro_addr_false; lia | unfold TASK_SIZE; pose proof (@ceil_hi ACEIL); unfold alloc_ceiling in *; lia]. }
    assert (MUz : munch [(xa, xa + nd)] m6 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono psegs m6 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono psegs m6 xa nd); try lia; exact Hw).
    assert (FRz : rw_cells psegs mz (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR6| exact MUz| exact WMz|]. cbn. lia. }
    assert (STz : stk psegs mz lo (bv_unsigned sp + -144)) by exact ST6.
    assert (ERRz : rw_cells psegs mz (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [exact ERR6| exact MUz| exact WMz|]. rewrite EA. cbn. lia. }
    (* [comment removed for export] *)
    assert (MSLN : meta_slot stN mm) by (eapply meta_slot_same_areas; [| exact MSLS]; rewrite EstN; reflexivity).
    assert (RECN : get_meta_rec stN mm = meta0) by (rewrite EstN; change (get_meta_rec (fst (new_region RKGroup xa nd stS)) mm) with (get_meta_rec stS mm); rewrite RECS; exact G0).
    assert (CTRN : c_mmap_counter (ctx stN) = c_mmap_counter (ctx st2)) by (rewrite EstN; change (ctx (fst (new_region RKGroup xa nd stS))) with (ctx stS); exact CTRS).
    assert (GCN : conc stN mm = conc st2 mm).
    { rewrite <- CONCS. rewrite EstN. apply nr_conc. cbn [fst].
      (nelim MSLS 6%nat; intros ar arr kk Ha Hk ->). unfold aadd. cbn [fst]. intros E.
      (nelim PT1 10%nat; intros _ _ _ _ _ _ _ _ P9 _). destruct (P9 _ _ Ha) as [X _]. exact (X E). }
    replace (ret_pc (Z_to_bv 64 0x166d0)) with (Z_to_bv 64 0x166d0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    riprefixT.
    eapply evt_cut.
    { rewrite <- GCN. subst sp'.
      assert (XC' : xa + nd <= alloc_ceiling) by (unfold alloc_ceiling; exact XC).
      eapply (rmm_ret_ok_walk stN sc c size nd xa (c_mmap_counter (ctx st2)) mm SC ltac:(lia) SZ ltac:(lia) NDM X0 XC' MSLN RECN CTRN FC1);
        [exact MRz| exact MIz]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 9%nat; intros xa3 xa4 m8 -> MU8 WM8 MI8 MR8 CTR8).
    set (stT := mm_st4 stN nd mm) in *.
    (* [comment removed for export] *)
    assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (ML : 0 <= Z.shiftr nd 12 < 2^52) by (rewrite ND12; Z.div_mod_to_equations; lia).
    assert (RECT : get_meta_rec stT mm = {| m_prev := None; m_next := None; m_mem := None; m_avail := 0; m_freed := 0; m_last_idx := 0; m_freeable := 0; m_sizeclass := 0; m_maplen := Z.shiftr nd 12 |}).
    { unfold stT, mm_st4. rewrite rec_upd_ctx. unfold upd_meta. rewrite get_meta_rec_put_same, RECN. unfold m_set_maplen, meta0. cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass].
      f_equal. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (HrT : (s_regions stT) !! rid = Some r0) by (unfold stT, mm_st4, upd_meta; cbn; first [apply lookup_insert_eq | rewrite EstN; apply nr_lookup_new]).
    assert (GNT : forall off, (s_groups stT) !! (rid, off) = None).
    { intros off. change (s_groups stT) with (s_groups stS). destruct ((s_groups stS) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
      (nelim PT1 10%nat; intros _ _ _ _ _ _ _ _ _ P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
    assert (SHT : (s_shadow stT) !! rid = None) by (change (s_shadow stT) with (s_shadow stS); rewrite SHS; exact FRs).
    assert (ACTT : active stT sc = None).
    { unfold stT, mm_st4. unfold active, ctx, upd_ctx, upd_meta. cbn. change (c_active (s_ctx stS) !! sc) with (active stS sc). rewrite ACTS, (amr_active _ _ _ REL). exact ACT0. }
    assert (TKT : ticks_ok stT).
    { eapply ticks_ok_same; [| | exact TK3]; [change (s_shadow stT) with (s_shadow stS); exact SHS| change (s_tick stT) with (s_tick stS); exact TKS']. }
    pose proof (mm_ai_range stN c size nd mm ltac:(lia) SZ) as AIR.
    eapply evt_cut.
    { replace (Z_to_bv 64 xa) with (Z_to_bv 64 (conc stT (rid, 0))) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; f_equal; lia).
      change (conc stN mm) with (conc stT mm).
      eapply (rtail_walk stT sc c (mm_ai c size) (Z.shiftr nd 12) mm (rid, 0) r0 SC ltac:(lia) AIR ML);
        [eapply meta_slot_same_areas; [| exact MSLN]; reflexivity| exact RECT| exact HrT| reflexivity| cbn; lia| cbn; reflexivity
        | cbn [snd r_len r0]; rewrite RU; lia| apply GNT
        | intros b' gh Hb' Hf'; exfalso; destruct b' as [b1 b2]; cbn in Hf'; subst b1; rewrite GNT in Hb'; discriminate
        | intros o' v t Ho Hc; exfalso; unfold get_shadow in Hc; rewrite SHT in Hc; cbn in Hc; rewrite lookup_empty in Hc; discriminate
        | change (usage stT sc) with (usage stS sc); rewrite US; apply URall
        | exact ACTT| exact TKT| exact MR8| exact MI8]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 12%nat; intros s0x a1x a2x a3x a4x m9 -> MU9 WM9 MI9 MR9 TK9).
    assert (GT : conc stT mm = conc st2 mm) by (change (conc stT mm) with (conc stN mm); exact GCN).
    assert (PT : conc stT (rid, 0) = xa) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; lia).
    (* [comment removed for export] *)
    assert (FR9 : rw_cells psegs m9 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; unfold alloc_ceiling in GC; lia].
      eapply rw_cells_transport; [exact FRz| exact MU8| exact WM8|]. rewrite GCN. unfold RCTX. cbn. unfold alloc_ceiling in GC. lia. }
    assert (ST9 : stk psegs m9 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; unfold alloc_ceiling in GC; lia].
      eapply stk_transport_disjoint; [exact STz| exact MU8| exact WM8| rewrite GCN; unfold RCTX; cbn; unfold alloc_ceiling in GC; lia]. }
    eapply evt_cut. { unfold rFRM in FR9. eapply (ras_ret0 sp gp tp); [exact MR9| exact MI9| exact FR9| exact ST9| exact CLO| lia]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 4%nat; intros a1y a2y -> ST10). apply evt_done.
    rewrite (ag_tail_kq_eq sc k bail stT mm (rid, 0) c (mm_ai c size)); [| rewrite RECT; reflexivity| rewrite RECT; reflexivity| exact ACTT].
    apply HK.
    (* [comment removed for export] *)
    set (ai := mm_ai c size) in *. set (ml := Z.shiftr nd 12) in *.
    set (stF := st_model stT sc c ai mm (rid, 0)).
    assert (C32 : 1 <= c <= 32) by lia.
    assert (EML : nd = 4096 * ml) by (subst ml; rewrite ND12; Z.div_mod_to_equations; lia).
    assert (ML28 : 1 <= ml < 2^28) by lia.
    assert (Hk0 : r_kind r0 = RKGroup) by reflexivity.
    assert (LEN0 : r_len r0 = nd) by reflexivity.
    assert (MST : meta_slot stT mm) by (eapply meta_slot_same_areas; [| exact MSLN]; reflexivity).
    assert (Esz : size = 16 * size_class sc) by reflexivity.
    assert (NDC' : c = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * c + 16 <= nd /\ nd < 16 * size_class sc * c + 16 + 4096).
    { pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 _]. pose proof (round_up_pg_props (size * c + 16) ltac:(apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia| lia])) as [N1 _].
      rewrite <- Esz. destruct NDC as [[Ec En]|[LE En]]; [left; split; [exact Ec| rewrite En; lia] | right; split; [exact LE| rewrite En at 1; lia]]. }
    (nelim (sm_slot_ok stT sc c ai ml mm rid r0 SC C32 AIR ML28 RECT HrT Hk0 SHT GNT req nd RQ FIT LEN0 EML NDR ltac:(lia) NDC' MST) 4%nat; intros SO STR S16 SND).
    fold stF in SO, STR, S16, SND.
    (nelimp (sm_proj stT sc c ai mm rid) 10%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10).
    fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
    assert (MRF : rmrep stF m9) by (exact (rmrep_st_model stT sc c ai ml mm (rid, 0) SC C32 RECT ltac:(cbn; lia) m9 MR9)).
    assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK9]; reflexivity).
    assert (MSF : meta_slot stF mm) by (apply (proj1 (sm_meta_slot stT sc c ai mm rid mm)); exact MST).
    (* [comment removed for export] *)
    assert (REGT : s_regions stT = <[rid:=r0]> (s_regions stS)) by reflexivity.
    assert (SHT' : s_shadow stT = s_shadow st2) by (transitivity (s_shadow stS); [reflexivity| exact SHS]).
    assert (GRT : s_groups stT = s_groups st2) by (transitivity (s_groups stS); [reflexivity| exact GRS]).
    assert (ART : s_areas stT = s_areas st2) by (transitivity (s_areas stS); [reflexivity| exact ARS]).
    assert (TKT' : s_tick stT = s_tick st2) by (transitivity (s_tick stS); [reflexivity| exact TKS']).
    assert (NRT : s_next_rid stT = N.succ rid) by reflexivity.
    assert (RST : s_reserved stT = s_reserved st2) by (transitivity (s_reserved stS); [reflexivity| exact RSS]).
    assert (BRKT : c_brk (ctx stT) = c_brk (ctx st2)) by (transitivity (c_brk (ctx stS)); [reflexivity| exact BRKS]).
    assert (ACTT' : forall c', active stT c' = active st2 c') by (intros c'; transitivity (active stS c'); [reflexivity| apply ACTS]).
    assert (GF : conc stF mm = conc st2 mm) by (rewrite (sm_conc stT sc c ai mm rid); exact GT).
    assert (HOLD : forall q rq, (s_regions st2) !! q = Some rq -> (s_regions stF) !! q = Some rq /\ q <> rid).
    { intros q rq Hq. assert (NE : q <> rid) by (intros ->; rewrite FRr in Hq; discriminate).
      split; [| exact NE]. rewrite PF1, REGT, lookup_insert_ne, REGS by congruence. exact Hq. }
    assert (MREL0S : forall q rq, (s_regions st0) !! q = Some rq ->
              exists r', (s_regions stS) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
    { intros q rq Hq. (nelim (mrel_regions _ _ (er_mrel _ _ ER) q rq Hq) 5%nat; intros r1 H1 K1 B1 L1). rewrite <- REG1 in H1.
      (nelim (amr_regions _ _ _ REL q r1 H1) 6%nat; intros r2 H2 K2 B2 L2 _). exists r2. rewrite REGS. repeat split; auto; try congruence. lia. }
    assert (FRESH : forall a, xa <= a < xa + nd -> fresh_addr st0 a).
    { intros a Ha. eapply (fresh_addr_anti st0 stS); [| exact MREL0S|].
      - rewrite RS6, <- RS0. exact (mrel_reserved _ _ (er_mrel _ _ ER)).
      - split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa nd); [exact XRF| lia| lia| lia]. }
    assert (HFP2 : forall a, rmalloc_fp st0 st2 lo (bv_unsigned sp) a -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
    { intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros q rq Hq. exists rq. split; [apply (proj1 (HOLD q rq Hq))|]. repeat split; auto. lia. }
    (* [comment removed for export] *)
    assert (OLDW : forall q rq off, (s_regions st2) !! q = Some rq -> r_kind rq = RKGroup -> 0 <= off < round_up_pg (r_len rq) ->
              m9 (wa (r_base rq + off)) = m3 (wa (r_base rq + off))).
    { intros q rq off Hq Hk Ho.
      assert (HqS : (s_regions stS) !! q = Some rq) by (rewrite REGS; exact Hq).
      (nelim (WR6 _ _ HqS) 5%nat; intros R0 _ _ RC _). unfold alloc_ceiling in RC.
      (nelim (rregion_facts st2 m3 q rq MR3 Hq) 5%nat; intros _ _ _ RI1 RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      (nelim (rmeta_chunk_facts st2 m3 mm MR3 MSL) 7%nat; intros _ _ _ _ _ GRG _). pose proof (GRG q rq Hq Hk) as GRq.
      pose proof (In_live_ranges stS q rq HqS) as HIq. unfold region_live_range in HIq. rewrite Hk in HIq.
      pose proof (ranges_free_In _ _ _ _ _ XRF HIq) as DJq.
      pose proof (lr_lo_group rq Hk) as LRq.
      (* [comment removed for export] *)
      transitivity (m8 (wa (r_base rq + off))). { apply MU9. rewrite wa_unsigned by (clear - Ho R0 RC; lia). unfold rtailW. rewrite GT, PT. cbn. unfold RCTX. clear - Ho R0 RC RI2 GRq DJq SC SND S16; lia. }
      transitivity (mz (wa (r_base rq + off))). { apply MU8. rewrite wa_unsigned by (clear - Ho R0 RC; lia). rewrite GCN. cbn. unfold RCTX. clear - Ho R0 RI2 GRq; lia. }
      transitivity (m6 (wa (r_base rq + off))). { apply ZO; [clear - Ho R0 RC; lia | clear - Ho R0 DJq; lia]. }
      transitivity (m4 (wa (r_base rq + off))). { apply MU6. rewrite wa_unsigned by (clear - Ho R0 RC; lia). cbn. clear - Ho R0 RC CLO' LO ASG; lia. }
      apply MU4. rewrite wa_unsigned by (clear - Ho R0 RC; lia). unfold rseqW, RCTX. cbn. clear - Ho R0 RI2; lia. }
    assert (UAF : unk_agree stF o m9).
    { eapply (unk_agree_transfer st2 stF o m3 m9 UA3). intros q rq Hq Hk.
      rewrite PF1, REGT, REGS in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      - right. rewrite lookup_insert_eq in Hq. inversion Hq; subst rq. cbn [r_len r_base]. intros off h Ho Hc.
        rewrite (sm_cell_read stT sc c ai mm rid SHT off ltac:(lia)) in Hc.
        destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T. apply (sm_grp_hdr_cov stT sc c ai mm rid SC). lia.
      - left. rewrite lookup_insert_ne in Hq by congruence.
        split; [exact Hq|].
        split. { rewrite (sm_shadow_other stT sc c ai mm rid q NE). unfold get_shadow. rewrite SHT'. reflexivity. }
        split. { intros off X. apply (sm_grp_hdr_cov_old stT sc c ai mm rid GNT). eapply rgrp_hdr_cov_same; [exact GRT| exact X]. }
        intros off h Ho Hc NG. exact (OLDW q rq off Hq Hk Ho). }
    assert (PE09 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m9).
    { eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE04| exact HFP2]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. left. left. lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. do 4 right. apply FRESH. lia. }
      eapply rpres_except_trans.
      { eapply rpres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. rewrite GCN. cbn. split; [|split; [|exact I]]; intros X; apply NC.
        - left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
          exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
        - left. right. right. left. unfold RCTX in *. lia. }
      eapply rpres_except_of_munch; [exact MU9| exact WM9|]. intros a Ha NC. unfold rtailW. rewrite GT, PT. cbn.
      split; [|split; [|split; [|split; [|exact I]]]]; intros X; apply NC.
      - left. right. right. left. unfold RCTX in *. lia.
      - left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
        exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
      - do 4 right. apply FRESH. lia.
      - left. right. right. left. unfold RCTX in *. lia. }
    assert (ERR9 : rw_cells psegs m9 (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [| exact MU9| exact WM9|].
      - eapply rw_cells_transport; [exact ERRz| exact MU8| exact WM8|]. rewrite EA, GCN. cbn. unfold RCTX. lia.
      - unfold rtailW. rewrite GT, PT, EA. cbn. unfold RCTX. lia. }
    unfold ras_post2.
    nexists 14%nat. exists m9, errv'. split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST10|]. split; [exact ERR9|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m9); [exact MRF| exact AUX| exact PE09| exact CLO| lia]|].
    split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE09|].
    split. { split.
      - intros q rq Hq. rewrite <- REG1 in Hq. (nelim (amr_regions _ _ _ REL q rq Hq) 6%nat; intros r' H' K' B' L' _).
        exists r'. split; [apply (proj1 (HOLD q r' H'))|]. repeat split; auto.
      - rewrite PF6, NRT. pose proof (amr_next_rid _ _ _ REL) as NX1. pose proof (tr_next _ _ _ TR) as NX0. subst rid. rewrite NRS. lia.
      - rewrite PF7, RST, (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
    split. { unfold brk_link_ps in BL2 |- *. rewrite PF8, BRKT. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:EB; auto.
             rewrite (sm_conc stT sc c ai mm rid). rewrite <- (CONCS (brid, boff)) in BL2.
             replace (conc stT (brid, boff)) with (conc stS (brid, boff)); [exact BL2|].
             change (conc stT (brid, boff)) with (conc stN (brid, boff)). rewrite EstN. symmetry. apply nr_conc. cbn [fst].
             (nelim PT1 8%nat; intros _ _ _ _ _ _ P7 _). rewrite BRKS in P7. first [rewrite EB in P7; exact P7 | exact P7]. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite (sm_active stT sc c ai mm rid). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite ACTT', (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ART. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF5, TKT', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros _ rid' S len RS o' v t Ho Hc. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        rewrite (sm_cells_none stT sc c ai mm rid SHT) in Hc. discriminate.
      - intros _ _ rid' S len RS o' Ho. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        split; [apply (sm_cells_none stT sc c ai mm rid SHT)|].
        split; [apply (sm_hav_none stT sc c ai mm rid SHT); lia| apply (sm_havp_none stT sc c ai mm rid SHT)]. }
    split. { rewrite PF9, CTR8. unfold u32. Z.div_mod_to_equations. lia. }
    right. split; [lia|]. exists mm, (rid, 0), r0.
    split; [rewrite (sm_active stT sc c ai mm rid), Z.eqb_refl; reflexivity|]. split; [exact SO|]. split.
    + intros a Ha. replace (r_base r0) with xa in Ha by reflexivity. cbn [fst snd] in Ha. do 4 right. apply FRESH. rewrite Z.mul_0_r in Ha. lia.
    + intros _. cbn [fst snd]. replace (0 + (16 + get_stride (get_meta_rec stF mm) * 0) + -3) with 13 by lia.
      apply (sm_rdv stT sc c ai mm rid SHT).
Qed.
End LEVEL.


End CeilWrap.
End RASlot_M4.

(* [comment removed for export] *)
Module RASlot_M6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M0 RASlot_M1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3.RASlot_M2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_M3 RASlot_M4 RASlot_M5D RASlot_M5F RASlot_M5S RASlot_M5.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Theorem ralloc_slot_ok (ram_pre : mstate -> Prop) :
  ralloc_meta_stmt ram_pre -> RAMP_AS ram_pre -> forall f, ralloc_slot_stmt2 f.
Proof using .
  intros AM AMP f. induction f as [|f IHf].
  - intros R k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv
           PRE MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK.
    cbn [alloc_slot]. apply rimplT_undef.
  - intros R k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv
           PRE MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK.
    destruct PRE as ((LB & AR & IS) & ER & AC & SC & RQ & FIT).
    pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st AR IS) as F0.
    pose proof (RAS_STACK_ge sc) as ASG.
    rewrite (alloc_slot_S full_lay f sc req k bail st). subst a0.
    eapply (rta_phase (as_k full_lay f sc req k bail) bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
              (rtaf_of_facts st LB sc F0 SC) SC CLO ltac:(lia)).
    + (* [comment removed for export] *)
      intros stX g3 msk kk m' t0' t1' a1' a2' a3' a4' a5' a6' a7' TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
      exact (rhk1_ok f k bail o s Q ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv
                AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK stX g3 msk kk m' t0' t1' a1' a2' a3' a4' a5' a6' a7' TR HA GM MSK MR0 LBK KK MR' MI' ST' PE).
    + reflexivity.
    + exact MR.
    + exact MI.
    + exact ST.
    + (* [comment removed for export] *)
      intros st1 m' t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' junk TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
      unfold as_k. cbn [Z.eqb negb].
      eapply (rag_phase f k bail o s Q ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv
                AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK ram_pre AM AMP); [| exact TF| exact TR| exact ACT0| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      (* [comment removed for export] *)
      refine (rhag_ok f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req AR SC RQ FIT _ _).
      * (* [comment removed for export] *)
        exact (rhmm_ok k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req
                 AR ER SC RQ FIT MR AUX CLO LO TP A1 HK).
      * (* [comment removed for export] *)
        refine (rhnest_ok f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc AR ER SC MR CLO LO TP IHf _ _).
        -- exact (rnfail_ok f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req errv
                   AR IS ER SC RQ MR AUX CLO LO ERR TP HK).
        -- exact (rnsucc_ok f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req errv
                   AR IS ER SC RQ FIT MR AUX CLO LO ERR TP HK).
Qed.


End CeilWrap.
End RASlot_M6.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RMalloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv2.
Module RF_malloc_top.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_A.RF_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMalloc_ifaceP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
  implM psegs (membed t1) s Q1 ms ->
  implM psegs (membed t2) s
        (fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
    exists r1, []. cbn. auto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
              impl psegs (at_node psegs) (ITree.bind _ (Ret Unr) f) Qx msx = impl psegs (at_node psegs) (f Unr) Qx msx) by reflexivity.
    destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         eapply impl_epost_mono; [eapply IH; exact H1|];
         intros [r2' s2] ms2; cbn; intros nelH_; (nelim nelH_ 6%nat; intros r1' ans F1 F2 HR HQ);
         exists r1', (z :: ans); cbn; auto.
Qed.

Lemma rraw_malloc_bridge2 : forall st s n (o : mem) Q1 Q ms,
  strip st = ps_m s ->
  rimplT o (malloc st n) s Q1 ms ->
  (forall st' (p : optr) s' ms' (r : option bptr) ans o' cst c,
     Q1 (st', p) s' ms' -> ptr_rel p r ->
     follow (mrun o (malloc st n)) ans = Some (o', (st', p)) ->
     follow (cmalloc (strip st) n) ans = Some (cst, c) ->
     cst = strip st' ->
     r = match c with Some slot => Some (slot, fresh_off cst slot n) | None => None end ->
     Q r (set_m (strip st') s') ms') ->
  implM psegs (raw_malloc n) s Q ms.
Proof.
  intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
  eapply (implM_bind psegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> ->). cbv beta.
  eapply (implM_bind psegs _ _ _ (fun r s' ms' => exists st' p ans o', Q1 (st', p) s' ms' /\ MREL (o', (st', p)) r
             /\ follow (mrun o (malloc st n)) ans = Some (o', (st', p)) /\ follow (cmalloc (strip st) n) ans = Some r)).
  { rewrite <- Hst. unfold rimplT in H.
    eapply implM_mono.
    - eapply (rmembed_strel_follow MREL (mrun o (malloc st n)) (cmalloc (strip st) n)); [| exact H].
      unfold mrun. apply malloc_control. apply pans_mem_range.
    - intros [cs c] s' ms' ([o1 [st' p]] & ans & F1 & F2 & HR & H1). cbn in H1.
      exists st', p, ans, o1. auto. }
  intros [cs c] s' ms' (st' & p & ans & o' & H1 & HR & F1 & F2). cbv beta iota.
  eapply (implM_bind psegs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
  unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
  eapply (HQ st' p s' ms' _ ans o' (strip st') c H1); [| exact F1| exact F2| reflexivity| reflexivity].
  destruct p as [pf|], c as [c|]; cbn in Hp |- *; try exact Hp.
Qed.

(* [comment removed for export] *)
Lemma rimplT_silent {R} o (t : Malloc.M R) o' (x : R) s Q ms :
  mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt psegs (Q x s) ms.
Proof using . intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_of_fp st st' LB lo sp m m' :
  RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
  rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
  rheap_pres LB sp m m'.
Proof.
  intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
  destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
  - destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); unfold alloc_ceiling in *; lia.
  - destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
  - (nelim (rblock_inside st LB m blk MF MR Hin) 12%nat; intros r g idx Hr Hk SL LOB HIB BZ R4 RC RI1).
    unfold alloc_ceiling in *.
    pose proof MR' as (WF' & _). (nelimp WF' 4%nat; intros _ WR' DISJ' _).
    pose proof MR as (WF & _). (nelimp WF 4%nat; intros _ WR DISJ _).
    destruct REL as [RREG _ _]. (nelim (RREG _ _ Hr) 5%nat; intros r1 Hr1 K1 B1 L1).
    pose proof (round_up_pg_mono _ _ L1) as RL1.
    pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
    destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
    + lia.
    + rewrite unsigned_lit in H by lia. lia.
    + unfold RCTX in H. lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
      destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
      pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
        (nelim (HB blk Hin (eq_sym E)) 3%nat; intros r'' Hr'' DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
        rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ruser_chunk st' m' (p : aptr) r n :
  rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
  16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
  exists junk, rw_cells psegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof using .
  intros MR Hr Hk P0 PN N0.
  (nelimp MR 6%nat; intros WF _ _ _ _ SH). destruct (SH (fst p) r Hr Hk) as [HW _].
  (nelimp (rregion_addr_facts st' m' (fst p) r MR Hr) 4%nat; intros R4 _ RC RI). unfold alloc_ceiling in RC.
  rewrite (conc_region' st' p r Hr).
  assert (W : wr_at psegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
  (nelim (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) 3%nat; intros bs L B).
  exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
  split; [exact L| exact I].
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists st2 r ans o1,
    fst res = strip st2
    /\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
    /\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
    /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
    /\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| unfold alloc_ceiling in *; lia]).
  (nelim HEAP 6%nat; intros st LB0 HPERM Hst MR [BLK AR]). rename LB into LBc. rename LB0 into LB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  (* [comment removed for export] *)
  eapply (implM_evt psegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom psegs))).
  { unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  unfold raw_malloc.
  eapply (implM_bind psegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0' s1' ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> ->). cbv beta.
  eapply (implM_bind psegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (rmembed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold rimplT in |- *.
          pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold rimplT in X. exact X.
      + intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold rmidQ. exists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  (nelim MQ 9%nat; intros st2 r ans o1 Ecs Ec F1 F2 CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind psegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.
  (* [comment removed for export] *)
  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    (nelim CQ 40%nat; intros b rg m1 errv1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' u3 u4 u5 u6 ra' -> MR2 TK2 UA2 MI2 ST2 FR2 ERR2 AUX2 PE2 SPANFP CTR2 SO EXPO MREL BL2 PSM PSF PSO)
.
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    (nelimp (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) 4%nat; intros R4 RAL RC RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    unfold alloc_ceiling in RC, CLO. unfold RMALLOC_STACK in LO.
    pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold renf_post in EP.
    (nelim EP 25%nat; intros st' p w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' ER -> MI' ST' MR' TK' PE' LEAF).
    (nelim LEAF 7%nat; intros off OFF0 FIT Ep Est' Ep2 Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    (nelimp (strip_eq_proj _ _ SE) 8%nat; intros Ec Er En Em _ _ Esl Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    (* [comment removed for export] *)
    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold rmalloc_post. nexists 15%nat. exists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - clear - Ha X RI1 SPAN SKL SK B0 S16. first [heap_lia_imp | lia]. }   (* [comment removed for export] *)
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    exists A, ujunk.
    split; [reflexivity|].
    split. { unfold rblock_range, alloc_ceiling. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). clear - N0' RC RI1 SPAN SKL SK B0 FIT OFF0 S16. lia. }  (* [comment removed for export] *)
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].
    (* [comment removed for export] *)
    intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
    assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
    { apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
      pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
    unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
    rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
    unfold fresh_off. cbn [s_slots strip].
    replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
    rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
    rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
    change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    (nelim CQ 29%nat; intros m1 errv1 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 -> MR2 TK2 MI2 ST2 ERR2 AUX2 PE2 MREL BL2 PSM PSF PSO)
.
    apply evt_done. unfold rmalloc_post. nexists 15%nat. exists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    split; [reflexivity|].
    exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.
End TOPLEVEL.



End CeilWrap.
End RF_malloc_top.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_alloc_meta.
Module RF_alloc_slot.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_alloc_meta.RF_am_P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_alloc_meta RASlot_M6.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


(* [comment removed for export] *)
Lemma ras_pre2_intro : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> ras_pre2 st (set_tick t st) sc n FUEL.
Proof using .
  intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
  - exists LB. split; [exact AR| apply ist_top; exact TT].
  - apply ER_refl_tick.
  - apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof.
  unfold ralloc_slot_stmt. intros fuel.
  exact (ralloc_slot_ok ram_pre ralloc_meta_spec MallocFacts_inv4.ist_ampre_proof fuel).
Qed.


End CeilWrap.
End RF_alloc_slot.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RF_malloc_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_malloc_core RF_malloc_top OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RASlot_I RF_alloc_slot RF_malloc_big OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_alloc_meta.RF_am_P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_alloc_meta.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Theorem rmalloc_spec : rmalloc_stmt.
Proof using .
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.



End CeilWrap.
End RF_malloc_spec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Frame SCPS NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Export PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_A Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KInv2 KRaw KB_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import RMalloc_ifaceP.
Import RF_malloc_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require RF_realloc_fentry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.RF_realloc_fentry.RF_free_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bview (b : block) : cblock := (blk_addr b, blk_size b).

Definition LHEAPd (SPB : Z) (LB : list cblock) (m : mem) (mo : Model) : Prop :=
  exists s LBi B, RHEAP s LBi m /\ LB = map bview LBi /\ AOWN (map blk_slot LBi) s mo /\ MOK mo
                  /\ rauxv_ok m B /\ SPB <= B.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lhd_mok : forall SPB LB m mo, LHEAPd SPB LB m mo -> MOK mo.
Proof using . intros SPB LB m mo nelH_; (nelim nelH_ 8%nat; intros s LBi B _ _ _ HM _). exact HM. Qed.

Lemma lhd_lower : forall SPB SPB' LB m mo, LHEAPd SPB LB m mo -> SPB' <= SPB -> LHEAPd SPB' LB m mo.
Proof using . intros SPB SPB' LB m mo (s & LBi & B & H1 & H2 & H3 & H4 & H5 & H6) HS. exists s, LBi, B. splits; auto. lia. Qed.

Lemma lhd_perm : forall SPB LB LB' m mo, LHEAPd SPB LB m mo -> Permutation LB LB' -> LHEAPd SPB LB' m mo.
Proof using .
  intros SPB LB LB' m mo (s & LBi & B & HR & -> & HO & HM & HA & HS) HP.
  (nelim (Permutation_map_inv _ _ (Permutation_sym HP)) 3%nat; intros LBi' -> HP').
  exists s, LBi', B. splits; auto.
  - eapply RHEAP_perm; [exact HR| exact HP'].
  - eapply AOWN_perm; [apply Permutation_map; exact HP'| exact HO].
Qed.

Lemma in_bview : forall LBi A n, In (A, n) (map bview LBi) -> exists b, In b LBi /\ blk_addr b = A /\ blk_size b = n.
Proof using .
  intros LBi A n H. apply in_map_iff in H as (b & E & Hb). exists b. unfold bview in E. injection E as E1 E2. auto.
Qed.

Lemma lhd_block_range : forall SPB LB m mo A n, LHEAPd SPB LB m mo -> In (A, n) LB -> cblock_range A n.
Proof using .
  intros SPB LB m mo A n (s & LBi & B & HR & -> & _) Hin. (nelim (in_bview _ _ _ Hin) 4%nat; intros b Hb <- <-).
  exact (RHEAP_block_range_proof s LBi m b HR Hb).
Qed.

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof using .
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma lhd_blocks_disjoint : forall SPB LB m mo A1 n1 A2 n2,
  LHEAPd SPB LB m mo -> In (A1, n1) LB -> In (A2, n2) LB -> A1 <> A2 -> A1 + n1 <= A2 \/ A2 + n2 <= A1.
Proof.
  intros SPB LB m mo A1 n1 A2 n2 (s & LBi & B & HR & -> & _) H1 H2 NE.
  (nelim (in_bview _ _ _ H1) 4%nat; intros b1 Hb1 <- <-). (nelim (in_bview _ _ _ H2) 4%nat; intros b2 Hb2 <- <-).
  apply (RHEAP_blocks_disjoint_proof s LBi m b1 b2 HR Hb1 Hb2). intros E. apply NE.
  rewrite (nodup_map_inj blk_id LBi b1 b2 (RHEAP_blocks_nodup_proof s LBi m HR) Hb1 Hb2 E). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma RHEAP_addr_nodup : forall s LBi m, RHEAP s LBi m -> List.NoDup (map blk_addr LBi).
Proof.
  intros s LBi m nelH_; (nelim nelH_ 6%nat; intros st LB0 HP _ _ [_ AR]). pose proof (mf_nodup _ _ (MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  apply MallocFacts_inv2.NoDup_map_on.
  - intros x y Hx Hy E. destruct (decide (blk_slot x = blk_slot y)) as [ES|NS].
    + exact (nodup_map_inj blk_slot LB0 x y ND Hx Hy ES).
    + exfalso. pose proof (areach_blocks_apart st LB0 x y AR Hx Hy NS) as D.
      (nelim (areach_block_span st LB0 x AR Hx) 9%nat; intros r1 lo1 hi1 _ _ _ _ Z1 _).
      (nelim (areach_block_span st LB0 y AR Hy) 9%nat; intros r2 lo2 hi2 _ _ _ _ Z2 _).
      unfold IB in D. lia.
  - eapply NoDup_map_inv. exact ND.
Qed.

Lemma map_fst_bview : forall LBi, map fst (map bview LBi) = map blk_addr LBi.
Proof using . intros LBi. rewrite map_map. apply map_ext. intros [[p A] n]. reflexivity. Qed.

Lemma lhd_nodup : forall SPB LB m mo, LHEAPd SPB LB m mo -> NoDup (map fst LB).
Proof using . intros SPB LB m mo nelH_; (nelim nelH_ 6%nat; intros s LBi B HR -> _). apply NoDup_ListNoDup. rewrite map_fst_bview. eapply RHEAP_addr_nodup. exact HR. Qed.

Lemma lhd_ssp : forall SPB LB m mo, LHEAPd SPB LB m mo ->
  rw_cells psegs m PGOT_SSP [C8 (wz PSSP)] /\ exists canary : word, rw_cells psegs m PSSP [C8 canary].
Proof using .
  intros SPB LB m mo (s & LBi & B & (st & LB0 & _ & _ & MR & _) & _).
  destruct MR as (_ & _ & (_ & _ & _ & G1 & G2) & _). split; [exact G1| eexists; exact G2].
Qed.

(* [comment removed for export] *)
Lemma RHEAP_block_region : forall s LBi m b, RHEAP s LBi m -> In b LBi ->
  exists base top, base <= blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b + IB <= top /\ top mod 8 = 0
    /\ wr_at psegs m base (top - base) /\ (top <= 0x10000 \/ 0x55000 <= base) /\ 0 <= base /\ top <= alloc_ceiling.
Proof.
  intros s LBi m b (st & LB0 & HP & _ & MR & [_ AR]) Hin.
  assert (Hin0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hin]).
  (nelim (areach_block_span st LB0 b AR Hin0) 12%nat; intros r lo hi Hr Kr Hlo A1 Z1 A2 Hhi M1 M2).
  (nelimp MR 6%nat; intros WF _ _ _ _ SH). (nelimp WF 3%nat; intros _ WR _).
  (nelim (WR _ _ Hr) 5%nat; intros RB0 RBAL RL0 RBC RF). destruct (SH _ _ Hr Kr) as [W _].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  assert (RP : 0 < round_up_pg (r_len r)) by (unfold IB in A2; lia).
  pose proof (rreserved_disjoint1 _ _ RF RP) as D.
  exists (r_base r), (r_base r + hi). splits; try lia.
  (nelim W 3%nat; intros W0 W1 W2). split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
Qed.

Lemma lhd_block_wr : forall SPB LB m mo A n, LHEAPd SPB LB m mo -> In (A, n) LB -> wr_at psegs m A n.
Proof using .
  intros SPB LB m mo A n (s & LBi & B & HR & -> & _) Hin. (nelim (in_bview _ _ _ Hin) 4%nat; intros b Hb <- <-).
  destruct (RHEAP_block_region s LBi m b HR Hb) as (base & top & H1 & H2 & H3 & H4 & (W0 & W1 & W2) & H5 & H6 & H7).
  split; [lia|]. split; [unfold IB in H3; pose proof KStep.alloc_ceiling_lt; lia|]. intros i Hi.
  replace (blk_addr b + i) with (base + (blk_addr b + i - base)) by lia. apply W2. unfold IB in H3. lia.
Qed.

Lemma lhd_block_slack : forall SPB LB m mo A n i, LHEAPd SPB LB m mo -> In (A, n) LB ->
  0 <= i -> (A + n + i) < (A + n + 7) / 8 * 8 -> m (wa (A + n + i)) <> None.
Proof using .
  intros SPB LB m mo A n i (s & LBi & B & HR & -> & _) Hin Hi Hlt. (nelim (in_bview _ _ _ Hin) 4%nat; intros b Hb <- <-).
  destruct (RHEAP_block_region s LBi m b HR Hb) as (base & top & H1 & H2 & H3 & H4 & (W0 & W1 & W2) & H5 & H6 & H7).
  pose proof KStep.alloc_ceiling_lt as Hcl. unfold IB in H3.
  assert (Htop : (blk_addr b + blk_size b + 7) / 8 * 8 <= top).
  { pose proof (Z_div_mod_eq_full (blk_addr b + blk_size b + 7) 8). pose proof (Z.mod_pos_bound (blk_addr b + blk_size b + 7) 8).
    pose proof (Z_div_mod_eq_full top 8). lia. }
  specialize (W2 (blk_addr b + blk_size b + i - base) ltac:(lia)).
  replace (base + (blk_addr b + blk_size b + i - base)) with (blk_addr b + blk_size b + i) in W2 by lia.
  rewrite ref_wview_overlay in W2; [exact W2|]. unfold wa. rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nonempty_ivs (W : list ivl) : list ivl := List.filter (fun iv => fst iv <? snd iv) W.

Lemma outside_nonempty : forall W x, outside (nonempty_ivs W) x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exact I|]. cbn [nonempty_ivs List.filter fst snd] in H.
  destruct (Z.ltb_spec lo hi); cbn in H |- *.
  - destruct H as [H1 H2]. split; [exact H1| apply IH; exact H2].
  - split; [lia| apply IH; exact H].
Qed.

Lemma munch_nonempty : forall W m m', munch W m m' -> munch (nonempty_ivs W) m m'.
Proof using . intros W m m' H. eapply munch_weaken; [| exact H]. intros x Hx. apply outside_nonempty. exact Hx. Qed.

(* [comment removed for export] *)
Definition ivs_disjoint (W : list ivl) (a n : Z) : Prop :=
  forall lo hi, In (lo, hi) W -> lo < hi -> a + n <= lo \/ hi <= a.

Lemma disjoint_from_nonempty : forall W a n, ivs_disjoint W a n -> disjoint_from (nonempty_ivs W) a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; [exact I|]. cbn [nonempty_ivs List.filter fst snd].
  destruct (Z.ltb_spec lo hi).
  - cbn. split; [apply (H lo hi); [left; reflexivity| lia]|]. apply IH. intros lo' hi' Hin Hlt. apply H; [right; exact Hin| exact Hlt].
  - apply IH. intros lo' hi' Hin Hlt. apply H; [right; exact Hin| exact Hlt].
Qed.

Lemma munch_eq_at : forall W m m' x, munch W m m' -> ivs_disjoint W x 1 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x).
Proof using .
  intros W m m' x HM HD Hx. apply (munch_nonempty _ _ _ HM). unfold wa. rewrite unsigned_lit by lia.
  eapply disjoint_outside; [apply disjoint_from_nonempty; exact HD| lia].
Qed.

Lemma bytes_at_munch : forall W m m' a bs, munch W m m' -> bytes_at psegs m a bs -> ivs_disjoint W a (Z.of_nat (length bs)) ->
  bytes_at psegs m' a bs.
Proof using .
  intros W m m' a bs HM (H0 & H1 & HB) HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  rewrite (munch_eq_at W m m' (a + Z.of_nat i) HM); [reflexivity| | lia].
  intros lo hi Hin Hlt. pose proof (HD lo hi Hin Hlt). lia.
Qed.

Lemma rw_cells_munch : forall W m m' a cs, munch W m m' -> wmono psegs m m' -> rw_cells psegs m a cs ->
  ivs_disjoint W a (Z.of_nat (cells_size cs)) -> rw_cells psegs m' a cs.
Proof using .
  intros W m m' a cs HM HW [[Hwf HB] HWR] HD. split; [split; [exact Hwf|]|].
  - eapply bytes_at_munch; eauto. rewrite cells_bytes_length by assumption. exact HD.
  - eapply wr_at_transport; eauto.
Qed.

Lemma rauxv_ok_munch : forall W m m' B, munch W m m' -> wmono psegs m m' -> rauxv_ok m B ->
  (forall lo hi, In (lo, hi) W -> lo < hi -> (alloc_ceiling <= lo /\ hi <= B) \/ (hi <= RLIBC /\ lo < alloc_ceiling) \/ (0x55000 <= lo /\ hi <= alloc_ceiling)) ->
  rauxv_ok m' B.
Proof using .
  intros W m m' B HM HW (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & H1 & H2 & H3 & H4) HWok.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H4]]].
  - eapply rw_cells_munch; eauto. cbn [cells_size csize Nat.add]. unfold RAUXV_CELL. intros lo hi Hin Hlt.
    destruct (HWok lo hi Hin Hlt) as [D|[D|D]]; unfold alloc_ceiling, RLIBC in *; lia.
  - eapply bytes_at_munch; eauto. intros lo hi Hin Hlt. rewrite u64s_length. unfold auxv_list. rewrite length_map. cbn [length Nat.mul Nat.add].
    destruct (HWok lo hi Hin Hlt) as [D|[D|D]]; unfold alloc_ceiling, RLIBC in *; lia.
  - eapply bytes_at_munch; eauto. intros lo hi Hin Hlt. rewrite length_le8. (* [comment removed for export] *)
    destruct (HWok lo hi Hin Hlt) as [D|[D|D]]; unfold alloc_ceiling, RLIBC in *; lia.
Qed.

Lemma lhd_frame : forall SPB LB m m' mo W,
  LHEAPd SPB LB m mo -> munch W m m' -> wmono psegs m m' -> Forall (cj_write_ok SPB LB) W -> LHEAPd SPB LB m' mo.
Proof using .
  intros SPB LB m m' mo W (s & LBi & B & HR & -> & HO & HM & HA & HS) MU WM FW.
  pose proof (proj1 (Forall_forall _ _) FW) as FW'.
  assert (HB : alloc_ceiling <= B) by ((nelim HA 15%nat; intros ? ? ? ? ? ? ? ? ? ? _ _ _ HB _); exact HB).
  exists s, LBi, B. splits; auto.
  - apply (RHEAP_frame_proof s LBi m m' (nonempty_ivs W) HR (munch_nonempty _ _ _ MU) WM).
    apply Forall_forall. intros [lo hi] Hin. unfold nonempty_ivs in Hin. apply List.filter_In in Hin as [Hin Hlt]. cbn [fst snd] in Hlt. apply Z.ltb_lt in Hlt.
    specialize (FW' _ Hin). unfold cj_write_ok, rclient_write_ok in *. cbn [fst snd] in *. (* [comment removed for export] *)
    unfold PERRNO, PGERROR, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *.
    destruct FW' as [E|[ST|[ER|[GE|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    right; right. (nelim (in_bview _ _ _ HinB) 4%nat; intros b Hb <- <-). exists b. auto.
  - eapply rauxv_ok_munch; eauto. intros lo hi Hin Hlt. specialize (FW' _ Hin).
    unfold cj_write_ok in FW'. cbn [fst snd] in FW'. (* [comment removed for export] *) unfold PERRNO, PGERROR, RLIBC, alloc_ceiling in *.
    destruct FW' as [E|[ST|[ER|[GE|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    (nelim (in_bview _ _ _ HinB) 4%nat; intros b Hb <- <-).
    (nelimp (RHEAP_block_range_proof s LBi m b HR Hb) 5%nat; intros R1 R2 R3 R4 R5). unfold alloc_ceiling in R4. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lb_remove_cons : forall p b LB, lb_remove p (b :: LB) = if bptr_eqb (blk_id b) p then lb_remove p LB else b :: lb_remove p LB.
Proof using . intros p b LB. unfold lb_remove. cbn. destruct (bptr_eqb (blk_id b) p); reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true <-> p = q.
Proof using .
  intros [c o] [c' o']. unfold bptr_eqb. cbn [fst snd]. rewrite andb_true_iff, MI_Kit.aptr_eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros E; injection E as -> ->; auto].
Qed.

Lemma RHEAP_slot_nodup : forall s LBi m, RHEAP s LBi m -> List.NoDup (map blk_slot LBi).
Proof.
  intros s LBi m nelH_; (nelim nelH_ 6%nat; intros st LB0 HP _ _ [_ AR]). pose proof (mf_nodup _ _ (MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP| exact ND].
Qed.

Lemma lb_remove_notin : forall p LBi, ~ In (fst p) (map blk_slot LBi) -> lb_remove p LBi = LBi.
Proof using .
  intros p LBi. induction LBi as [|b LBi IH]; intros Hni; [reflexivity|]. rewrite lb_remove_cons.
  destruct (bptr_eqb (blk_id b) p) eqn:E.
  - exfalso. apply bptr_eqb_eq in E. apply Hni. left. unfold blk_slot, blk_id in *. rewrite E. reflexivity.
  - rewrite IH; [reflexivity|]. intros Hin. apply Hni. right. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_views : forall LBi p A n,
  List.NoDup (map blk_slot LBi) -> List.NoDup (map blk_addr LBi) -> In (p, A, n) LBi ->
  map blk_slot (lb_remove p LBi) = ap_remove (fst p) (map blk_slot LBi)
  /\ map bview (lb_remove p LBi) = cb_remove A (map bview LBi)
  /\ (forall b, In b (lb_remove p LBi) <-> In b LBi /\ b <> (p, A, n)).
Proof using .
  induction LBi as [|b LBi IH]; intros p A n NDs NDa Hin; [destruct Hin|].
  cbn [map] in NDs, NDa. inversion NDs as [|? ? Hs NDs']; subst. inversion NDa as [|? ? Ha NDa']; subst.
  rewrite lb_remove_cons. cbn [map ap_remove cb_remove bview].
  destruct Hin as [->|Hin].
  - cbn [blk_id blk_slot blk_addr blk_size fst snd]. rewrite (proj2 (bptr_eqb_eq p p) eq_refl), MI_Kit.aptr_eqb_refl, Z.eqb_refl.
    cbn [blk_slot blk_addr fst snd] in Hs, Ha. rewrite (lb_remove_notin p LBi Hs).
    splits; [reflexivity| reflexivity|]. intros b'. split.
    + intros Hb'. split; [right; exact Hb'|]. intros ->. apply Hs. apply in_map_iff. exists (p, A, n). auto.
    + intros [[<-|Hb'] Hne]; [congruence| exact Hb'].
  - assert (Hsl : blk_slot b <> fst p). { intros E. apply Hs. rewrite E. apply in_map_iff. exists (p, A, n). auto. }
    assert (Had : blk_addr b <> A). { intros E. apply Ha. rewrite E. apply in_map_iff. exists (p, A, n). auto. }
    destruct (bptr_eqb (blk_id b) p) eqn:E.
    { exfalso. apply bptr_eqb_eq in E. apply Hsl. unfold blk_slot, blk_id in *. rewrite E. reflexivity. }
    destruct (aptr_eqb (blk_slot b) (fst p)) eqn:E2. { exfalso. apply MI_Kit.aptr_eqb_eq in E2. exact (Hsl E2). }
    destruct b as [[q B] k]. cbn [blk_addr fst snd] in Had |- *. rewrite (proj2 (Z.eqb_neq B A) Had).
    (nelim (IH p A n NDs' NDa' Hin) 3%nat; intros IH1 IH2 IH3). cbn [map]. rewrite IH1, IH2. splits; [reflexivity| reflexivity|].
    intros b'. split.
    + intros [<-|Hb']; [split; [left; reflexivity| intros E3; injection E3 as -> -> ->; exact (Had eq_refl)]|].
      apply IH3 in Hb'. destruct Hb'. split; [right; assumption| assumption].
    + intros [[<-|Hb'] Hne]; [left; reflexivity| right]. apply IH3. auto.
Qed.

(* [comment removed for export] *)
Lemma cj_pres_of_rheap_pres : forall LBi SP m m', rheap_pres LBi SP m m' -> cj_pres (map bview LBi) SP m m'.
Proof.
  intros LBi SP m m' H a Ha Hc. apply H; [exact Ha|].
  unfold cj_client_addr, rclient_addr, palloc_static, ralloc_static, in_cblock, in_block in *.
  unfold PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP, PDATA_LO, PIMG_HI, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
  destruct Hc as [Hc|[Hc|(A & n & Hin & Hr)]]; [left; exact Hc| right; left; exact Hc| right; right].
  (nelim (in_bview _ _ _ Hin) 4%nat; intros b Hb <- <-). exists b. auto.
Qed.

Lemma errno_addr_PTP : bv_unsigned (wz PTP) + -164 = PERRNO.
Proof using . reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem lhd_malloc : malloc_scps_stmt LHEAPd.
Proof using .
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo SPB LB n lo errv.
  intros (s & LBi & B & HR & -> & HO & HM & HA & HS) HSP ST Hlo Hlo2 ER MI Htp Ha0 Hn.
  (* [comment removed for export] *)
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi n lo B errv
                HR HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0 Hn) as Himpl.
  pose proof (raw_malloc_etwf (map blk_slot LBi) s mo n HO ltac:(lia)) as Hwf.
  eapply scps_mono; [apply (implM_scps psegs (raw_malloc n) s _ _ _ mo Himpl HM Hwf)|].
  intros ms' mo' (r & s' & HQ & (HRr & Hfa & Hso & Hvo) & HM'). cbn [fst snd] in HRr.
  (nelim HQ 26%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv' -> MI' ST' ER' HA' HP _ _ Hr).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite Htp, errno_addr_PTP in ER'; exact ER'|].
  split; [apply cj_pres_of_rheap_pres; exact HP|].
  destruct r as [[c off]|].
  - (nelim Hr 7%nat; intros A junk -> HRng HR' RW _). (nelim HRr 4%nat; intros HO' Hni _ _). cbn [fst snd] in HO'.
    right. exists A, junk. split; [reflexivity|]. split; [exact HRng|]. split.
    + rewrite map_fst_bview. pose proof (RHEAP_addr_nodup _ _ _ HR') as ND. cbn [map blk_addr fst snd] in ND. inversion ND; assumption.
    + split; [| exact RW]. exists s'. exists (((c, off), A, n) :: LBi). exists B. splits; auto.
  - destruct Hr as [-> HR']. left. split; [reflexivity|]. exists s', LBi, B. splits; auto.
Qed.

Theorem lhd_free : free_scps_stmt LHEAPd.
Proof using .
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo SPB LB A n lo errv.
  intros (s & LBi & B & HR & -> & HO & HM & HA & HS) Hin HSP ST Hlo Hlo2 ER MI Htp Ha0.
  (* [comment removed for export] *)
  destruct (in_bview _ _ _ Hin) as ([[p A'] n'] & Hb & E1 & E2). cbn [blk_addr blk_size fst snd] in E1, E2. subst A' n'.
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi p A n lo B errv
                HR Hb HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0) as Himpl.
  assert (Hinp : In (fst p) (map blk_slot LBi)). { apply in_map_iff. exists (p, A, n). auto. }
  pose proof (raw_free_etwf (map blk_slot LBi) s mo p HO Hinp) as Hwf.
  (nelim (lb_remove_views LBi p A n (RHEAP_slot_nodup _ _ _ HR) (RHEAP_addr_nodup _ _ _ HR) Hb) 3%nat; intros V1 V2 V3).
  eapply scps_mono; [apply (implM_scps psegs (raw_free p) s _ _ _ mo Himpl HM Hwf)|].
  intros ms' mo' (r & s' & HQ & (HRr & _ & Hfa & Hso & Hvo) & HM'). cbn [fst snd] in HRr.
  (nelim HQ 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MI' ST' ER' HA' HP _ _ HR').
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite Htp, errno_addr_PTP in ER'; exact ER'|].
  rewrite <- V2. split; [apply cj_pres_of_rheap_pres; exact HP|].
  exists s', (lb_remove p LBi), B. rewrite V1. splits; auto.
Qed.

Theorem lhd_free_null : free_null_stmt.
Proof using . exact rfree_null_spec. Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
