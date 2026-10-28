(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A MallocBlocks.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl MI_Inv MI_Ext MI_WGroup MI_WRealloc.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocFacts_inv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RMallocKit_A RMalloc_fp RF_realloc_C.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma wr32_wr8_comm' p q v w st : fst p = fst q -> snd q + 1 = snd p ->
  wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof.
  intros Hf H1. unfold wr32.
  rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

Section RESIZE_REP.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (st : mstate) (m1 : mem) (c : cptr) (off n n' : Z) (mm : aptr) (i : Z) (r : region).
Let stride := get_stride (get_meta_rec st mm).
Let P := r_base r + snd c + UNIT * off.
Let E := r_base r + snd c + stride - IB.
Let b3 := i + 32 * Z.min (stride - IB - UNIT * off - n) 5.

Hypothesis HMR : rmrep st m1.
Hypothesis TK : ticks_ok st.
Hypothesis Hs : (s_slots st) !! c = Some (mm, i).
Hypothesis Hr : (s_regions st) !! (fst c) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis C4 : 4 <= snd c.
Hypothesis CE : snd c + stride - IB + 1 <= round_up_pg (r_len r).
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst c ->
  snd b' + 9 <= snd c - 3 \/ snd c + stride - IB <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n'.
Hypothesis FIT : UNIT * off + n' <= stride - IB.
Hypothesis R32 : stride - IB - UNIT * off - n' < 2^32.
Hypothesis I0 : 0 <= i.

#[using="off n i P E b3 Hr Hk C4 CE NOGRP"] Lemma rrs_wr8 : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st -> s_groups stx = s_groups st ->
  snd c - 3 <= o < snd c + stride - IB -> 0 <= v < 256 ->
  rmrep (wr8 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst c, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv.
  split; [|apply ticks_ok_wr8; exact TKx].
  apply (rmrep_wr8 stx mx (fst c, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| unfold IB in *; lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="off n i P E b3 Hr Hk C4 CE NOGRP"] Lemma rrs_wr32 : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st -> s_groups stx = s_groups st ->
  snd c - 3 <= o -> o + 4 <= snd c + stride - IB -> 0 <= v < 2^32 ->
  rmrep (wr32 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst c, o) v stx).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv.
  apply (rmrep_wr32 stx mx (fst c, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| unfold IB in *; lia| unfold IB in *; lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="HMR TK Hs Hr Hk C4 CE NOGRP OFF0 N0 FIT R32"] Lemma rresize_mrep :
  rmrep (mresize st c off n n') (rset_size_mem m1 P E n' b3) /\ ticks_ok (mresize st c off n n')
  /\ ctrl_eq st (mresize st c off n n').
Proof.
  rewrite (mresize_eq st c off n n' mm i Hs).
  assert (ST2 : rmrep (rs_st2 st c off n n' mm i) (rset_size_mem m1 P E n' b3) /\ ticks_ok (rs_st2 st c off n n' mm i)).
  { unfold rs_st2, rs_st1. set (st1 := set_tick (N.succ (s_tick st)) st).
    assert (MR1 : rmrep st1 m1) by (apply rmrep_set_tick; exact HMR).
    assert (TK1 : ticks_ok st1) by (apply ticks_ok_set_tick; [unfold st1; cbn; lia| exact TK]).
    assert (ER1 : s_regions st1 = s_regions st) by reflexivity. assert (EG1 : s_groups st1 = s_groups st) by reflexivity.
    change (MR st mm) with (get_meta_rec st mm). fold stride.
    unfold ss_list, rset_size_mem. unfold aadd. cbn [fst snd].
    set (rsv := snd c + (stride - IB) - (snd c + UNIT * off) - n').
    assert (Ersv : E - P - n' = rsv) by (unfold rsv, E, P; lia). rewrite Ersv.
    assert (Eb3 : i + 32 * Z.min (snd c + (stride - IB) - (snd c + UNIT * off) - n) 5 = b3) by (unfold b3; f_equal; f_equal; f_equal; lia). rewrite Eb3.
    assert (RSV : 0 <= rsv < 2^32) by (unfold rsv; unfold UNIT, IB in *; lia).
    assert (KV : forall r', 0 <= r' <= 5 -> 0 <= Z.land b3 31 + Z.shiftl r' 5 < 256).
    { intros r' Hr'. rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
      assert (0 <= Z.land b3 31 < 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound b3 (2^5)); lia). lia. }
    assert (PFX : forall (o : Z) stx mx, snd c - 3 <= snd c + (stride - IB) + - o -> 0 < o ->
              rmrep stx mx -> ticks_ok stx -> s_regions stx = s_regions st -> s_groups stx = s_groups st ->
              rmrep (wr8 (fst c, snd c + (stride - IB) + - o) 0 stx) (write_to_mem mx (wa (E - o)) [b8 0]) /\ ticks_ok (wr8 (fst c, snd c + (stride - IB) + - o) 0 stx)).
    { intros o stx mx Ho Ho' MRx TKx ERx EGx.
      replace (E - o) with (r_base r + (snd c + (stride - IB) + - o)) by (unfold E; lia).
      apply (rrs_wr8 stx mx _ 0 MRx TKx ERx EGx); lia. }
    assert (PL : forall stx mx r', 0 <= r' <= 5 -> rmrep stx mx -> ticks_ok stx -> s_regions stx = s_regions st -> s_groups stx = s_groups st ->
              rmrep (wr8 (fst c, snd c + UNIT * off + -3) (Z.land b3 31 + Z.shiftl r' 5) stx) (write_to_mem mx (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)])
              /\ ticks_ok (wr8 (fst c, snd c + UNIT * off + -3) (Z.land b3 31 + Z.shiftl r' 5) stx)).
    { intros stx mx r' Hr' MRx TKx ERx EGx.
      replace (P - 3) with (r_base r + (snd c + UNIT * off + -3)) by (unfold P; lia).
      apply (rrs_wr8 stx mx _ _ MRx TKx ERx EGx); [unfold UNIT, IB in *; lia| apply KV; lia]. }
    destruct (Z.eqb_spec rsv 0) as [R0|RN0]; [| destruct (Z.leb_spec 5 rsv) as [R5|R5]]; cbn [negb app wrs].
    -
      replace (5 <=? rsv) with false by (symmetry; apply Z.leb_gt; lia). cbn [app wrs].
      apply (PL st1 m1 rsv ltac:(lia) MR1 TK1 ER1 EG1).
    -
      destruct (PFX rsv st1 m1 ltac:(unfold rsv; unfold UNIT, IB in *; lia) ltac:(lia) MR1 TK1 ER1 EG1) as [MA TA].
      set (stA := wr8 _ 0 st1) in MA, TA |- *. set (mA := write_to_mem m1 _ _) in MA |- *.
      change (wr8 (fst c, snd c + (stride - IB) + -5) 0
                (wr8 (fst c, snd c + (stride - IB) + -4 + 3) (Z.shiftr rsv 24) (wr8 (fst c, snd c + (stride - IB) + -4 + 2) (Z.shiftr rsv 16)
                  (wr8 (fst c, snd c + (stride - IB) + -4 + 1) (Z.shiftr rsv 8) (wr8 (fst c, snd c + (stride - IB) + -4) rsv stA)))))
        with (wr8 (fst c, snd c + (stride - IB) + -5) 0 (wr32 (fst c, snd c + (stride - IB) + -4) rsv stA)).
      rewrite (wr32_wr8_comm' (fst c, snd c + (stride - IB) + -4) (fst c, snd c + (stride - IB) + -5)) by (cbn; lia || reflexivity).
      destruct (PFX 5 stA mA ltac:(unfold UNIT, IB in *; lia) ltac:(lia) MA TA eq_refl eq_refl) as [MB TB].
      destruct (rrs_wr32 _ _ (snd c + (stride - IB) + -4) rsv MB TB eq_refl eq_refl) as [MC TC]; [unfold UNIT, IB in *; lia| unfold UNIT, IB in *; lia| lia|].
      replace (E - 4) with (r_base r + (snd c + (stride - IB) + -4)) by (unfold E; lia).
      apply (PL _ _ 5 ltac:(lia) MC TC eq_refl eq_refl).
    -
      destruct (PFX rsv st1 m1 ltac:(unfold rsv; unfold UNIT, IB in *; lia) ltac:(lia) MR1 TK1 ER1 EG1) as [MA TA].
      apply (PL _ _ rsv ltac:(lia) MA TA eq_refl eq_refl). }
  destruct ST2 as [M2 T2].
  destruct (rmrep_havoc _ _ (aadd c (UNIT * off)) n' M2 T2) as [M3 T3].
  split; [exact M3|]. split; [exact T3|]. exact (proj1 (st3_ctrl st c off n n' mm i)).
Qed.
End RESIZE_REP.
