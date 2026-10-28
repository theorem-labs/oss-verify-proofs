(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QPjm.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rimplT_guard {R} o t (c : bool) (k bail : QUZl.M R) s Q ms :
(c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_guard) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_guard)]. Qed.

#[using="Type"] Lemma rimplT_rd8 {R} o st q (k : Z -> QUZl.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_rd8) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_rd8)]. Qed.

#[using="Type"] Lemma rimplT_rd16 {R} o st q (k : Z -> QUZl.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_rd16) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_rd16)]. Qed.

#[using="Type"] Lemma rimplT_rd32 {R} o st q (k : Z -> QUZl.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
+ 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
rimplT o (rd32 st q k) s Q ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_rd32) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_rd32)]. Qed.

#[using="Type"] Lemma rimplT_if {R} o (c : bool) (t1 t2 : QUZl.M R) s Q ms :
(c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_if) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rimplT_if)]. Qed.

#[using="Type"] Lemma rrdv_range : forall o st m q r,
rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
0 <= rdv pans_mem o st q < 256.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rrdv_range) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rrdv_range)]. Qed.

#[using="Type"] Lemma rrdv_cur : forall o st mX q r (x : byte),
rmrep st mX ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
(forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
bytes_at rsegs mX (r_base r + snd q) [x] ->
rdv pans_mem o st q = bv_unsigned x.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rrdv_cur) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rrdv_cur)]. Qed.

#[using="Type"] Lemma rwview_ext : forall m m' a, m' a = m a -> wview rsegs m' a = wview rsegs m a.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rwview_ext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rwview_ext)]. Qed.

#[using="Type"] Lemma rwr_at_agree : forall m m' A n, wr_at rsegs m A n -> agree_on m m' A n -> wr_at rsegs m' A n.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rwr_at_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rwr_at_agree)]. Qed.

#[using="Type"] Lemma rrw_cells_agree' : forall m m' A cs,
rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rrw_cells_agree') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rrw_cells_agree')]. Qed.

#[using="Type"] Lemma ru64arr_agree' : forall m m' A ws,
u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.ru64arr_agree') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.ru64arr_agree')]. Qed.

#[using="Type"] Lemma ru8arr_agree' : forall m m' A bs,
u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr rsegs m' A bs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.ru8arr_agree') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.ru8arr_agree')]. Qed.

#[using="Type"] Lemma rstk_agree : forall m m' lo hi, stk rsegs m lo hi -> agree_on m m' lo (hi - lo) -> stk rsegs m' lo hi.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rstk_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rstk_agree)]. Qed.

Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).
Lemma gw_eq_rgrp_region_addr : @rgrp_region_addr = ltac:(GwInst.gw_term (@QkTt.Mq3.rgrp_region_addr) (@rgrp_region_addr)). Proof. unfold rgrp_region_addr, QkTt.Mq3.rgrp_region_addr; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rgrp_region_addr : gw_eqs.

#[using="Type"] Lemma rmrep_transport_agree : forall st m m',
rmrep st m ->
(forall a, 0 <= a < 2^64 -> rrepfoot st a -> m' (wa a) = m (wa a)) ->
(forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None) ->
rmrep st m'.
Proof. rewrite ?gw_eq_rgrp_region_addr; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rmrep_transport_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rmrep_transport_agree)]. Qed.

#[using="Type"] Lemma rmrep_transport_agree' : forall st m m',
rmrep st m ->
(forall a, 0 <= a < 2^64 -> rrepfoot st a \/ rgrp_region_addr st a -> m' (wa a) = m (wa a)) ->
rmrep st m'.
Proof. rewrite ?gw_eq_rgrp_region_addr; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rmrep_transport_agree') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rmrep_transport_agree')]. Qed.

#[using="Type"] Lemma rpres_except_of_munch_nw : forall C W m m',
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rpres_except_of_munch_nw) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rpres_except_of_munch_nw)]. Qed.

#[using="Type"] Lemma rpres_except_agree : forall C m m' A n,
rpres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rpres_except_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.rpres_except_agree)]. Qed.

#[using="Type"] Lemma ru64arr_pres : forall C m m' A ws,
rpres_except C m m' -> u64arr rsegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr rsegs m' A ws.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.ru64arr_pres) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.ru64arr_pres)]. Qed.

#[using="Type"] Lemma ru8arr_pres : forall C m m' A bs,
rpres_except C m m' -> u8arr rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr rsegs m' A bs.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.ru8arr_pres) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq3.ru8arr_pres)]. Qed.

End RC__1.
Lemma gw_eq_rgrp_region_addr__2 : @rgrp_region_addr = ltac:(GwInst.gw_term (@QkTt.Mq3.rgrp_region_addr) (@rgrp_region_addr)). Proof. unfold rgrp_region_addr, QkTt.Mq3.rgrp_region_addr; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rgrp_region_addr__2 : gw_eqs.
