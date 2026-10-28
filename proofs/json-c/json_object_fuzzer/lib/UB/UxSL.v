(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QWTl.Mq5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
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
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qy8Z.Mqa.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

#[using="Hconc"] Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rpw_extP) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rpw_extP)]. Qed.

#[using="Hmetas"] Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rget_meta_rec_extP) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rget_meta_rec_extP)]. Qed.

#[using="P HP Hconc"] Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmeta_cells_extP) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmeta_cells_extP)]. Qed.

#[using="P HP Hconc Hctx"] Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_ctx_extP) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_ctx_extP)]. Qed.

#[using="P HP Hconc Hmetas"] Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rarea_rep_extP) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rarea_rep_extP)]. Qed.

#[using="P HP Hconc"] Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rgroup_rep_extP) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rgroup_rep_extP)]. Qed.
End PEXT.

#[using="Type"] Lemma rbytes_at_agree m m' A bs : bytes_at rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rbytes_at_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rbytes_at_agree)]. Qed.

#[using="Type"] Lemma rwr_at_agree m m' A n : wr_at rsegs m A n -> agree_on m m' A n -> wr_at rsegs m' A n.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rwr_at_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rwr_at_agree)]. Qed.

#[using="Type"] Lemma rrw_cells_agree m m' A cs : rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rrw_cells_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rrw_cells_agree)]. Qed.

#[using="Type"] Lemma ru64arr_agree m m' A ws : u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.ru64arr_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.ru64arr_agree)]. Qed.

#[using="Type"] Lemma ru8arr_agree m m' A bs : u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr rsegs m' A bs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.ru8arr_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.ru8arr_agree)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Qy8Z.Mqa.rmrep) (@UQXM.rmrep) Q6nq.gwt_nil)).
#[using="Type"] Lemma rmrep_agree : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mqa.rmrep_agree) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([1168; 4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_zc RLIBC (Q6nq.gwt_zc RGOT_SSP (Q6nq.gwt_pat (@RGOT_SSP) (@RGOT_SSP) (Q6nq.gwt_hdr GwI.RGOT_SSP (@RGOT_SSP) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_agree)]. Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.

Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

#[using="Type"] Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_regions) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_regions)]. Qed.
#[using="Type"] Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_lookup_new) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_lookup_new)]. Qed.
#[using="r0"] Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_lookup_old) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_lookup_old)]. Qed.
#[using="Type"] Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_lookup_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_lookup_inv)]. Qed.
#[using="r0"] Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_conc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_conc)]. Qed.
#[using="r0"] Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_conc_new) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_conc_new)]. Qed.
#[using="Type"] Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_shadow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_shadow)]. Qed.
#[using="RC__ st m' rid L ZF"] Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_lr_lo_new) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_lr_lo_new)]. Qed.

#[using="RC__ rid RF"] Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_old_disjoint) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_old_disjoint)]. Qed.

#[using="m m' rid L r0 MR PT X0 XA LEN XC RF ZF"] Lemma rnr_regions_wf : rregions_wf st'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_X0__3; @gw_eq_X0__2; @gw_eq_X0]; [@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_regions_wf) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rnr_regions_wf)]. Qed.

#[using="m rid L r0 MR PT FRs X0 XA LEN XC RF AG ZF"] Lemma rmrep_new_region : rmrep st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_X0__3; @gw_eq_X0__2; @gw_eq_X0]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_new_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_new_region)]. Qed.

#[using="Type"] Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rticks_ok_new_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rticks_ok_new_region)]. Qed.

#[using="Type"] Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rptrs_in_new_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rptrs_in_new_region)]. Qed.
End NEWREGION.

Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
(RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x490 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
\/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
m' (wa a) = m (wa a).

#[using="Type"] Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_regions) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_regions)]. Qed.
#[using="Type"] Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_lookup_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_lookup_inv)]. Qed.
#[using="Type"] Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_lookup_old) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_lookup_old)]. Qed.
#[using="Type"] Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_conc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_conc)]. Qed.
#[using="Type"] Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_shadow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rdr_shadow)]. Qed.

#[using="m r MR Hr PT AG"] Lemma rmrep_drop_region : rmrep st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_drop_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_drop_region)]. Qed.

#[using="Type"] Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rticks_ok_drop_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rticks_ok_drop_region)]. Qed.
End DROPREGION.

#[using="Type"] Lemma rmrep_put_group_new : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mqa.rmrep_put_group_new) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_put_group_new) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_put_group_new)]. Qed.

#[using="Type"] Lemma rmrep_set_mmap_counter : forall st m v,
rmrep st m -> 0 <= v < 2^32 ->
rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_set_mmap_counter) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mqa.rmrep_set_mmap_counter)]. Qed.

End RC__1.
