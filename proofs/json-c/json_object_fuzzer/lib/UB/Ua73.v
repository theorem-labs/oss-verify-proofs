(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFkE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKaC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKaC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoCS.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxSL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
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
Lemma LAY_win_1 : ltac2:(GwEq.gw_fact_ty 'segs '(@QQRC.Mqb.gw_all) @LAY_win_1). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_2 : ltac2:(GwEq.gw_fact_ty 'segs '(@QQRC.Mqb.gw_all) @LAY_win_2). Proof. GwApply.gw_side. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QQRC.Mqb.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma LAY_ref_reserved : ltac2:(GwEq.gw_fact_ty 'segs '(@QQRC.Mqb.gw_all) @LAY_ref_reserved). Proof. GwApply.gw_side. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ptrs_in_but (rid : N) (g b : aptr) (st : mstate) : Prop :=
let P := fun x : N => x <> rid in
let c := ctx st in
optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
/\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
/\ (forall sc, optr_in P (active st sc))
/\ match c_brk c with BrkLive q _ => P q | _ => True end
/\ (forall g', optr_in P (m_prev (get_meta_rec st g')) /\ optr_in P (m_next (get_meta_rec st g'))
/\ (g' <> g -> optr_in P (m_mem (get_meta_rec st g'))))
/\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
/\ (forall b' gh, (s_groups st) !! b' = Some gh -> (b' <> b -> P (fst b')) /\ optr_in P (g_meta gh)).
Lemma gw_eq_ptrs_in_but : @ptrs_in_but = ltac:(GwInst.gw_term (@QQRC.Mqb.ptrs_in_but) (@ptrs_in_but)). Proof. unfold ptrs_in_but, QQRC.Mqb.ptrs_in_but; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ptrs_in_but : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QQRC.Mqb.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QQRC.Mqb.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QQRC.Mqb.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QQRC.Mqb.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QQRC.Mqb.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QQRC.Mqb.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QQRC.Mqb.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QQRC.Mqb.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QQRC.Mqb.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QQRC.Mqb.rarea_rep) (@UQXM.rarea_rep) Q6nq.gwt_nil)))))))))))))))))))).
#[using="Type"] Lemma bytes_at_pointwise : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.bytes_at_pointwise) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.bytes_at_pointwise) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.bytes_at_pointwise)]. Qed.

#[using="Type"] Lemma rwr_at_of_bytes : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rwr_at_of_bytes) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '([65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rwr_at_of_bytes) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rwr_at_of_bytes)]. Qed.

#[using="Type"] Lemma bytes_at_agree m m' A bs : bytes_at rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.bytes_at_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.bytes_at_agree)]. Qed.

Section REMAP.
Variables (st : mstate) (m m' : word -> option byte) (rid : N) (r : region) (g b : aptr) (ai : Z) (nb nd : Z).
Let ol := round_up_pg (r_len r).
Let mr := get_meta_rec st g.
Let st' := remap_region rid nb nd g st.
Let G := conc st g.
Let mr' := m_set_maplen (nd / 4096) mr.

Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Hb : (s_groups st) !! b = Some (mkGhdr (Some g) ai).
Hypothesis Fb : fst b = rid.
Hypothesis Sb : snd b = 0.
Hypothesis MSg : meta_slot st g.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis PT : ptrs_in_but rid g b st.
Hypothesis NB0 : 0 < nb.
Hypothesis NBA : nb mod 4096 = 0.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis ND16 : 16 <= nd.
Hypothesis NBC : nb + nd <= alloc_ceiling.

Hypothesis RFI : ranges_free ref_reserved nb nd = true.
Hypothesis RFX : forall q r', (s_regions st) !! q = Some r' -> q <> rid -> nb + nd <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb.

Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < nb \/ nb + nd <= a) -> (a < r_base r \/ r_base r + ol <= a) ->
(a < G + 16 \/ G + 24 <= a) -> (a < G + 32 \/ G + 40 <= a) -> m' (wa a) = m (wa a).
Hypothesis CP : forall o, 0 <= o < Z.min ol nd -> m' (wa (nb + o)) = m (wa (r_base r + o)).
Hypothesis ZF : forall o, ol <= o < nd -> m' (wa (nb + o)) = Some (b8 0).
Hypothesis MW1 : bytes_at rsegs m' (G + 16) (le8 (wz nb)).
Hypothesis MW2 : bytes_at rsegs m' (G + 32) (le8 (wz (meta_word mr'))).
Hypothesis MWo : forall a, G <= a < G + 16 \/ G + 24 <= a < G + 32 -> m' (wa a) = m (wa a).

Hypothesis SHX : forall o v, Z.min ol nd <= o < nd -> cell_read (get_shadow st' rid) o = Known v -> v = 0.
Hypothesis SHK : forall o v, 0 <= o < Z.min ol nd -> cell_read (get_shadow st' rid) o = Known v -> cell_read (get_shadow st rid) o = Known v.

#[using="r Hr"] Lemma rmr_regions : s_regions st' = <[rid := mkRegion RKGroup nb nd]> (s_regions st).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_regions) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_regions)]. Qed.
#[using="r Hr"] Lemma rmr_lookup_new : (s_regions st') !! rid = Some (mkRegion RKGroup nb nd).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_lookup_new) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_lookup_new)]. Qed.
#[using="r Hr"] Lemma rmr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_lookup_old) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_lookup_old)]. Qed.
#[using="r Hr"] Lemma rmr_lookup_inv : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rmr_lookup_inv) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_lookup_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_lookup_inv)]. Qed.
#[using="r Hr"] Lemma rmr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_conc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_conc)]. Qed.
#[using="r Hr"] Lemma rmr_conc_new off : conc st' (rid, off) = nb + off.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_conc_new) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_conc_new)]. Qed.
#[using="r Hr"] Lemma rmr_groups : s_groups st' = s_groups st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_groups) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_groups)]. Qed.
#[using="r Hr"] Lemma rmr_areas : s_areas st' = s_areas st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_areas) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_areas)]. Qed.
#[using="r Hr"] Lemma rmr_ctx : ctx st' = ctx st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_ctx)]. Qed.
#[using="r Hr"] Lemma rmr_reserved : s_reserved st' = s_reserved st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_reserved) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_reserved)]. Qed.
#[using="r Hr"] Lemma rmr_tick : s_tick st' = s_tick st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_tick) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_tick)]. Qed.
#[using="r Hr"] Lemma rmr_meta_other q : q <> g -> get_meta_rec st' q = get_meta_rec st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_meta_other) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_meta_other)]. Qed.
#[using="r Hr"] Lemma rmr_meta_g : get_meta_rec st' g = mr'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_meta_g) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_meta_g)]. Qed.
#[using="r Hr"] Lemma rmr_shadow_other q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_shadow_other) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_shadow_other)]. Qed.
#[using="r Hr"] Lemma rmr_active sc : active st' sc = active st sc.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_active) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_active)]. Qed.

Let WF := proj1 MR.

#[using="st m rid MR Hr WF"] Lemma rmr_r_facts : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rmr_r_facts) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '([4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_pat (@ref_reserved) (@ref_reserved) (Q6nq.gwt_hdr GwI.ref_reserved (@ref_reserved) gwt_X)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_r_facts) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_r_facts)]. Qed.

#[using="m r b nb nd ol MR Hr Kr Fb MSg NB0 ND16 WF"] Lemma rmr_g_facts : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rmr_g_facts) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_g_facts) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_g_facts)]. Qed.

#[using="RC__ st m rid g b nb nd G MR Hr Fb NB0 ND16 WF"] Lemma rmr_ol_ge : r_len r <= ol /\ ol mod 4096 = 0 /\ 0 <= ol.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_ol_ge) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_ol_ge)]. Qed.

#[using="RC__ st rid r g b nb ol G Fb NDA"] Lemma rmr_nd_round : round_up_pg nd = nd.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_nd_round) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_nd_round)]. Qed.

Hypothesis ONLYB : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = rid -> b' = b.

#[using="m r b ol G MR Hr Fb Sb PT NB0 NBA NDA ND16 NBC RFI RFX WF ONLYB"] Lemma rmr_regions_wf : rregions_wf st'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]]); first [ (pose proof PT as gw_h_; clear PT; rewrite ?gw_eq_ptrs_in_but in gw_h_; rename gw_h_ into PT) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_regions_wf) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_regions_wf)]. Qed.

#[using="RC__ rid b Fb NB0 ND16 AG"] Lemma rmr_agree : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rmr_agree) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_agree)]. Qed.

#[using="RC__ st rid r g b nb nd ol G MR Hr Kr Fb MSg NB0 ND16 RFI AG WF"] Lemma rmr_agree_image A n : 0x10000 <= A -> A + n <= 0x99000 -> agree_on m m' A n.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_agree_image) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_agree_image)]. Qed.

#[using="Type"] Lemma rmr_rw_cells_agree A cs : rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rw_cells_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rw_cells_agree)]. Qed.

#[using="RC__ m r b ol G MR Hr Kr Fb MSg PT NB0 ND16 RFI AG WF"] Lemma rmr_rep_ctx : rmrep_ctx st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]]); first [ (pose proof PT as gw_h_; clear PT; rewrite ?gw_eq_ptrs_in_but in gw_h_; rename gw_h_ into PT) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_ctx)]. Qed.

#[using="st m rid r g b nb nd ol G MR Hr Kr Fb MSg NB0 ND16 RFI AG WF"] Lemma rmr_rep_globals : rmrep_globals m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rmrep_globals__3; @gw_eq_rmrep_globals__2; @gw_eq_rmrep_globals]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_globals) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_globals)]. Qed.

#[using="m g b G MR Hr Kr Fb NB0 NBA NDA ND16 RFX WF"] Lemma rmr_area_facts : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rmr_area_facts) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '([4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_area_facts) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_area_facts)]. Qed.

#[using="RC__ m rid r g b nb nd ol G MR Fb NB0 ND16 WF"] Lemma rmr_area_sep : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rmr_area_sep) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '([4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_area_sep) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_area_sep)]. Qed.

#[using="RC__ m rid r b nb nd ol MR Fb MSg WF"] Lemma rmr_g_area : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rmr_g_area) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '(@nil Z) '(Q6nq.gwt_zc NSLOTS (Q6nq.gwt_zc META_SIZE (Q6nq.gwt_zc AREA_HDR gwt_X)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_g_area) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_g_area)]. Qed.

#[using="RC__ m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 RFX AG MW1 MW2 MWo SHX SHK WF ONLYB"] Lemma rmr_rep_areas : rmrep_areas st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]]); first [ (pose proof PT as gw_h_; clear PT; rewrite ?gw_eq_ptrs_in_but in gw_h_; rename gw_h_ into PT) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_areas) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_areas)]. Qed.

#[using="RC__ m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP MW1 MW2 MWo SHX SHK WF ONLYB"] Lemma rmr_rep_groups : rmrep_groups st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]]); first [ (pose proof PT as gw_h_; clear PT; rewrite ?gw_eq_ptrs_in_but in gw_h_; rename gw_h_ into PT) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_groups) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_groups)]. Qed.

#[using="RC__ m r b ol G MR Hr Kr Fb MSg PT NB0 NDA ND16 NBC RFI RFX AG CP ZF SHX SHK WF ONLYB"] Lemma rmr_rep_shadow : rmrep_shadow st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]]); first [ (pose proof PT as gw_h_; clear PT; rewrite ?gw_eq_ptrs_in_but in gw_h_; rename gw_h_ into PT) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_shadow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmr_rep_shadow)]. Qed.

#[using="m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK WF ONLYB"] Theorem rmrep_remap : rmrep st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [ (pose proof PT as gw_h_; clear PT; rewrite ?gw_eq_ptrs_in_but in gw_h_; rename gw_h_ into PT) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmrep_remap) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rmrep_remap)]. Qed.

End REMAP.

#[using="Type"] Lemma ranges_free_except_In : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.ranges_free_except_In) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.ranges_free_except_In) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.ranges_free_except_In)]. Qed.

#[using="Type"] Lemma rr_answer_cases (live : list (Z * Z)) (B ol nd : Z) (x : mremap_ans) :
let zz := match x with MrErr e => neg_errno e | MrInPlace => B | MrMoved a => a end in
mremap_answer_ok live B ol nd zz = true ->
match x with
| MrErr e => e = 12
| MrInPlace => True
| MrMoved a => (a mod 4096 = 0 /\ 0 < a /\ a + nd <= alloc_ceiling) /\ avoids a nd [] = true /\ a <> B mod 2^64
end ->
0 < B -> 0 < ol -> 0 < nd -> ol <> nd -> ol mod 4096 = 0 -> nd mod 4096 = 0 -> B + ol <= alloc_ceiling ->
(B + ol <= 0x10000 \/ 0x99000 <= B) ->
In (B, ol) live -> (forall y, In y ref_reserved -> In y live) ->
match x with
| MrErr e => is_err zz = true
| MrInPlace => is_err zz = false /\ (nd < ol \/ (ol < nd /\ B + nd <= alloc_ceiling /\ (B + nd <= 0x10000 \/ 0x99000 <= B + ol)
/\ forall b0 k, In (b0, k) live -> b0 <> B -> B + nd <= b0 \/ b0 + k <= B + ol))
| MrMoved a => is_err zz = false /\ ol < nd /\ (a + nd <= 0x10000 \/ 0x99000 <= a) /\ (B + ol <= a \/ a + nd <= B)
/\ ranges_free live a nd = true
end.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rr_answer_cases) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rr_answer_cases)]. Qed.

#[using="Type"] Lemma rptrs_in_but : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.rptrs_in_but) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_ptrs_in_but]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ptrs_in_but; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rptrs_in_but) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.rptrs_in_but)]. Qed.

#[using="Type"] Lemma ticks_ok_remap_region rid nb nd g st : ticks_ok st -> ticks_ok (remap_region rid nb nd g st).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.ticks_ok_remap_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.ticks_ok_remap_region)]. Qed.

#[using="Type"] Lemma strip_remap_fin : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.strip_remap_fin) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.strip_remap_fin) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.strip_remap_fin)]. Qed.

#[using="Type"] Lemma get_stride_remap : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.get_stride_remap) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '([4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.get_stride_remap) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.get_stride_remap)]. Qed.

#[using="Type"] Lemma ctx_havoc' p n st : ctx (havoc p n st) = ctx st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.ctx_havoc') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.ctx_havoc')]. Qed.
#[using="Type"] Lemma ctx_set_size' p e n b st : ctx (set_size p e n b st) = ctx st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.ctx_set_size') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.ctx_set_size')]. Qed.

#[using="Type"] Lemma write_other : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqb.write_other) [[@gw_eq_ptrs_in_but__3; @gw_eq_ptrs_in_but__2; @gw_eq_ptrs_in_but]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.write_other) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.write_other)]. Qed.

Section FIN.
Variables (st : mstate) (rid : N) (r : region) (g : aptr) (nb nd : Z) (p e : aptr) (n k : Z).
Hypothesis Hr : (s_regions st) !! rid = Some r.
Let stR := remap_region rid nb nd g st.
Let stW := wr8 e 0 stR.
Let stF := havoc p n (set_size p e n k stW).

#[using="r Hr"] Lemma fin_regions_R : s_regions stR = <[rid := mkRegion RKGroup nb nd]> (s_regions st).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_regions_R) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_regions_R)]. Qed.
#[using="Type"] Lemma fin_regions_W : s_regions stW = s_regions stR.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_regions_W) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_regions_W)]. Qed.
#[using="r Hr"] Lemma fin_lookup_W : (s_regions stW) !! rid = Some (mkRegion RKGroup nb nd).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_lookup_W) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_lookup_W)]. Qed.
#[using="r Hr"] Lemma fin_groups_W : s_groups stW = s_groups st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_groups_W) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_groups_W)]. Qed.
#[using="r Hr"] Lemma fin_meta_W : get_meta_rec stW g = m_set_maplen (nd / 4096) (get_meta_rec st g).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_meta_W) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_meta_W)]. Qed.
#[using="r Hr"] Lemma fin_conc q : conc stF q = if (fst q =? rid)%N then nb + snd q else conc st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_conc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_conc)]. Qed.
#[using="r Hr"] Lemma fin_ctx : ctx stF = ctx st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_ctx)]. Qed.
#[using="r Hr"] Lemma fin_brk_link pb : match c_brk (ctx st) with BrkLive q _ => q <> rid | _ => True end -> brk_link st pb -> brk_link stF pb.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_brk_link) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqb.fin_brk_link)]. Qed.
End FIN.

End RC__1.
Lemma gw_eq_ptrs_in_but__2 : @ptrs_in_but = ltac:(GwInst.gw_term (@QQRC.Mqb.ptrs_in_but) (@ptrs_in_but)). Proof. unfold ptrs_in_but, QQRC.Mqb.ptrs_in_but; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ptrs_in_but__2 : gw_eqs.
