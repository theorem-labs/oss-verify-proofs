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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxSL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWzX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWzX.
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
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QQRC.Mq6.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := QWTl.Mq5.
Module RA2 := UxSL.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_agree_but_ctx : forall st st' m m',
rmrep st m ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
A2.agree_on m m' RMLOCK 4 -> A2.agree_on m m' RLIBC 0x68 -> A2.agree_on m m' RGOT_SSP 8 -> A2.agree_on m m' RSSP_GUARD 8 ->
(forall a ar, (s_areas st) !! a = Some ar -> A2.agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> A2.agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> A2.agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
rmrep_ctx st' m' ->
rmrep st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rmrep_agree_but_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rmrep_agree_but_ctx)]. Qed.

#[using="Type"] Lemma rmrep_ctx_mid_agree : forall st st' m m',
rmrep st m -> ctx st' = ctx st \/ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
/\ (forall i, unmap_seq st' i = unmap_seq st i) /\ (forall i, bounces st' i = bounces st i) ->
s_regions st' = s_regions st ->
A2.agree_on m m' (RCTX + 80) 832 ->
u64arr rsegs m' (RCTX + 80) (actives st') /\ u64arr rsegs m' (RCTX + 464) (usages st')
/\ u8arr rsegs m' (RCTX + 848) (unmap_seqs st') /\ u8arr rsegs m' (RCTX + 880) (bouncess st').
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rmrep_ctx_mid_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rmrep_ctx_mid_agree)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QQRC.Mq6.rregions_wf) (@UQXM.rregions_wf) Q6nq.gwt_nil)).
#[using="Type"] Lemma rarea_in_live : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq6.rarea_in_live) [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]] '([4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rarea_in_live) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rarea_in_live)]. Qed.

#[using="Type"] Lemma rgroup_in_live : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq6.rgroup_in_live) [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgroup_in_live) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgroup_in_live)]. Qed.

#[using="Type"] Lemma rimage_clear_of_ranges_free : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq6.rimage_clear_of_ranges_free) [] '([65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_pat (@ref_reserved) (@ref_reserved) (Q6nq.gwt_hdr GwI.ref_reserved (@ref_reserved) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) gwt_X))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rimage_clear_of_ranges_free) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rimage_clear_of_ranges_free)]. Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

#[using="Hr"] Lemma rgr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_eq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_eq)]. Qed.
#[using="Type"] Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_regions) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_regions)]. Qed.
#[using="Type"] Lemma rgr_lookup_inv : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq6.rgr_lookup_inv) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_lookup_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_lookup_inv)]. Qed.
#[using="Type"] Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_lookup_old) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_lookup_old)]. Qed.
#[using="Type"] Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_lookup_new) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_lookup_new)]. Qed.
#[using="Hr"] Lemma rgr_conc q : conc st' q = conc st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_conc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_conc)]. Qed.
#[using="RC__ OFF OAL"] Lemma rgr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_ru) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_ru)]. Qed.

#[using="m MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rgr_regions_wf : rregions_wf st'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_regions_wf) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rgr_regions_wf)]. Qed.

#[using="MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rmrep_grow_region : rmrep st' m.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rmrep_grow_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rmrep_grow_region)]. Qed.

#[using="Type"] Lemma rptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rptrs_in_grow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rptrs_in_grow)]. Qed.
End GROW.

#[using="Type"] Lemma rimpl_enode_dec_weaken : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq6.rimpl_enode_dec_weaken) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rimpl_enode_dec_weaken) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq6.rimpl_enode_dec_weaken)]. Qed.

End RC__1.
