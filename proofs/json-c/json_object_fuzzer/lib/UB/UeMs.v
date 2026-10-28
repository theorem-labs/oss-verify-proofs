(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qc3B QZAi QfYR Q7wb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK UxDK UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QfYR.
Import Q7wb.
Import UjdK UxDK.
Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition RSTRTOD : Z := 0x5b4fc.
Definition RSSCANF : Z := 0x25bcc.
Definition RFMT_LG : Z := 0x102ac.
Definition RATP : Z := 0x77c00.
Definition RERRNO : Z := 0x77b5c.
Definition RGLOBALS_TOP : Z := 0x99000.
Definition RIMG_LO : Z := 65536.

Definition RSTRTOD_DEPTH : Z := 8928.
Definition RSSCANF_DEPTH : Z := 9504.

Definition rstrtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(T PE : Z) (txt : list Z) (npre bits used lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (PE, PE + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
/\ reg_get F' 10 = Z_to_bv 64 bits
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' PE [C8 (Z_to_bv 64 (T + used))]
/\ bytes_at rsegs m' T (map (Z_to_bv 8) txt)
/\ ssp_cells m' canary
/\ rw_cells rsegs m' RERRNO [C4 ev']
/\ 0 <= used <= npre.

Definition rstrtod_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
bytes_at rsegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> zlength pre < 2^30 -> zlength txt <= 2^40 ->
rw_cells rsegs m PE [C8 ejunk] ->
scan_strtod txt = Some (bits, used) ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSTRTOD_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
0 < T ->
(((T + zlength txt <= RIMG_LO \/ RGLOBALS_TOP <= T) /\ T + zlength txt <= lo) \/ bv_unsigned sp <= T) ->

T + 2^41 <= 2^63 -> bv_unsigned sp <= PE -> PE + 8 <= 2^63 ->
(PE + 8 <= T \/ T + zlength txt <= PE) ->
ssp_cells m canary -> rw_cells rsegs m RERRNO [C4 ev] ->
mem_inv rsegs m -> frm0 fc ->
tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
evt rsegs (rstrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RSTRTOD) fc None m (seg_rom rsegs)).

Definition rsscanf_lg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(T PD : Z) (txt : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (PD, PD + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' PD [C8 (match res with Some bits => Z_to_bv 64 bits | None => djunk end)]
/\ bytes_at rsegs m' T (map (Z_to_bv 8) txt)
/\ ssp_cells m' canary
/\ rw_cells rsegs m' RERRNO [C4 ev'].

Definition rsscanf_lg_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
bytes_at rsegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
(T + zlength txt) mod 8 = 0 -> zlength txt <= 256 ->
rw_cells rsegs m PD [C8 djunk] ->
scan_sscanf_lg txt = Some (r, res) ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSSCANF_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
bv_unsigned sp <= T -> T + 2^41 <= 2^63 -> bv_unsigned sp <= PD -> PD + 8 <= 2^63 ->
(PD + 8 <= T \/ T + zlength txt <= PD) ->
ssp_cells m canary -> rw_cells rsegs m RERRNO [C4 ev] ->
mem_inv rsegs m -> frm0 fc ->
tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 RFMT_LG -> a2 = Z_to_bv 64 PD ->
evt rsegs (rsscanf_lg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RSSCANF) fc None m (seg_rom rsegs)).
End Mq0.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Q8P7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBeb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QBeb.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Module GwI.
Definition segs := tt.
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

Notation RAMpre := (@AMpre_g ref_reserved rc_secret).
Notation ram_pre := (am_pre_g ref_reserved rc_secret).
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PURE.
Variable st : mstate.
Hypothesis AMP : RAMpre st.

#[using="AMP"] Lemma rAMpre_init : RAMpre (am_init_st st).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMpre_init) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMpre_init)]. Qed.

#[using="Type"] Lemma ram_init_regions : s_regions (am_init_st st) = s_regions st.
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_init_regions) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_init_regions)]. Qed.
#[using="Type"] Lemma ram_init_brk : c_brk (ctx (am_init_st st)) = c_brk (ctx st).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_init_brk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_init_brk)]. Qed.
#[using="Type"] Lemma ram_init_conc q : conc (am_init_st st) q = conc st q.
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_init_conc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_init_conc)]. Qed.

#[using="RC__ AMP"] Lemma rAMI_init : AMI st (am_init_st st).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMI_init) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMI_init)]. Qed.

#[using="Type"] Lemma rptrs_in_upd_ctx : ltac2:(Q6nq.ty2 'UeMs.GwI.segs '(@Q8l1.rptrs_in_upd_ctx) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rptrs_in_upd_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rptrs_in_upd_ctx)]. Qed.

#[using="Type"] Lemma ram_rel_final : ltac2:(Q6nq.ty2 'UeMs.GwI.segs '(@Q8l1.ram_rel_final) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_final) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_final)]. Qed.

#[using="Type"] Lemma ram_rel_none stX : AMI st stX -> am_rel st stX None.
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_none) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_none)]. Qed.

#[using="Type"] Lemma ram_rel_take : ltac2:(Q6nq.ty2 'UeMs.GwI.segs '(@Q8l1.ram_rel_take) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_take) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_take)]. Qed.

#[using="Type"] Lemma ram_rel_carve : ltac2:(Q6nq.ty2 'UeMs.GwI.segs '(@Q8l1.ram_rel_carve) [] '([100]%Z : list Z) '(Q6nq.gwt_zc NSLOTS (Q6nq.gwt_zc META_SIZE (Q6nq.gwt_zc AREA_HDR Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_carve) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_carve)]. Qed.

#[using="Type"] Lemma ram_rel_deq : ltac2:(Q6nq.ty2 'UeMs.GwI.segs '(@Q8l1.ram_rel_deq) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_deq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.ram_rel_deq)]. Qed.

#[using="Type"] Lemma rAMI_ctx : ltac2:(Q6nq.ty2 'UeMs.GwI.segs '(@Q8l1.rAMI_ctx) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMI_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMI_ctx)]. Qed.

#[using="Type"] Lemma rAMI_new_region : ltac2:(Q6nq.ty2 'UeMs.GwI.segs '(@Q8l1.rAMI_new_region) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMI_new_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMI_new_region)]. Qed.

#[using="Type"] Lemma rAMI_grow stX rid r off :
AMI st stX -> (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> r_len r = off ->
let st' := set_regions (<[rid := mkRegion (r_kind r) (r_base r) (off + 4096)]> (s_regions stX)) stX in
AMI st st' /\ (forall q, conc st' q = conc stX q) /\ (s_regions st') !! rid = Some (mkRegion (r_kind r) (r_base r) (off + 4096)).
Proof. first [GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMI_grow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UeMs.GwI.segs (@Q8l1.rAMI_grow)]. Qed.
End PURE.

End RC__1.
