(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFkE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKNz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQXM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv2Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIMz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpkF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1ti. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdkX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdkX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXT6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOpO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaiD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x51e40%Z.
Definition w_37 := 0x00044797%Z.
Definition w_39 := 0x31c7b783%Z.
Definition w_47 := 0xfffc4817%Z.
Definition w_48 := 0x61c80813%Z.
Definition w_76 := 0xfffc4597%Z.
Definition w_77 := 0x5a858593%Z.
Definition w_87 := 0xfffc4517%Z.
Definition w_88 := 0x57c50513%Z.
Definition hi_37 := (Z_to_bv 20 68).
Definition hi_47 := (Z_to_bv 20 1048516).
Definition hi_76 := (Z_to_bv 20 1048516).
Definition hi_87 := (Z_to_bv 20 1048516).
Definition lo_39 := (Z_to_bv 12 796).
Definition lo_48 := (Z_to_bv 12 1564).
Definition lo_77 := (Z_to_bv 12 1448).
Definition lo_88 := (Z_to_bv 12 1404).
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Lemma CODE : CodeAt.code_at rsegs 0x51e40 (QSsB.Mq8.is_allzero_code 0x00044797%Z 0x31c7b783%Z 0xfffc4817%Z 0x61c80813%Z 0xfffc4597%Z 0x5a858593%Z 0xfffc4517%Z 0x57c50513%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x51e40 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x51e40 /\ 0x51e40 + 376 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Definition land_pow2_testbit := ltac:(pose proof (@land_pow2_testbit) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition sllw1_word' := ltac:(pose proof (@sllw1_word') as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@QSsB.Mq8.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq_c1.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rallzerop_entry : Z := 0x51e40.
Lemma gw_eq_rallzerop_entry : @rallzerop_entry = ltac:(GwInst.gw_term (@QSsB.Mq8.rallzerop_entry 0x51e40) (@rallzerop_entry)). Proof. unfold rallzerop_entry, QSsB.Mq8.rallzerop_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rallzerop_entry : gw_eqs.

Definition raz_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (res : bool) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m0 (seg_rom rsegs)
/\ (bv_unsigned a0 <> 0 -> res = true).
Lemma gw_eq_raz_post : @raz_post = ltac:(GwInst.gw_term (@QSsB.Mq8.raz_post rsegs) (@raz_post)). Proof. unfold raz_post, QSsB.Mq8.raz_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_raz_post : gw_eqs.
End RC__1.
Lemma gw_eq_rallzerop_entry__2 : @rallzerop_entry = ltac:(GwInst.gw_term (@QSsB.Mq8.rallzerop_entry 0x51e40) (@rallzerop_entry)). Proof. unfold rallzerop_entry, QSsB.Mq8.rallzerop_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rallzerop_entry__2 : gw_eqs.
Lemma gw_eq_raz_post__2 : @raz_post = ltac:(GwInst.gw_term (@QSsB.Mq8.raz_post rsegs) (@raz_post)). Proof. unfold raz_post, QSsB.Mq8.raz_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_raz_post__2 : gw_eqs.

Ltac st1 := step; fix_lit_store; try nrm.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma raz_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m0 : mem)
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
let stride := if (maplen =? 0) || negb (last_idx =? 0) then 16 * size_class sc else maplen * 4096 - 16 in
let res := (48 <=? sc) || (stride <? 16 * size_class sc) in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes rsegs m0 (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes rsegs m0 (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes rsegs m0 (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes rsegs m0 (wa B) 8 = Some (le8 (wz G)) ->
rw_cells rsegs m0 G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes rsegs m0 (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes rsegs m0 (wa RCTX) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes rsegs m0 (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
(maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
evt rsegs (raz_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 res)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rallzerop_entry) fc None m0 (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rallzerop_entry__2, ?gw_eq_raz_post__2; first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq8.raz_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq8.raz_walk)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@QSsB.Mq8.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@QXT6.RHEAP) (Q6nq.gwt_def (@QSsB.Mq8.RHEAP) (@QXT6.RHEAP) Q6nq.gwt_nil)))).
#[using="Type"] Lemma raz_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.Mq8.raz_spec) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rallzerop_entry__2]; [@gw_eq_raz_post__2]] '([256]%Z : list Z) '(Q6nq.gwt_zc rallzerop_entry (Q6nq.gwt_zc UNIT gwt_X))).
Proof. rewrite ?gw_eq_rallzerop_entry__2, ?gw_eq_raz_post__2; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq8.raz_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq8.raz_spec)]. Qed.

Definition razH_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (s : PState) (c : cptr) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 a4 a5 a6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m0 (seg_rom rsegs)
/\ (bv_unsigned a0 <> 0 -> exists g idx, (s_slots (ps_m s)) !! c = Some (g, idx) /\ is_allzero_ctrl (get_meta_rec (ps_m s) g) = true).
Lemma gw_eq_razH_post : @razH_post = ltac:(GwInst.gw_term (@QSsB.Mq8.razH_post rsegs) (@razH_post)). Proof. unfold razH_post, QSsB.Mq8.razH_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_razH_post : gw_eqs.

#[using="Type"] Lemma raz_heap : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.Mq8.raz_heap) [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_rallzerop_entry__2]; [@gw_eq_razH_post]; [@gw_eq_raz_post__3; @gw_eq_raz_post__2; @gw_eq_raz_post]] '(@nil Z) '(Q6nq.gwt_zc rallzerop_entry gwt_X)).
Proof. rewrite ?gw_eq_rallzerop_entry__2, ?gw_eq_razH_post; ltac2:(GwEq.gw_rw [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq8.raz_heap) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq8.raz_heap)]. Qed.

End RC__2.
Lemma gw_eq_razH_post__2 : @razH_post = ltac:(GwInst.gw_term (@QSsB.Mq8.razH_post rsegs) (@razH_post)). Proof. unfold razH_post, QSsB.Mq8.razH_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_razH_post__2 : gw_eqs.
