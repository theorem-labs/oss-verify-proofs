(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x526a4%Z.
Definition w_36 := 0x00046797%Z.
Definition w_39 := 0x84c7b783%Z.
Definition w_47 := 0xfffc4797%Z.
Definition w_48 := 0xde078793%Z.
Definition hi_36 := (Z_to_bv 20 70).
Definition hi_47 := (Z_to_bv 20 1048516).
Definition lo_39 := (Z_to_bv 12 2124).
Definition lo_48 := (Z_to_bv 12 3552).
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition runlock_entry := UKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x526a4 (QCa8.Mq4.get_meta_code 0x00046797%Z 0x84c7b783%Z 0xfffc4797%Z 0xde078793%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x526a4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x526a4 /\ 0x526a4 + 272 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_runlock_entry : CodeAt.code_at rsegs runlock_entry QCa8.Mq4.unlock_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@QCa8.Mq4.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma land_pow2_testbit a i : 0 <= a -> 0 <= i -> Z.land a (2 ^ i) = 0 <-> Z.testbit a i = false.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.land_pow2_testbit) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.land_pow2_testbit)]. Qed.

#[using="Type"] Lemma sllw1_word' i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.sllw1_word') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.sllw1_word')]. Qed.

Definition rget_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw : word) (off16 : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2 a3 a4 a5,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs).
Lemma gw_eq_rget_meta_post : @rget_meta_post = ltac:(GwInst.gw_term (@QCa8.Mq4.rget_meta_post rsegs) (@rget_meta_post)). Proof. unfold rget_meta_post, QCa8.Mq4.rget_meta_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rget_meta_post : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QCa8.Mq4.rmrep) (@UQXM.rmrep) Q6nq.gwt_nil)).
#[using="Type"] Lemma rget_meta_tail : ltac2:(Q6nq.ty2 'GwI.segs '(@QCa8.Mq4.rget_meta_tail) [[@gw_eq_rget_meta_post]] '([256; 65536; 337816]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) gwt_X)).
Proof. rewrite ?gw_eq_rget_meta_post; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.rget_meta_tail) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.rget_meta_tail)]. Qed.

#[using="Type"] Lemma rget_meta_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes rsegs m (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt rsegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz G) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x526a4) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rget_meta_post; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.rget_meta_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.rget_meta_walk)]. Qed.

#[using="Type"] Lemma rget_meta_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@QCa8.Mq4.rget_meta_spec) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rget_meta_post]] '([256]%Z : list Z) '(Q6nq.gwt_zc rget_meta_entry (Q6nq.gwt_zc UNIT gwt_X))).
Proof. rewrite ?gw_eq_rget_meta_post; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.rget_meta_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.rget_meta_spec)]. Qed.

Definition runlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs).
Lemma gw_eq_runlock_post : @runlock_post = ltac:(GwInst.gw_term (@QCa8.Mq4.runlock_post rsegs) (@runlock_post)). Proof. unfold runlock_post, QCa8.Mq4.runlock_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_runlock_post : gw_eqs.

#[using="Type"] Lemma runlock_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@QCa8.Mq4.runlock_spec) [[@gw_eq_runlock_post]; [@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]] '(@nil Z) '(Q6nq.gwt_zc runlock_entry (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_pat (@runlock_entry) (@runlock_entry) (Q6nq.gwt_hdr GwI.runlock_entry (@runlock_entry) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))).
Proof. rewrite ?gw_eq_runlock_post; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.runlock_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq4.runlock_spec)]. Qed.

End RC__1.
Lemma gw_eq_rget_meta_post__2 : @rget_meta_post = ltac:(GwInst.gw_term (@QCa8.Mq4.rget_meta_post rsegs) (@rget_meta_post)). Proof. unfold rget_meta_post, QCa8.Mq4.rget_meta_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rget_meta_post__2 : gw_eqs.
Lemma gw_eq_runlock_post__2 : @runlock_post = ltac:(GwInst.gw_term (@QCa8.Mq4.runlock_post rsegs) (@runlock_post)). Proof. unfold runlock_post, QCa8.Mq4.runlock_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_runlock_post__2 : gw_eqs.
