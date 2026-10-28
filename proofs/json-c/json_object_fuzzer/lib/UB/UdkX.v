(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1ti.
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
Definition base := 0x53d40%Z.
Definition w_15 := 0xde5fc0ef%Z.
Definition w_59 := 0x00044797%Z.
Definition w_62 := 0x1547b783%Z.
Definition w_67 := 0xfffc2797%Z.
Definition w_70 := 0x6f478793%Z.
Definition w_145 := 0xfffc2317%Z.
Definition w_147 := 0x59c30313%Z.
Definition w_185 := 0x31c000ef%Z.
Definition w_238 := 0x3400b0ef%Z.
Definition hi_59 := (Z_to_bv 20 68).
Definition hi_67 := (Z_to_bv 20 1048514).
Definition hi_145 := (Z_to_bv 20 1048514).
Definition lo_62 := (Z_to_bv 12 340).
Definition lo_70 := (Z_to_bv 12 1780).
Definition lo_147 := (Z_to_bv 12 1436).
Definition joff_15 := (Z_to_bv 21 2084324).
Definition joff_185 := (Z_to_bv 21 796).
Definition joff_238 := (Z_to_bv 21 45888).
Definition e_24f80 := 0x5f438%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rerrno_loc_entry := UKNz.rerrno_loc_entry.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x53d40 (QQRC.Mqa.realloc_code 0xde5fc0ef%Z 0x00044797%Z 0x1547b783%Z 0xfffc2797%Z 0x6f478793%Z 0xfffc2317%Z 0x59c30313%Z 0x31c000ef%Z 0x3400b0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x53d40 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x53d40 /\ 0x53d40 + 1092 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry QQRC.Mqa.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition land_pow2_testbit := ltac:(pose proof (@land_pow2_testbit) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition sllw1_word' := ltac:(pose proof (@sllw1_word') as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition zx32_wz := @zx32_wz.
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@QQRC.Mqa.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rrealloc_entry : Z := 0x53d44.
Lemma gw_eq_rrealloc_entry : @rrealloc_entry = ltac:(GwInst.gw_term (@QQRC.Mqa.rrealloc_entry 0x53d40) (@rrealloc_entry)). Proof. unfold rrealloc_entry, QQRC.Mqa.rrealloc_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rrealloc_entry : gw_eqs.

Definition rrhead_post (ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (G B sc mword stride idx E rsv : Z) : machine_state -> Prop :=
fun ms' => exists t2 t3 t4,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp
(Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) t2
s0 (wz G)
a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 RSIZE_CLASSES) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - bv_unsigned a0))
(Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53f28) fc None m0 (seg_rom rsegs).
Lemma gw_eq_rrhead_post : @rrhead_post = ltac:(GwInst.gw_term (@QQRC.Mqa.rrhead_post rsegs 0x53d40 UKNz.RDEBRUIJN) (@rrhead_post)). Proof. unfold rrhead_post, QQRC.Mqa.rrhead_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rrhead_post : gw_eqs.

#[using="Type"] Lemma rr_head_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m0 : mem)
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret r32 : Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
let stride := if (maplen =? 0) || negb (last_idx =? 0) then 16 * size_class sc else maplen * 4096 - 16 in
let E := B + 16 + stride * idx + stride - 4 in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
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
16 <= stride -> P <= E -> E + 1 <= 2^64 ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m0 (E - 5) [b8 0]) ->
rsv <= E - P -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
evt rsegs (rrhead_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m0 G B sc mword stride idx E rsv)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53d9c) fc None m0 (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rrhead_post; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqa.rr_head_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqa.rr_head_walk)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QQRC.Mqa.rmrep) (@UQXM.rmrep) Q6nq.gwt_nil)).
#[using="Type"] Lemma rr_head_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mqa.rr_head_spec) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrhead_post]; [@gw_eq_rrealloc_entry__3; @gw_eq_rrealloc_entry__2; @gw_eq_rrealloc_entry]] '([160; 256; 343452]%Z : list Z) '(Q6nq.gwt_zc UNIT (Q6nq.gwt_zc IB gwt_X))).
Proof. rewrite ?gw_eq_rrhead_post; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqa.rr_head_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mqa.rr_head_spec)]. Qed.

End RC__1.
Lemma gw_eq_rrealloc_entry__2 : @rrealloc_entry = ltac:(GwInst.gw_term (@QQRC.Mqa.rrealloc_entry 0x53d40) (@rrealloc_entry)). Proof. unfold rrealloc_entry, QQRC.Mqa.rrealloc_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rrealloc_entry__2 : gw_eqs.
Lemma gw_eq_rrhead_post__2 : @rrhead_post = ltac:(GwInst.gw_term (@QQRC.Mqa.rrhead_post rsegs 0x53d40 UKNz.RDEBRUIJN) (@rrhead_post)). Proof. unfold rrhead_post, QQRC.Mqa.rrhead_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rrhead_post__2 : gw_eqs.
