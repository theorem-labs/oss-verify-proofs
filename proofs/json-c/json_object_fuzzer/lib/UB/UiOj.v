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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1.
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
Definition base := 0x53a78%Z.
Definition w_10 := 0xfffc3797%Z.
Definition w_12 := 0xaa078793%Z.
Definition hi_10 := (Z_to_bv 20 1048515).
Definition lo_12 := (Z_to_bv 12 2720).
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Lemma CODE : CodeAt.code_at rsegs 0x53a78 (QCa8.Mq3.enframe_code 0xfffc3797%Z 0xaa078793%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x53a78 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x53a78 /\ 0x53a78 + 336 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@QCa8.Mq3.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition renframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
let m1 := write_to_mem m (wa (P - 3)) [b8 k] in
let m2 := write_to_mem m1 (wa (P - 2)) (le2 (wz q)) in
let r := E - P - n in
let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].
Lemma gw_eq_renframe_tail_mem : @renframe_tail_mem = ltac:(GwInst.gw_term (@QCa8.Mq3.renframe_tail_mem) (@renframe_tail_mem)). Proof. unfold renframe_tail_mem, QCa8.Mq3.renframe_tail_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_renframe_tail_mem : gw_eqs.

Definition ren3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (P E n k q : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 pw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ m' = renframe_tail_mem m P E n k q
/\ mem_inv rsegs m'.
Lemma gw_eq_ren3_post : @ren3_post = ltac:(GwInst.gw_term (@QCa8.Mq3.ren3_post rsegs) (@ren3_post)). Proof. unfold ren3_post, QCa8.Mq3.ren3_post; rewrite ?gw_eq_renframe_tail_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ren3_post : gw_eqs.

#[using="Type"] Lemma lor_shl5 r k : 0 <= k < 32 -> 0 <= r -> Z.lor (r * 2 ^ 5) k = Z.land k 31 + Z.shiftl r 5.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.lor_shl5) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.lor_shl5)]. Qed.
End RC__1.
Lemma gw_eq_renframe_tail_mem__2 : @renframe_tail_mem = ltac:(GwInst.gw_term (@QCa8.Mq3.renframe_tail_mem) (@renframe_tail_mem)). Proof. unfold renframe_tail_mem, QCa8.Mq3.renframe_tail_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_renframe_tail_mem__2 : gw_eqs.
Lemma gw_eq_ren3_post__2 : @ren3_post = ltac:(GwInst.gw_term (@QCa8.Mq3.ren3_post rsegs) (@ren3_post)). Proof. unfold ren3_post, QCa8.Mq3.ren3_post; rewrite ?gw_eq_renframe_tail_mem__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ren3_post__2 : gw_eqs.

Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.

Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
let H := fresh "SO" in
pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma renframe_tail_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QCa8.Mq3.renframe_tail_walk) [[@gw_eq_ren3_post__2]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]] '([342868]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ren3_post__2; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.renframe_tail_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.renframe_tail_walk)]. Qed.

Definition renframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
if off =? 0 then m
else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off)))
(wa (P0 + 16 * off - 4)) [b8 0].
Lemma gw_eq_renframe_off_mem : @renframe_off_mem = ltac:(GwInst.gw_term (@QCa8.Mq3.renframe_off_mem) (@renframe_off_mem)). Proof. unfold renframe_off_mem, QCa8.Mq3.renframe_off_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_renframe_off_mem : gw_eqs.

#[using="Type"] Lemma renframe_off_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QCa8.Mq3.renframe_off_walk) [[@gw_eq_ren3_post__2]; [@gw_eq_renframe_off_mem]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]] '([342832]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ren3_post__2, ?gw_eq_renframe_off_mem; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.renframe_off_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.renframe_off_walk)]. Qed.

#[using="Type"] Lemma swrap32_add_2p64 d : -2^31 <= d < 2^31 -> bv_swrap 32 (18446744073709551616 + d) = d.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.swrap32_add_2p64) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.swrap32_add_2p64)]. Qed.

#[using="Type"] Lemma renframe_fold_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QCa8.Mq3.renframe_fold_walk) [[@gw_eq_ren3_post__2]; [@gw_eq_renframe_off_mem]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]] '([256; 342772]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_ren3_post__2, ?gw_eq_renframe_off_mem; first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.renframe_fold_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.renframe_fold_walk)]. Qed.

#[using="Type"] Lemma land_m4096 a : 0 <= a < 2^64 -> Z.land a 18446744073709547520 = a - a mod 4096.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.land_m4096) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.land_m4096)]. Qed.

#[using="Type"] Lemma renframe_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw nw prev next : word) F fc m
(B stride n k ctr avail freed last_idx freeable sc maplen vb3 v16 : Z),
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
let P0 := B + 16 + stride * k in
let slack := (stride - 4 - n) / 16 in
let off0 := (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
let off := fold_off off0 slack in
bv_unsigned nw = n ->
stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
((last_idx =? 0) && negb (maplen =? 0) = false -> sc < 48) ->
mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
wr_at rsegs m (P0 - 4) stride ->
ov_read_bytes rsegs m (wa (P0 - 3)) 1 = Some [b8 vb3] ->
ov_read_bytes rsegs m (wa (P0 - 2)) 2 = Some (le2 (wz v16)) ->
ov_read_bytes rsegs m (wa (P0 - 4)) 1 = Some [b8 0] ->
P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
(forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 0 <= k < 32 ->
0 <= ctr < 2^32 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
0 <= vb3 < 256 -> 0 <= v16 < 65536 ->
evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
(renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1
gw (wz k) nw (wz (sxv ctr)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53a78) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_ren3_post__2, ?gw_eq_renframe_off_mem; ltac2:(GwEq.gw_rw [[@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.renframe_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QCa8.Mq3.renframe_walk)]. Qed.

End RC__2.
Lemma gw_eq_renframe_off_mem__2 : @renframe_off_mem = ltac:(GwInst.gw_term (@QCa8.Mq3.renframe_off_mem) (@renframe_off_mem)). Proof. unfold renframe_off_mem, QCa8.Mq3.renframe_off_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_renframe_off_mem__2 : gw_eqs.
