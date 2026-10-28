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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x52e64%Z.
Definition w_11 := 0xcd1fd0ef%Z.
Definition w_26 := 0x00045597%Z.
Definition w_27 := 0xac58493%Z.
Definition w_37 := 0x314010ef%Z.
Definition w_40 := 0x00045517%Z.
Definition w_41 := 0xf8f54503%Z.
Definition w_43 := 0x00045517%Z.
Definition w_44 := 0x06850513%Z.
Definition w_45 := 0x6380d0ef%Z.
Definition w_57 := 0xfffc3617%Z.
Definition w_59 := 0x5d860993%Z.
Definition w_85 := 0xfffc3617%Z.
Definition w_90 := 0x58860593%Z.
Definition w_125 := 0x00045517%Z.
Definition w_126 := 0xe3b54503%Z.
Definition w_128 := 0x00045517%Z.
Definition w_129 := 0xf1450513%Z.
Definition w_130 := 0x4e40d0ef%Z.
Definition w_147 := 0x00045517%Z.
Definition w_148 := 0xec850513%Z.
Definition w_149 := 0x7200d0ef%Z.
Definition w_152 := 0x350010ef%Z.
Definition w_203 := 0x6480d0ef%Z.
Definition w_216 := 0x00045517%Z.
Definition w_217 := 0xdb450513%Z.
Definition w_218 := 0x60c0d0ef%Z.
Definition hi_26 := (Z_to_bv 20 69).
Definition hi_40 := (Z_to_bv 20 69).
Definition hi_43 := (Z_to_bv 20 69).
Definition hi_57 := (Z_to_bv 20 1048515).
Definition hi_85 := (Z_to_bv 20 1048515).
Definition hi_125 := (Z_to_bv 20 69).
Definition hi_128 := (Z_to_bv 20 69).
Definition hi_147 := (Z_to_bv 20 69).
Definition hi_216 := (Z_to_bv 20 69).
Definition lo_27 := (Z_to_bv 12 172).
Definition lo_41 := (Z_to_bv 12 3983).
Definition lo_44 := (Z_to_bv 12 104).
Definition lo_59 := (Z_to_bv 12 1496).
Definition lo_90 := (Z_to_bv 12 1416).
Definition lo_126 := (Z_to_bv 12 3643).
Definition lo_129 := (Z_to_bv 12 3860).
Definition lo_148 := (Z_to_bv 12 3784).
Definition lo_217 := (Z_to_bv 12 3508).
Definition joff_11 := (Z_to_bv 21 2088144).
Definition joff_37 := (Z_to_bv 21 4884).
Definition joff_45 := (Z_to_bv 21 54840).
Definition joff_130 := (Z_to_bv 21 54500).
Definition joff_149 := (Z_to_bv 21 55072).
Definition joff_152 := (Z_to_bv 21 4944).
Definition joff_203 := (Z_to_bv 21 54856).
Definition joff_218 := (Z_to_bv 21 54796).
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
Definition rlock_entry := UKNz.rlock_entry.
Definition runlock_entry := UKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x52e64 (Qy8Z.Mq8.malloc_code 0xcd1fd0ef%Z 0x00045597%Z 0xac58493%Z 0x314010ef%Z 0x00045517%Z 0xf8f54503%Z 0x00045517%Z 0x06850513%Z 0x6380d0ef%Z 0xfffc3617%Z 0x5d860993%Z 0xfffc3617%Z 0x58860593%Z 0x00045517%Z 0xe3b54503%Z 0x00045517%Z 0xf1450513%Z 0x4e40d0ef%Z 0x00045517%Z 0xec850513%Z 0x7200d0ef%Z 0x350010ef%Z 0x6480d0ef%Z 0x00045517%Z 0xdb450513%Z 0x60c0d0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x52e64 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x52e64 /\ 0x52e64 + 880 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Qy8Z.Mq8.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@Qy8Z.Mq8.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_RDEBRUIJN : ltac2:(GwEq.gw_fact_ty 'segs '(@Qy8Z.Mq8.gw_all) @ROM_RDEBRUIJN). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rDB32 : Z := 125613361.
Lemma gw_eq_rDB32 : @rDB32 = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rDB32) (@rDB32)). Proof. unfold rDB32, Qy8Z.Mq8.rDB32; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rDB32 : gw_eqs.
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.
Lemma gw_eq_rdbi : @rdbi = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rdbi) (@rdbi)). Proof. unfold rdbi, Qy8Z.Mq8.rdbi; rewrite ?gw_eq_rDB32; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rdbi : gw_eqs.

#[using="Type"] Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. rewrite ?gw_eq_rdbi; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rdbi_range) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rdbi_range)]. Qed.

Definition rdebruijn_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RDEBRUIJN 32 with Some bs => bs | None => [] end).
Lemma gw_eq_rdebruijn_bytes : @rdebruijn_bytes = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rdebruijn_bytes) (@rdebruijn_bytes)). Proof. unfold rdebruijn_bytes, Qy8Z.Mq8.rdebruijn_bytes; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rdebruijn_bytes : gw_eqs.

#[using="Type"] Lemma rdebruijn_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof. rewrite ?gw_eq_rdebruijn_bytes; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rdebruijn_ro) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rdebruijn_ro)]. Qed.

#[using="Type"] Lemma rdebruijn_read : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq8.rdebruijn_read) [[@gw_eq_rdbi]; [@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]] '(@nil Z) '(Q6nq.gwt_zc RDEBRUIJN (Q6nq.gwt_pat (@RDEBRUIJN) (@RDEBRUIJN) (Q6nq.gwt_hdr GwI.RDEBRUIJN (@RDEBRUIJN) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_rdbi; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rdebruijn_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rdebruijn_read)]. Qed.

#[using="Type"] Lemma mul_srliw27 : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq8.mul_srliw27) [[@gw_eq_rDB32]; [@gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]] '(@nil Z) '(Q6nq.gwt_zc rDB32 Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_rDB32, ?gw_eq_rdbi; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.mul_srliw27) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.mul_srliw27)]. Qed.

Definition rclz_v4 (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) x in
let v2 := Z.lor v1 (Z.shiftr x 1) in
let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
let w3 := Z.lor (Z.shiftr w2 4) w2 in
Z.lor (Z.shiftr w3 8) w3.
Lemma gw_eq_rclz_v4 : @rclz_v4 = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rclz_v4) (@rclz_v4)). Proof. unfold rclz_v4, Qy8Z.Mq8.rclz_v4; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rclz_v4 : gw_eqs.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Lemma gw_eq_rclz_pow : @rclz_pow = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rclz_pow) (@rclz_pow)). Proof. unfold rclz_pow, Qy8Z.Mq8.rclz_pow; rewrite ?gw_eq_rclz_v4; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rclz_pow : gw_eqs.
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
Lemma gw_eq_rclz_fn : @rclz_fn = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rclz_fn) (@rclz_fn)). Proof. unfold rclz_fn, Qy8Z.Mq8.rclz_fn; rewrite ?gw_eq_rclz_v4, ?gw_eq_rclz_pow; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rclz_fn : gw_eqs.
#[using="Type"] Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof. rewrite ?gw_eq_rclz_fn; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rclz_check_true) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rclz_check_true)]. Qed.
#[using="Type"] Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof. rewrite ?gw_eq_rclz_v4, ?gw_eq_rclz_pow; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rclz_pow_eq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rclz_pow_eq)]. Qed.

#[using="Type"] Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.lxor_4k_124) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.lxor_4k_124)]. Qed.

#[using="Type"] Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.lor_even_1) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.lor_even_1)]. Qed.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53070) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Lemma gw_eq_rentry_post : @rentry_post = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rentry_post rsegs 0x52e64 UKNz.RATP UKNz.RDEBRUIJN) (@rentry_post)). Proof. unfold rentry_post, Qy8Z.Mq8.rentry_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rentry_post : gw_eqs.

#[using="Type"] Lemma rmalloc_entry_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq8.rmalloc_entry_walk) [[@gw_eq_rentry_post]; [@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]] '([626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_zc rmalloc_entry (Q6nq.gwt_zc RNEED_LOCKS (Q6nq.gwt_zc MMAP_THRESHOLD (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) Q6nq.gwt_nil))))))))).
Proof. rewrite ?gw_eq_rentry_post; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rmalloc_entry_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rmalloc_entry_walk)]. Qed.

Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x52ed8) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Lemma gw_eq_rentry_big_post : @rentry_big_post = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rentry_big_post rsegs 0x52e64 UKNz.RATP) (@rentry_big_post)). Proof. unfold rentry_big_post, Qy8Z.Mq8.rentry_big_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rentry_big_post : gw_eqs.

#[using="Type"] Lemma rentry_big_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq8.rentry_big_walk) [[@gw_eq_rentry_big_post]; [@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]] '([(-4097); 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_zc rmalloc_entry (Q6nq.gwt_zc MMAP_THRESHOLD (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) Q6nq.gwt_nil)))))).
Proof. rewrite ?gw_eq_rentry_big_post; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rentry_big_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rentry_big_walk)]. Qed.

Definition rentry_ovf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 12)].
Lemma gw_eq_rentry_ovf_post : @rentry_ovf_post = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rentry_ovf_post rsegs) (@rentry_ovf_post)). Proof. unfold rentry_ovf_post, Qy8Z.Mq8.rentry_ovf_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rentry_ovf_post : gw_eqs.

#[using="Type"] Lemma rentry_ovf_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq8.rentry_ovf_walk) [[@gw_eq_rentry_ovf_post]; [@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]] '([(-4097); 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_zc rmalloc_entry (Q6nq.gwt_zc RATP (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) Q6nq.gwt_nil)))))))).
Proof. rewrite ?gw_eq_rentry_ovf_post; first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rentry_ovf_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq8.rentry_ovf_walk)]. Qed.

End RC__1.
Lemma gw_eq_rDB32__2 : @rDB32 = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rDB32) (@rDB32)). Proof. unfold rDB32, Qy8Z.Mq8.rDB32; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rDB32__2 : gw_eqs.
Lemma gw_eq_rdbi__2 : @rdbi = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rdbi) (@rdbi)). Proof. unfold rdbi, Qy8Z.Mq8.rdbi; rewrite ?gw_eq_rDB32__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rdbi__2 : gw_eqs.
Lemma gw_eq_rdebruijn_bytes__2 : @rdebruijn_bytes = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rdebruijn_bytes) (@rdebruijn_bytes)). Proof. unfold rdebruijn_bytes, Qy8Z.Mq8.rdebruijn_bytes; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rdebruijn_bytes__2 : gw_eqs.
Lemma gw_eq_rclz_v4__2 : @rclz_v4 = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rclz_v4) (@rclz_v4)). Proof. unfold rclz_v4, Qy8Z.Mq8.rclz_v4; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rclz_v4__2 : gw_eqs.
Lemma gw_eq_rclz_pow__2 : @rclz_pow = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rclz_pow) (@rclz_pow)). Proof. unfold rclz_pow, Qy8Z.Mq8.rclz_pow; rewrite ?gw_eq_rclz_v4__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rclz_pow__2 : gw_eqs.
Lemma gw_eq_rclz_fn__2 : @rclz_fn = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rclz_fn) (@rclz_fn)). Proof. unfold rclz_fn, Qy8Z.Mq8.rclz_fn; rewrite ?gw_eq_rclz_v4__2, ?gw_eq_rclz_pow__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rclz_fn__2 : gw_eqs.
Lemma gw_eq_rentry_post__2 : @rentry_post = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rentry_post rsegs 0x52e64 UKNz.RATP UKNz.RDEBRUIJN) (@rentry_post)). Proof. unfold rentry_post, Qy8Z.Mq8.rentry_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rentry_post__2 : gw_eqs.
Lemma gw_eq_rentry_big_post__2 : @rentry_big_post = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rentry_big_post rsegs 0x52e64 UKNz.RATP) (@rentry_big_post)). Proof. unfold rentry_big_post, Qy8Z.Mq8.rentry_big_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rentry_big_post__2 : gw_eqs.
Lemma gw_eq_rentry_ovf_post__2 : @rentry_ovf_post = ltac:(GwInst.gw_term (@Qy8Z.Mq8.rentry_ovf_post rsegs) (@rentry_ovf_post)). Proof. unfold rentry_ovf_post, Qy8Z.Mq8.rentry_ovf_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rentry_ovf_post__2 : gw_eqs.
