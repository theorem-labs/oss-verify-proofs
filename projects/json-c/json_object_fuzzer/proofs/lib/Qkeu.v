(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsB.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKZH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKZH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 : Z).
Variables (hi_59 hi_67 hi_145 : bv 20).
Variables (lo_62 lo_70 lo_147 : bv 12).
Variables (joff_15 joff_185 joff_238 : bv 21).
Variables (e_memcpy : Z).
Hypothesis CODE : code_at segs base (realloc_code w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1092.
Let rmremap_entry := (rvm_wait_entry + 312)%Z.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Jal 1 joff_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (Auipc 15 hi_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_62 : decode_any (Z_to_bv 32 w_62) = Some (Load SZ8 true 15 15 lo_62, 4%Z).
Hypothesis E_62 : is_ecall (Z_to_bv 32 w_62) = false.
Hypothesis D_67 : decode_any (Z_to_bv 32 w_67) = Some (Auipc 15 hi_67, 4%Z).
Hypothesis E_67 : is_ecall (Z_to_bv 32 w_67) = false.
Hypothesis D_70 : decode_any (Z_to_bv 32 w_70) = Some (OpImm ALU_ADD 15 15 lo_70, 4%Z).
Hypothesis E_70 : is_ecall (Z_to_bv 32 w_70) = false.
Hypothesis D_145 : decode_any (Z_to_bv 32 w_145) = Some (Auipc 6 hi_145, 4%Z).
Hypothesis E_145 : is_ecall (Z_to_bv 32 w_145) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (OpImm ALU_ADD 6 6 lo_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_185 : decode_any (Z_to_bv 32 w_185) = Some (Jal 1 joff_185, 4%Z).
Hypothesis E_185 : is_ecall (Z_to_bv 32 w_185) = false.
Hypothesis D_238 : decode_any (Z_to_bv 32 w_238) = Some (Jal 1 joff_238, 4%Z).
Hypothesis E_238 : is_ecall (Z_to_bv 32 w_238) = false.
Hypothesis ANCH_62 : gw_anch (Z.shiftl (bv_signed hi_59) 12 + (base + 236) + bv_signed lo_62)%Z (RATP + 131968).
Hypothesis ANCH_70 : gw_anch (Z.shiftl (bv_signed hi_67) 12 + (base + 268) + bv_signed lo_70)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_147 : gw_anch (Z.shiftl (bv_signed hi_145) 12 + (base + 580) + bv_signed lo_147)%Z RDEBRUIJN.
Hypothesis LINK_15 : gw_anch (base + 60 + bv_signed joff_15)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_185 : gw_anch (base + 740 + bv_signed joff_185)%Z (rmremap_entry + 0)%Z.
Hypothesis LINK_238 : gw_anch (base + 952 + bv_signed joff_238)%Z (e_memcpy + 0)%Z.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Hypothesis lor_shl5 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.lor_shl5) (base + -712)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_0))) in let T := gw_fold_pcs T base (-712)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).
Hypothesis land_m4096 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.land_m4096) (base + -712)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_0))) in let T := gw_fold_pcs T base (-712)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).

Definition rr_epilogue : ltac:(gw_ctx_fold_ty2 (@QSsB.Mq9.rr_epilogue) constr:(gw_tbl_0)) := ltac:(gw_ctx_fold_tm2 (@QSsB.Mq9.rr_epilogue)).

Ltac read_k := lazymatch goal with BKc : bytes_at segs ?mc (?P - 3) [b8 ?k] |- _ =>
pose proof (bytes_at_read segs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.

#[using="RDEBRUIJN rerrno_loc_entry rmremap_entry e_memcpy RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_15 E_15 D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 D_145 E_145 D_147 E_147 D_185 E_185 D_238 E_238 ANCH_62 ANCH_70 ANCH_147 LINK_15 LINK_185 LINK_238 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmremap_entry lor_shl5 land_m4096"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="rvm_wait_entry ref_mrd_overlay rmremap_entry"] Lemma write_to_mem_idem : forall m a bs,
bytes_at segs m a bs -> (a + Z.of_nat (length bs) <= 0x10000 \/ RIMG_HI <= a) ->
forall x, write_to_mem m (wa a) bs x = m x.
Proof. clear - rvm_wait_entry ref_mrd_overlay rmremap_entry segs RIMG_HI. gw_expose_win.
intros m a bs (H0 & H1 & HB) Himg x. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite write_to_mem_spec by lia.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
specialize (HB (Z.to_nat (bv_unsigned x - a)) ltac:(lia)).
replace (a + Z.of_nat (Z.to_nat (bv_unsigned x - a))) with (bv_unsigned x) in HB by lia.
unfold wa in HB. rewrite Z_to_bv_bv_unsigned in HB. rewrite ref_mrd_overlay in HB by lia. symmetry. gw_exact HB.
Qed.

Definition rr_mr_mem (m : word -> option byte) (G NB mw E P n k : Z) : word -> option byte :=
rr_ss_mem (write_to_mem (write_to_mem (write_to_mem m (wa (G + 16)) (le8 (wz NB))) (wa (G + 32)) (le8 (wz mw))) (wa E) [b8 0]) P E n k.

#[using="rvm_wait_entry rmremap_entry"] Lemma land_high_low' x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof. clear - rvm_wait_entry rmremap_entry x k y.
intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n k) as [LT|GE].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

#[using="rvm_wait_entry rmremap_entry"] Lemma lor_low12_pg (w nd : Z) : 0 <= w -> 0 <= nd -> nd mod 4096 = 0 -> Z.lor (Z.land w 4095) nd = nd + w mod 4096.
Proof. clear - rvm_wait_entry rmremap_entry w nd.
intros Hw Hn Hm. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
replace nd with ((nd / 4096) * 2^12) by (change (2^12) with 4096; Z.div_mod_to_equations; lia).
rewrite Z.lor_comm. rewrite lor_disjoint_add; [lia|]. apply land_high_low'; [Z.div_mod_to_equations; lia| lia| change (2^12) with 4096; Z.div_mod_to_equations; lia].
Qed.

Definition rr_tail2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (G NB mw' E P n k : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ m' = rr_mr_mem m G NB mw' E P n k
/\ mem_inv segs m'.
End RC__1.

Ltac sok_at W off len addr := lazymatch type of W with wr_at segs ?mc ?A0 _ =>
let H := fresh "SO" in
pose proof (wr_at_store_ok segs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
replace (A0 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Section RC__2.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved lor_shl5 rmremap_entry"] Lemma rr_tail2_walk : forall (x1 sp gp tp t0 t1 t2 s0 a0 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(v0 v1 v2 v3 v4 v5 v6 ra gw : word) F fc (m : word -> option byte) (G NB base_ nd n mw k lo : Z) (prev next memw : word) (avail freed : Z),
let P := NB + 16 + base_ in
bv_unsigned gw = G ->
let E := NB + nd - 4 in
mem_inv segs m ->
rw_cells segs m G [C8 prev; C8 next; C8 memw; C4 (wz avail); C4 (wz freed); C8 (wz mw)] ->
wr_at segs m (P - 3) (E - P + 4) ->
bytes_at segs m (P - 3) [b8 k] ->
rw_cells segs m (bv_unsigned sp + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra] ->
E + 1 <= lo -> G + 40 <= lo -> lo <= bv_unsigned sp + -64 ->
(G + 40 <= P - 3 \/ E + 1 <= G) -> 0 <= G ->
(G + 40 <= 0x10000 \/ RIMG_HI <= G) -> (E + 1 <= 0x10000 \/ RIMG_HI <= P - 3) ->
16 <= NB -> 0 <= base_ -> P + n <= E -> E - P - n < 2^31 -> 0 <= n -> 0 <= k < 256 ->
0 <= mw < 2^64 -> 0 <= nd -> nd mod 4096 = 0 -> nd + mw mod 4096 < 2^64 ->
evt segs (rr_tail2_post ra sp gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t5 t6 F fc m G NB (nd + mw mod 4096) E P n k)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 nd) gw
a0 (Z_to_bv 64 n) (Z_to_bv 64 NB) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 base_) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x2fc)) fc None m (seg_rom segs)).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved lor_shl5 rmremap_entry segs base RIMG_HI. gw_expose_win.
intros until freed. intros P HG E MI MM WRS BK FR ELO GLO LOS GD G0 GIMG SIMG NB16 B0 PNE EP N0 HK MW ND0 NDM MW'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
rewrite <- HG in *.
pose proof (rw_cells_wr_at segs m _ _ 40 MM ltac:(cbn; lia)) as WRG.
set (r := E - P - n).

step.

step. step. step. step. step. step. step. step.
rewrite ?(wz_unsigned mw), ?(unsigned_lit nd), ?(unsigned_lit NB), ?(unsigned_lit base_), ?(unsigned_lit n) by lia.
assert (LR : 0 <= Z.land mw 4095 < 4096).
{ change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; lia. }
rewrite (unsigned_lit (Z.land mw 4095)) by lia. rewrite lor_low12_pg by lia.
rewrite ?(unsigned_lit (NB + nd + -4)), ?(unsigned_lit (n + (NB + base_ + 16))) by lia.
rewrite (swrap32_small (NB + nd + -4 - (n + (NB + base_ + 16)))) by (subst r E P; lia).
replace (NB + nd + -4 - (n + (NB + base_ + 16))) with r by (subst r E P; lia).
replace (NB + base_ + 16) with P by (subst P; lia). replace (NB + nd + -4) with E by (subst E; lia).
replace (n + P) with (P + n) by lia.
clear MM.

sok_at WRG 16 8%nat (bv_unsigned gw + 16). step. change (le8 (Z_to_bv 64 NB)) with (le8 (wz NB)). sdk.
lazymatch goal with W : wr_at segs ?mc (bv_unsigned gw) _ |- _ => sok_at W 32 8%nat (bv_unsigned gw + 32) end.
step. change (le8 (Z_to_bv 64 (nd + mw mod 4096))) with (le8 (wz (nd + mw mod 4096))). sdk.
lazymatch goal with W : wr_at segs ?mc (P - 3) _ |- _ => sok_at W (E - P + 3) 1%nat (NB + nd + -4) end.
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

assert (J : forall (a1v a2v a4v : word) (m4 : word -> option byte) (r' : Z) (m3 : word -> option byte),
a1v = Z_to_bv 64 r' -> 0 <= r' <= 5 ->
mem_inv segs m4 -> bytes_at segs m4 (P - 3) [b8 k] -> wr_at segs m4 (P - 3) (E - P + 4) ->
rw_cells segs m4 (bv_unsigned sp + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra] ->
m3 = write_to_mem (write_to_mem (write_to_mem m (wa (bv_unsigned gw + 16)) (le8 (wz NB))) (wa (bv_unsigned gw + 32)) (le8 (wz (nd + mw mod 4096)))) (wa E) [b8 0] ->
(let '(m4', r'') := (if 5 <=? r then (write_to_mem (write_to_mem (if r =? 0 then m3 else write_to_mem m3 (wa (E - r)) [b8 0]) (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5)
else ((if r =? 0 then m3 else write_to_mem m3 (wa (E - r)) [b8 0]), r)) in m4 = m4' /\ r' = r'') ->
evt segs (rr_tail2_post ra sp gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t5 t6 F fc m (bv_unsigned gw) NB (nd + mw mod 4096) E P n k)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 nd) gw
(Z_to_bv 64 P) a1v a2v (Z_to_bv 64 (E + 4)) a4v (Z_to_bv 64 (nd + mw mod 4096)) (Z_to_bv 64 r) a7 s2 (Z_to_bv 64 base_) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x408)) fc None m4 (seg_rom segs))).
{ intros a1v a2v a4v m4 r' m3 -> R' MI4 BK4 WR4 FR4 EM3 HM.
assert (K31 : 0 <= Z.land k 31 < 32).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32. split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; lia. }
read_k. step. clear RK. rewrite ?zxb_b8 by lia.
step. rewrite ?(wz_unsigned k) by lia.
step. rewrite ?(unsigned_lit r'), (Z.shiftl_mul_pow2 r') by lia.
step. rewrite ?(unsigned_lit (r' * 2 ^ 5)), ?(unsigned_lit (Z.land k 31)) by lia.
rewrite (lor_shl5 r' (Z.land k 31)) by lia. rewrite !land31_idem.
assert (BV : 0 <= Z.land k 31 + Z.shiftl r' 5 < 256) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
sok_at WR4 0 1%nat (P + -3).
step. change (le1 (Z_to_bv 64 (Z.land k 31 + Z.shiftl r' 5))) with (le1 (wz (Z.land k 31 + Z.shiftl r' 5))).
rewrite (le1_wz (Z.land k 31 + Z.shiftl r' 5)) by gw_exact BV. sdk.
eapply rr_epilogue; [eassumption|].
unfold rr_tail2_post. do 13 eexists. split; [reflexivity|]. split; [|assumption].
unfold rr_mr_mem, rr_ss_mem. fold r. rewrite <- EM3.
destruct (5 <=? r); destruct HM as [-> ->]; subst; reflexivity. }
replace (Z_to_bv 64 (NB + nd)) with (Z_to_bv 64 (E + 4)) by (f_equal; subst E; lia).

step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
-
step. step. eapply (J _ _ _ _ 0); try eassumption; [reflexivity| lia| reflexivity|].
rewrite KR. change (5 <=? 0) with false. change (0 =? 0) with true. cbv beta iota zeta. split; [subst; reflexivity| reflexivity].
-
step. rewrite ?(unsigned_lit E), ?(unsigned_lit (P + n)) by lia. rewrite (swrap32_small (E - (P + n))) by lia.
replace (E - (P + n)) with r by lia.
step. rewrite ?(unsigned_lit r), (swrap32_small (0 - r)) by lia.
step. replace (E + (0 - r)) with (E - r + 0) by lia.
step.
lazymatch goal with W : wr_at segs ?mc (P - 3) _ |- _ => sok_at W (n + 3) 1%nat (E - r + 0) end.
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
+ step. eapply (J _ _ _ _ r); try eassumption; [reflexivity| lia| reflexivity|].
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia).
split; [|reflexivity]. subst. repeat (f_equal; try (unfold wa; f_equal; lia)).
+ lazymatch goal with W : wr_at segs ?mc (P - 3) _ |- _ => sok_at W (E - P - 2) 1%nat (E + 4 + -9) end.
step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
lazymatch goal with W : wr_at segs ?mc (P - 3) _ |- _ => sok_at W (E - P - 1) 4%nat (E + 4 + -8) end.
step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
step. eapply (J _ _ _ _ 5); try eassumption; [reflexivity| lia| reflexivity|].
replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia).
split; [|reflexivity]. subst. repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

#[using="w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 joff_185 CODE D_185 E_185 LINK_185 land_m4096 rmremap_entry"] Lemma rr_mr_head_walk : forall (ra sp gp tp t2 s0 gw a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : word -> option byte) (P S E B mword maplen n : Z) Q,
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 n -> 0 <= n < 2^63 - 4097 -> 0 <= S <= P -> P - S <= 4080 -> P < 2^64 -> 0 <= B < 2^64 - 1 ->
0 <= mword < 2^64 -> mword - mword mod 4096 = 4096 * maplen ->
let base_ := P - S in
let nd := rr_needed n base_ in
(4096 * maplen = nd -> forall a3v a5v,
evt segs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 S) t2 (Z_to_bv 64 nd) gw
a0 a1 (Z_to_bv 64 B) a3v (Z_to_bv 64 (4096 * maplen)) a5v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
s2 (Z_to_bv 64 base_) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x2fc)) fc None m (seg_rom segs))) ->
(4096 * maplen <> nd -> forall a5v,
evt segs Q (MS (mkR (Z_to_bv 64 (base + 0x2e8)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 S) t2 (Z_to_bv 64 nd) gw
(Z_to_bv 64 B) (Z_to_bv 64 (4096 * maplen)) (Z_to_bv 64 nd) (Z_to_bv 64 1) (Z_to_bv 64 (4096 * maplen)) a5v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
s2 (Z_to_bv 64 base_) (Z_to_bv 64 4095) a0 a1 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom segs))) ->
evt segs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 S) t2 s0 gw
a0 a1 (Z_to_bv 64 B) (Z_to_bv 64 63) (wz mword) (Z_to_bv 64 48) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x298)) fc None m (seg_rom segs)).
Proof. clear - w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 joff_185 CODE D_185 E_185 LINK_185 land_m4096 rmremap_entry segs base.
intros until Q. intros HA HN NR SP BS PR BR MW MWP base_ nd KEQ KNE. subst a0 a1.

step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }

step. step. rewrite ?(unsigned_lit P), ?(unsigned_lit S) by lia. fold base_.
step. step. step. rewrite ?(unsigned_lit n) by lia. step. rewrite ?(unsigned_lit (n + 4095)), ?(unsigned_lit base_) by lia.
step. step. rewrite (unsigned_lit (n + 4095 + (P + - S) + 20)) by lia. rewrite land_m4096 by lia.
assert (END : n + 4095 + (P + - S) + 20 - (n + 4095 + (P + - S) + 20) mod 4096 = nd).
{ unfold nd, rr_needed, base_, UNIT, IB. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. }
rewrite END.
assert (NDR : 0 <= nd < 2^63 + 16384) by (unfold nd, rr_needed, base_, UNIT, IB; rewrite round_up_pg_eq; Z.div_mod_to_equations; lia).

step. rewrite (wz_unsigned mword), land_m4096, MWP by lia.
replace (P + - S) with base_ by (unfold base_; lia).
step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
-
step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. revert K2. vm_compute. lia. }
apply KEQ. gw_exact K1.
-
step. step. step. step. step. step. step.
replace (Z_to_bv 64 (rmremap_entry + 0)) with (Z_to_bv 64 rmremap_entry) by (rewrite Z.add_0_r; reflexivity).
apply KNE. gw_exact K1.
Qed.

End RC__2.

End G.
