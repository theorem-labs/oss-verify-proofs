(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Export QQLG.Mq0.
Export QDXD.Mq0. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

End G.
End Mq0.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1 Q2qa QVbl Lib.CodeAt Lib.StepGen Lib.GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1 Q2qa.
Import QVbl.Mq0.
Import QQLG.Mq0.
Import QDXD.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition subtf3_code : list Z :=
[0xfff00713; 0x03f71713; 0x00e6c6b3; 0x0040006f]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base subtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 16.

Definition addtf3_post := Eval cbv beta delta [QDXD.Mq0.addtf3_post] in (QDXD.Mq0.addtf3_post segs).
Hypothesis addtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QDXD.Mq0.addtf3_spec segs (base + 16)%Z) 5%nat in let T := gw_subst T (QDXD.Mq0.addtf3_post segs) addtf3_post in let T := gw_fold_pcs T base (16)%Z [0; 28; 92; 128; 200; 220; 240]%Z in exact T).

Definition subtf3_entry := (base + 0x0)%Z.

#[using="CODE BASE4 BASER addtf3_spec"] Lemma land_shl64_low : forall h l, (0 <= l < 2^64)%Z -> Z.land (Z.shiftl h 64) l = 0%Z.
Proof.
intros h l Hl. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- replace (Z.testbit l i) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec l 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

#[using="CODE BASE4 BASER addtf3_spec"] Lemma f128_sub_split : forall aLo aHi bLo bHi,
(0 <= bLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
f128_sub (aLo + 2^64 * aHi) (bLo + 2^64 * bHi) = f128_add (aLo + 2^64 * aHi) (bLo + 2^64 * Z.lxor bHi 9223372036854775808).
Proof.
intros aLo aHi bLo bHi Hl Hh. unfold f128_sub. rewrite lo64_words, hi64_words by lia.
unfold mk128, SIGN64. rewrite Z.lor_comm, lor_disjoint_add.
- rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
- rewrite Z.land_comm. apply land_shl64_low. lia.
Qed.

#[using="CODE BASE4 BASER addtf3_spec"] Lemma subtf3_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk segs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
mem_inv segs m ->
frm0 fc ->
evt segs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
(f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until m. intros ST MI FRM. pose_word_ranges.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
rewrite f128_sub_split by lia.
do 4 zstep.
eapply evt_mono; [ eapply addtf3_spec; eassumption | ].
intros ms' PO. unfold addtf3_post in *.
rewrite (inr64_unsigned_lit (Z.lxor (bv_unsigned a3) 9223372036854775808)) in PO by zrange.
exact PO.
Qed.

End G.
End Mq1.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg Qy5Y Q4J3 QPjm Q8QT QCa8 QZAi QUZl Q7S0 Ql2m QGeV Q6q3 Lib.StepGenX Lib.StepGenX2 Lib.GwFold G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Qy5Y.Mq4 Q4J3.Mq3 QPjm.Mq4.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rcalloc_entry rrealloc_sym : Z).
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
Hypothesis AL_rcalloc_entry : gw_al rcalloc_entry 4.
Hypothesis AL_rrealloc_sym : gw_al rrealloc_sym 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ralloc_static : ltac:(gw_rebind_ty (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QDXD.Mq3.ralloc_static RATP) (@ralloc_static) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QDXD.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QDXD.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QDXD.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QDXD.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QDXD.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QDXD.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QDXD.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QDXD.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QDXD.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))).
Definition RHEAP : ltac:(gw_rebind_ty (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) gw_tbl_11).
Definition rclient_addr : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) gw_tbl_12).
Definition rheap_pres : ltac:(gw_rebind_ty (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) gw_tbl_13).
Definition rblock_range : ltac:(gw_rebind_ty (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QDXD.Mq3.rblock_range RIMG_HI RC__) (@rblock_range) gw_tbl_14).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QDXD.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_15)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_16)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rcalloc_entry rrealloc_sym RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rcalloc_entry AL_rrealloc_sym ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Definition RCALLOC_SYM : Z := rcalloc_entry.
Definition RREALLOC_SYM : Z := rrealloc_sym.
Definition RCALLOC_STACK : Z := RMALLOC_STACK + 32.
Definition RREALLOC_STACK : Z := RMALLOC_STACK + 64.

Definition rcalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (N lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres LB (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 12 /\ RHEAP s' LB m'
| Some p => exists A,
a0 = Z_to_bv 64 A /\ rblock_range A N
/\ RHEAP s' ((p, A, N) :: LB) m'
/\ rw_cells segs m' A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))]
end.

Definition rcalloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (cnt sz lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RCALLOC_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 ->
implM segs (raw_calloc cnt sz) s
(rcalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (cnt * sz) lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RCALLOC_SYM) fc None m (seg_rom segs)).

Definition real_off (cs : mstate) (slot : cptr) (A : Z) : Z := (A - conc cs slot) / UNIT.

Definition rrealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (old : list byte) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None =>
a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 12 /\ RHEAP s' LB m' /\ rheap_pres LB (bv_unsigned sp) m m'
| Some p' => exists A' junk,
a0 = Z_to_bv 64 A' /\ rblock_range A' n
/\ RHEAP s' ((p', A', n) :: lb_remove p LB) m'
/\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ rw_cells segs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n n0)) old ++ junk)]
end.

Definition rrealloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old junk0 : list byte),
RHEAP s LB m -> In (p, A, n0) LB ->
rw_cells segs m A [CB (Z.to_nat n0) (old ++ junk0)] ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
implM segs (raw_realloc (fst p) (real_off (ps_m s) (fst p) A) n) s
(rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n0 n lo B old m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom segs)).

End RC__1.

End G.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import Q2qa.Mq1 Q4J3.Mq1.
Export QPjm.Mq2.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
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
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_0)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_0).
Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_1).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_6))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_7))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_8))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_12)).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).

Definition rimplT_peek : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_peek) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_peek)).
#[global] Arguments rimplT_peek {R}%_type_scope o p c%_Z_scope h%_Z_scope k%_function_scope s Q%_function_scope ms _.
Definition rimplT_undef : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_undef) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_undef)).
#[global] Arguments rimplT_undef {R}%_type_scope o w k%_function_scope s Q%_function_scope ms.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rrepfoot_ctx : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_ctx) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_ctx)).
Definition rrepfoot_mlock : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_mlock) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_mlock)).
Definition rrepfoot_nl : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_nl) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_nl)).
Definition rrepfoot_pgsz : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_pgsz) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_pgsz)).
Definition rrepfoot_area : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_area) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_area)).
Definition rrepfoot_group : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_group) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_group)).
Definition rrepfoot_known : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_known) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_known)).
Definition rrepfoot_got : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_got) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_got)).
Definition rrepfoot_guard : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrepfoot_guard) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrepfoot_guard)).
Definition rbytes_at_agree : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rbytes_at_agree) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rbytes_at_agree)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

#[using="Type"] Lemma rimplT_guard {R} o t (c : bool) (k bail : QUZl.M R) s Q ms :
(c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof. clear - R o t c k bail s Q ms. intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

#[using="Type"] Lemma rimplT_rd8 {R} o st q (k : Z -> QUZl.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof. clear - R o st q k s Q ms.
intros H. unfold rd8. unfold rdv in H.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [gw_exact H|].
apply rimplT_peek. rewrite peek_ok_pans. gw_exact H.
Qed.

#[using="Type"] Lemma rimplT_rd16 {R} o st q (k : Z -> QUZl.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof. clear - R o st q k s Q ms. intros H. unfold rd16. apply rimplT_rd8, rimplT_rd8. gw_exact H. Qed.

#[using="Type"] Lemma rimplT_rd32 {R} o st q (k : Z -> QUZl.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
+ 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
rimplT o (rd32 st q k) s Q ms.
Proof. clear - R o st q k s Q ms. intros H. unfold rd32. apply rimplT_rd8, rimplT_rd8, rimplT_rd8, rimplT_rd8. gw_exact H. Qed.

#[using="Type"] Lemma rimplT_if {R} o (c : bool) (t1 t2 : QUZl.M R) s Q ms :
(c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof. clear - R o c t1 t2 s Q ms. intros H1 H2. destruct c; auto. Qed.

#[using="Type"] Lemma rrdv_range : forall o st m q r,
rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
0 <= rdv pans_mem o st q < 256.
Proof. clear - segs.
intros o st m q r MR Hr Hk Ho. unfold rdv.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- exact (proj2 (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E)).
- apply pans_mem_range.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved ref_seg_rom_none"] Lemma rrdv_cur : forall o st mX q r (x : byte),
rmrep st mX ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
(forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
bytes_at segs mX (r_base r + snd q) [x] ->
rdv pans_mem o st q = bv_unsigned x.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved ref_seg_rom_none segs.
intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read segs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite (AG h eq_refl).
destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma rwview_ext : forall m m' a, m' a = m a -> wview segs m' a = wview segs m a.
Proof. clear - segs. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

#[using="Type"] Lemma rwr_at_agree : forall m m' A n, wr_at segs m A n -> agree_on m m' A n -> wr_at segs m' A n.
Proof. clear - segs.
intros m m' A n (H0 & H1 & HW) AG. split; [gw_exact H0|]. split; [gw_exact H1|].
intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. gw_exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree' : forall m m' A cs,
rw_cells segs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof. clear - segs.
intros m m' A cs [[Hwf HB] HW] AG. split; [split; [gw_exact Hwf|]|].
- eapply rbytes_at_agree; [gw_exact HB|]. rewrite cells_bytes_length by assumption. gw_exact AG.
- eapply rwr_at_agree; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree' : forall m m' A ws,
u64arr segs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr segs m' A ws.
Proof. clear - segs.
intros m m' A ws [HB HW] AG. split.
- eapply rbytes_at_agree; [gw_exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. gw_exact AG.
- eapply rwr_at_agree; [gw_exact HW|]. gw_exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree' : forall m m' A bs,
u8arr segs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof. clear - segs. intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

#[using="Type"] Lemma rstk_agree : forall m m' lo hi, stk segs m lo hi -> agree_on m m' lo (hi - lo) -> stk segs m' lo hi.
Proof. clear - segs.
intros m m' lo hi (H0 & H1 & HS) AG. split; [gw_exact H0|]. split; [gw_exact H1|].
intros a Ha. rewrite (rwview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. gw_exact Ha.
Qed.

Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4"] Lemma rmrep_transport_agree : forall st m m',
rmrep st m ->
(forall a, 0 <= a < 2^64 -> rrepfoot st a -> m' (wa a) = m (wa a)) ->
(forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview segs m (wa a) <> None -> wview segs m' (wa a) <> None) ->
rmrep st m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m m' (WF & CX & GL & AR & GR & SH) AG WG.
pose proof WF as (Hres & WR & DJ & WA & WGr).
assert (TC : forall A cs, rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells segs m' A cs).
{ intros A cs H HP. pose proof (rw_cells_bound segs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; gw_exact Ha]. }
split; [gw_exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
pose proof (u64arr_bound segs m _ _ C2) as B2. pose proof (u64arr_bound segs m _ _ C3) as B3.
pose proof (u8arr_bound segs m _ _ C4) as B4. pose proof (u8arr_bound segs m _ _ C5) as B5.
rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [gw_exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. gw_expose_fam RATP. lia.
+ eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [gw_expose_fam RATP; lia|]. apply rrepfoot_ctx. gw_expose_fam RATP. lia.
+ eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [gw_expose_fam RATP; lia|]. apply rrepfoot_ctx. gw_expose_fam RATP. lia.
+ eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [gw_expose_fam RATP; lia|]. apply rrepfoot_ctx. gw_expose_fam RATP. lia.
+ eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [gw_expose_fam RATP; lia|]. apply rrepfoot_ctx. gw_expose_fam RATP. lia.
+ apply TC; [gw_exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. gw_expose_fam RATP. lia.
- destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
+ apply TC; [gw_exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. gw_expose_fam RATP. lia.
+ apply TC; [gw_exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. gw_expose_fam RATP. lia.
+ apply TC; [gw_exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. gw_expose_fam RATP. lia.
+ apply TC; [gw_exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. gw_expose_fam RGOT_SSP. lia.
+ apply TC; [gw_exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. gw_expose_fam RATP. lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
split; [|split].
+ apply TC; [gw_exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [gw_exact Ha|lia].
+ intros k Hk. apply TC; [apply A2; gw_exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [gw_exact Ha|lia].
+ apply TC; [gw_exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [gw_exact Ha|lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|gw_exact Hw8].
apply TC; [gw_exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [gw_exact Hb|lia].
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). unfold alloc_ceiling in RBC.
split.
+ destruct HWr as (W0 & W1 & HW). split; [gw_exact W0|]. split; [gw_exact W1|].
intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; gw_exact Hi].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
eapply rbytes_at_agree; [gw_exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. gw_exact Hc.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4"] Lemma rmrep_transport_agree' : forall st m m',
rmrep st m ->
(forall a, 0 <= a < 2^64 -> rrepfoot st a \/ rgrp_region_addr st a -> m' (wa a) = m (wa a)) ->
rmrep st m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4.
intros st m m' MR AG. eapply rmrep_transport_agree; [gw_exact MR| |].
- intros a Ha Hf. apply AG; auto.
- intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.

#[using="Type"] Lemma rpres_except_of_munch_nw : forall C W m m',
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. clear - segs.
intros C W m m' MU HW a Ha Hc.
assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [gw_exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.

#[using="Type"] Lemma rpres_except_agree : forall C m m' A n,
rpres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof. clear - segs. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; gw_exact Ha]. Qed.

#[using="Type"] Lemma ru64arr_pres : forall C m m' A ws,
rpres_except C m m' -> u64arr segs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr segs m' A ws.
Proof. clear - segs.
intros C m m' A ws HP H HC. pose proof (u64arr_bound segs m A ws H).
eapply ru64arr_agree'; [gw_exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

#[using="Type"] Lemma ru8arr_pres : forall C m m' A bs,
rpres_except C m m' -> u8arr segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr segs m' A bs.
Proof. clear - segs.
intros C m m' A bs HP H HC. pose proof (u8arr_bound segs m A bs H).
eapply ru8arr_agree'; [gw_exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

End RC__1.

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Q4J3.Mq4.
Export QPjm.Mq3.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
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
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).
Definition rmrep_del_group : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_del_group) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_del_group)).
Definition rmrep_del_slots : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_del_slots) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_del_slots)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac rctx_same := intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
Import Q6q3.
Section RC__1.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved"] Lemma rmrep_set_usage : forall st m sc v,
rmrep st m -> 0 <= sc < 48 ->
rmrep (set_usage sc v st) (write_to_mem m (wa ((RATP + 132432) + 8 * sc)) (le8 (wz v))).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RATP segs. gw_expose_fam RATP.
intros st m sc v MR Hsc. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le8 (wz v)) as L8.
pose proof (munch_write [((RATP + 132432) + 8 * sc, (RATP + 132432) + 8 * sc + 8)] m m ((RATP + 132432) + 8 * sc) (le8 (wz v)) (munch_refl _ m)
ltac:(gw_expose_fam RATP; lia) ltac:(rewrite L8; gw_expose_fam RATP; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
pose proof (wmono_write segs m m (wa ((RATP + 132432) + 8 * sc)) (le8 (wz v)) (wmono_refl segs m)) as WM.
eapply (rmrep_ctx_frameW st (set_usage sc v st) m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left. rewrite usages_set_usage by lia. replace ((RATP + 132432) + 8 * sc) with (((RATP + 132432)) + 8 * sc) by lia.
apply u64arr_write; [gw_exact X3| rewrite usages_length; lia].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [| rctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_usage upd_ctx c_seq c_brk set_usage_map]. reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved"] Lemma rmrep_set_seq : forall st m v,
rmrep st m -> 0 <= v < 256 ->
rmrep (upd_ctx (set_seq v) st) (write_to_mem m (wa ((RATP + 132880))) [b8 v]).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved RATP segs. gw_expose_fam RATP.
intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (munch_write [((RATP + 132880), (RATP + 132881))] m m ((RATP + 132880)) [b8 v] (munch_refl _ m)
ltac:(gw_expose_fam RATP; lia) ltac:(cbn; gw_expose_fam RATP; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write segs m m (wa ((RATP + 132880))) [b8 v] (wmono_refl segs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_seq v) st) m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left.
pose proof (rw_cells_write segs m ((RATP + 132880)) (ctx_tail_cells st) 0 (C1 (b8 (c_seq (ctx st)))) (C1 (b8 v)) X6 eq_refl eq_refl I) as W.
rewrite Z.add_0_r in W. cbn [cbytes cell_upd ctx_tail_cells Nat.eqb] in W.
unfold ctx_tail_cells, brk_word, ctx in *. cbn [s_ctx upd_ctx set_seq c_seq c_brk]. gw_exact W.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved"] Lemma rmrep_set_unmap_seq : forall st m i v,
rmrep st m -> 0 <= i < 32 ->
rmrep (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) (write_to_mem m (wa ((RATP + 132816) + i)) [b8 v]).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RATP segs. gw_expose_fam RATP.
intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (munch_write [((RATP + 132816) + i, (RATP + 132816) + i + 1)] m m ((RATP + 132816) + i) [b8 v] (munch_refl _ m)
ltac:(gw_expose_fam RATP; lia) ltac:(cbn; gw_expose_fam RATP; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write segs m m (wa ((RATP + 132816) + i)) [b8 v] (wmono_refl segs m)) as WM.
eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left. rewrite unmap_seqs_set by lia. replace ((RATP + 132816) + i) with (((RATP + 132816)) + i) by lia.
apply (u8arr_write segs m ((RATP + 132816)) (unmap_seqs st) i (b8 v)); [gw_exact X4| rewrite unmap_seqs_length; lia].
- right. split; [reflexivity| rctx_same].
- right. split; [| rctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_group_hdr_zero : forall st m p gh bs,
rmrep st m -> (s_groups st) !! p = Some gh ->
(forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
length bs = 8%nat ->
rmrep (del_group p st) (write_to_mem m (wa (conc st p)) bs).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m p gh bs MR Hp UNK L8.
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (rgroup_conc st p gh WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
pose proof (round_up_pg_ge (r_len r)) as RU. unfold alloc_ceiling in RBC.
eapply rmrep_transport_unowned.
- apply rmrep_del_group. gw_exact MR.
- apply (munch_write [(conc st p, conc st p + 8)] m m (conc st p) bs (munch_refl _ m)); [lia| rewrite L8; cbn; lia| rewrite L8; cbn [inside]; lia].
- apply wmono_write. apply wmono_refl.
- intros lo hi a [E|[]] Ha. inversion E; subst lo hi. clear E.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ destruct C as (ak & ar & Hak & Hin). cbn in Hak.
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
assert (NE : fst ak <> fst p) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
change (conc (del_group p st) ak) with (conc st ak) in Hin.
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Kr).
destruct (DJ (fst ak) ra (fst p) r Hra Hr NE); lia.
+ destruct C as (b & gh' & Hb & Hin). cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [NEb Hb].
change (conc (del_group p st) b) with (conc st b) in Hin.
destruct (rgroup_conc st b gh' WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & _).
destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
assert (snd b <> snd p) by (intros E2; apply NEb; destruct b, p; cbn in *; congruence).
Z.div_mod_to_equations. lia.
* pose proof (lr_lo_group rb Krb). pose proof (lr_lo_group r Kr). destruct (DJ (fst b) rb (fst p) r Hrb Hr NE); lia.
+ destruct C as (rid & r' & v & Hr' & Hk' & Hin & HC). cbn in Hr'. change (get_shadow (del_group p st) rid) with (get_shadow st rid) in HC.
destruct (N.eq_dec rid (fst p)) as [E|NE].
* subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
destruct (UNK (a - r_base r - snd p) ltac:(lia)) as [h Hh].
replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in HC. discriminate.
* pose proof (lr_lo_group r' Hk'). pose proof (lr_lo_group r Kr). destruct (DJ rid r' (fst p) r Hr' Hr NE); lia.
+ gw_expose_fam RGOT_SSP. lia.
+ gw_expose_fam RATP. lia.
Qed.

#[using="Type"] Lemma rmrep_grp_del_eq : forall st m g p, rmrep (del_group p st) m -> rmrep (grp_del st g p) m.
Proof. clear - segs. intros. unfold grp_del. apply rmrep_del_slots. gw_exact H. Qed.

End RC__1.

End G.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA Qnxq QJE4 QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Export QLsg.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq3.
Import QDXD.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
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
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_0).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_1)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_6))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_7))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_8))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11))).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rmrep_wr8 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_wr8) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_wr8)).
Definition rmrep_wr16 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_wr16) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_wr16)).
Definition rwr_at_bytes_exist : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rwr_at_bytes_exist) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rwr_at_bytes_exist)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_wr32 : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq1.rmrep_wr32) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq1.rmrep_wr32)).
Definition rpres_write : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq1.rpres_write) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq1.rpres_write)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ | clear - hs segs RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay].

Notation RMFACTS := (@MFACTS_g ref_reserved).
Import Q6q3.
Section RC__1.

#[using="gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved"] Lemma rreserved_disjoint2 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
(b + n <= 0x10000 \/ RDATA_LO <= b) /\ (b + n <= RDATA_LO \/ RIMG_HI <= b).
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RIMG_HI RDATA_LO ref_reserved. gw_expose_win. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.

#[using="Type"] Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof. clear - p q v w st.
intros Hf Hs.
assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
{ intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
rewrite (insert_insert_ne _ (snd p) (snd q)) by gw_exact Hs. reflexivity.
Qed.

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

#[using="Hr"] Lemma rconc_b : B = r_base r + snd b.
Proof. clear - Hr st2 m4 g b r k n off mr stride B P0 MR TK Hmem Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16. first [clear Q16 | gw_hide Q16 | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear N0 | gw_hide N0 | idtac]; first [clear OFF0 | gw_hide OFF0 | idtac]; first [clear NOGRP | gw_hide NOGRP | idtac]; first [clear S31 | gw_hide S31 | idtac]; first [clear S16 | gw_hide S16 | idtac]; first [clear SPAN | gw_hide SPAN | idtac]; first [clear K0 | gw_hide K0 | idtac]; first [clear B0 | gw_hide B0 | idtac]; first [clear Hk | gw_hide Hk | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear P0 | gw_hide P0 | idtac]; try gw_hide B; first [clear stride | gw_hide stride | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear off | gw_hide off | idtac]; first [clear n | gw_hide n | idtac]; first [clear k | gw_hide k | idtac]; try gw_hide r; try gw_hide b; first [clear g | gw_hide g | idtac]; first [clear m4 | gw_hide m4 | idtac]; try gw_hide st2. unfold B. apply (conc_region' st2 b r Hr). Qed.

#[using="b off B P0 K0 S16"] Lemma rsk_nonneg : 0 <= stride * k.
Proof. clear - b off B P0 K0 S16 st2 m4 g r k n mr stride MR TK Hmem Hr Hk B0 SPAN S31 NOGRP OFF0 N0 FIT Q16. first [clear Q16 | gw_hide Q16 | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear N0 | gw_hide N0 | idtac]; first [clear OFF0 | gw_hide OFF0 | idtac]; first [clear NOGRP | gw_hide NOGRP | idtac]; first [clear S31 | gw_hide S31 | idtac]; first [clear SPAN | gw_hide SPAN | idtac]; first [clear B0 | gw_hide B0 | idtac]; first [clear Hk | gw_hide Hk | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear stride | gw_hide stride | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear n | gw_hide n | idtac]; first [clear k | gw_hide k | idtac]; first [clear r | gw_hide r | idtac]; first [clear g | gw_hide g | idtac]; first [clear m4 | gw_hide m4 | idtac]; first [clear st2 | gw_hide st2 | idtac]. apply Z.mul_nonneg_nonneg; lia. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr8_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
0 <= v < 256 ->
rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved off B P0 Hr Hk B0 K0 SPAN S16 NOGRP st2 m4 g b r k n mr stride MR TK Hmem S31 OFF0 N0 FIT Q16. first [clear Q16 | gw_hide Q16 | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear N0 | gw_hide N0 | idtac]; first [clear OFF0 | gw_hide OFF0 | idtac]; first [clear S31 | gw_hide S31 | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear stride | gw_hide stride | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear n | gw_hide n | idtac]; first [clear k | gw_hide k | idtac]; try gw_hide r; try gw_hide b; first [clear g | gw_hide g | idtac]; first [clear m4 | gw_hide m4 | idtac]; first [clear st2 | gw_hide st2 | idtac].
intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
split; [|apply ticks_ok_wr8; gw_exact TKx].
apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; gw_exact Hr| gw_exact Hk| lia| |gw_exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr16_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
0 <= v < 65536 ->
rmrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved off B P0 Hr Hk B0 K0 SPAN S16 NOGRP st2 m4 g b r k n mr stride MR TK Hmem S31 OFF0 N0 FIT Q16. first [clear Q16 | gw_hide Q16 | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear N0 | gw_hide N0 | idtac]; first [clear OFF0 | gw_hide OFF0 | idtac]; first [clear S31 | gw_hide S31 | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear stride | gw_hide stride | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear n | gw_hide n | idtac]; first [clear k | gw_hide k | idtac]; try gw_hide r; try gw_hide b; first [clear g | gw_hide g | idtac]; first [clear m4 | gw_hide m4 | idtac]; first [clear st2 | gw_hide st2 | idtac].
intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
split; [|apply ticks_ok_wr16; gw_exact TKx].
apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; gw_exact Hr| gw_exact Hk| lia| lia| |gw_exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr32_rep : forall stx mx (o v : Z),
rmrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
0 <= v < 2^32 ->
rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved off B P0 Hr Hk B0 K0 SPAN S16 NOGRP st2 m4 g b r k n mr stride MR TK Hmem S31 OFF0 N0 FIT Q16. first [clear Q16 | gw_hide Q16 | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear N0 | gw_hide N0 | idtac]; first [clear OFF0 | gw_hide OFF0 | idtac]; first [clear S31 | gw_hide S31 | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear stride | gw_hide stride | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear n | gw_hide n | idtac]; first [clear k | gw_hide k | idtac]; try gw_hide r; try gw_hide b; first [clear g | gw_hide g | idtac]; first [clear m4 | gw_hide m4 | idtac]; first [clear st2 | gw_hide st2 | idtac].
intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; gw_exact Hr| gw_exact Hk| lia| lia| |gw_exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr16_wr8_comm p q v w st : fst p = fst q -> snd q <> snd p -> snd q <> snd p + 1 ->
wr8 q w (wr16 p v st) = wr16 p v (wr8 q w st).
Proof. clear - st2 g b k off mr stride B P0 K0 p q v w st m4 r n MR TK Hmem Hr Hk B0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16. first [clear Q16 | gw_hide Q16 | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear N0 | gw_hide N0 | idtac]; first [clear OFF0 | gw_hide OFF0 | idtac]; first [clear NOGRP | gw_hide NOGRP | idtac]; first [clear S31 | gw_hide S31 | idtac]; first [clear S16 | gw_hide S16 | idtac]; first [clear SPAN | gw_hide SPAN | idtac]; first [clear B0 | gw_hide B0 | idtac]; first [clear Hk | gw_hide Hk | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear n | gw_hide n | idtac]; first [clear r | gw_hide r | idtac]; first [clear m4 | gw_hide m4 | idtac].
intros Hf H0 H1. unfold wr16.
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof. clear - st2 g b k off mr stride B P0 K0 p q v w st m4 r n MR TK Hmem Hr Hk B0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16. first [clear Q16 | gw_hide Q16 | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear N0 | gw_hide N0 | idtac]; first [clear OFF0 | gw_hide OFF0 | idtac]; first [clear NOGRP | gw_hide NOGRP | idtac]; first [clear S31 | gw_hide S31 | idtac]; first [clear S16 | gw_hide S16 | idtac]; first [clear SPAN | gw_hide SPAN | idtac]; first [clear B0 | gw_hide B0 | idtac]; first [clear Hk | gw_hide Hk | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear n | gw_hide n | idtac]; first [clear r | gw_hide r | idtac]; first [clear m4 | gw_hide m4 | idtac].
intros Hf H1. unfold wr32.
rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved r MR TK Hmem Hr Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16"] Lemma renframe_mrep :
let res := enframe_at st2 g k n off in
rmrep (fst res) (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
/\ ticks_ok (fst res)
/\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved r MR TK Hmem Hr Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16 st2 m4 g b k n off mr stride B P0. try gw_hide P0; try gw_hide B; try gw_hide stride; try gw_hide mr; try gw_hide off; try gw_hide n; try gw_hide k; try gw_hide b; first [clear g | gw_hide g | idtac]; try gw_hide m4; try gw_hide st2.
pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
unfold aadd. cbn [fst snd].

set (stC := if negb (off =? 0) then _ else _).
assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
/\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
/\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
/\ (forall q, conc (fst stC) q = conc st2 q)).
{ subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
- subst off. rewrite Z.mul_0_r, Z.add_0_r.
split; [gw_exact MR|]. split; [gw_exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
-
rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
unfold UNIT in *.
replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
split; [gw_exact M3|]. split; [gw_exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. destruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
cbn [fst snd].
unfold renframe_tail_mem. cbv zeta.

set (po := snd b + (UNIT + stride * k) + UNIT * off).
assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
{ unfold po, P0, UNIT. f_equal; lia. }
rewrite Eq.
assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
{ unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
split; [apply Z.div_pos; lia| gw_exact Q16]. }

rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.

unfold set_size, aadd. cbn [fst snd id].
set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
rewrite Ersv.
assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
set (stF := if negb (rsv =? 0) then _ else _).
set (mF := if rsv =? 0 then _ else _).
assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
{ subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
- split; [gw_exact ME|]. split; [gw_exact TE|]. split; assumption.
- destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
split; [gw_exact MF|]. split; [gw_exact TF|]. split; assumption. }
clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
set (stG := if 5 <=? rsv then _ else _).
set (mG := if 5 <=? rsv then _ else _).
assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
/\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
{ subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
-
rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
split; [gw_exact M2|]. split; [gw_exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
- split; [gw_exact MF|]. split; [gw_exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
destruct PG as (MG & TG & -> & R2 & ERg & EGg).
assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
{ rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| gw_exact KV|].
split; [gw_exact MH|]. split; [gw_exact TH|].
split; [|split; [reflexivity| unfold po, UNIT; lia]].
rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.

#[using="Type"] Lemma rpres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
rpres_except C m0 m4 ->
0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
(forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
rpres_except C m0 (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof. clear - segs.
intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
{ unfold renframe_off_mem. destruct (off =? 0); [gw_exact HP|].
apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
apply rpres_write; [gw_exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
unfold renframe_tail_mem. cbv zeta.
set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
assert (HE : rpres_except C m0 mE).
{ subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
apply rpres_write; [gw_exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mE.
set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
set (mF := if rsv =? 0 then _ else _).
assert (HF : rpres_except C m0 mF).
{ subst mF. destruct (Z.eqb_spec rsv 0); [gw_exact HE|]. apply rpres_write; [gw_exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mF.
set (mG := if 5 <=? rsv then _ else _).
assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
- split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
apply rpres_write; [gw_exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
- split; [gw_exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply rpres_write; [gw_exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved ref_seg_rom_none"] Lemma rrdv_agree : forall st (m1 o : mem) (q : aptr) r (x : byte),
rmrep st m1 -> unk_agree st o m1 ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
~ grp_hdr_cov st (fst q) (snd q) ->
bytes_at segs m1 (r_base r + snd q) [x] ->
rdv pans_mem o st q = bv_unsigned x.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved ref_seg_rom_none segs.
intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read segs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved"] Lemma rmeta_chunk_facts : forall st m g,
rmrep st m -> meta_slot st g ->
let G := conc st g in
rw_cells segs m G (meta_cells st (get_meta_rec st g))
/\ 0 < G /\ G + 40 <= alloc_ceiling
/\ (G + 40 <= 0x10000 \/ RDATA_LO <= G) /\ (G + 40 <= RDATA_LO \/ RIMG_HI <= G)
/\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
/\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
/\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved segs RIMG_HI RDATA_LO. gw_expose_win.
intros st m g MR MS G.
split; [apply rmrep_meta_chunk; assumption|].
pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
destruct MS as (a & ara & kk & Ha & Hkk & Eg).
destruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
{ subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
- intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
- exists (fst a), rga. split; [gw_exact Hra|]. split; [gw_exact NK|]. lia.
Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved"] Lemma rregion_facts : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ RDATA_LO <= r_base r)
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= RDATA_LO \/ RIMG_HI <= r_base r).
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RIMG_HI RDATA_LO. gw_expose_win.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
split; [|split; [gw_exact RBAL| split; [gw_exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
clear RFr. Z.div_mod_to_equations. lia.
Qed.

Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

#[using="RATP RGOT_SSP RIMG_HI gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay MR UA Hr Hk B0 IDX SPAN S16 B16 SMOD HDR0"] Lemma rslot_facts :
exists x3 x2 x1 : byte,
wr_at segs m1 (P0 - 4) stride
/\ bytes_at segs m1 (P0 - 4) [b8 0; b8 (bv_unsigned x3); b8 (bv_unsigned x2); b8 (bv_unsigned x1)]
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -3) = bv_unsigned x3
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2) = bv_unsigned x2
/\ rdv pans_mem o st (fst b, snd b + (16 + stride * idx) + -2 + 1) = bv_unsigned x1
/\ B = r_base r + snd b /\ 4096 <= r_base r
/\ P0 + stride <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ RDATA_LO <= r_base r).
Proof. clear - RATP RGOT_SSP RIMG_HI gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay MR UA Hr Hk B0 IDX SPAN S16 B16 SMOD HDR0 segs RDATA_LO st m1 o g b r idx n mr stride B P0 Hmem NOGRP. gw_expose_win. first [clear NOGRP | gw_hide NOGRP | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; try gw_hide P0; try gw_hide B; try gw_hide stride; first [clear mr | gw_hide mr | idtac]; first [clear n | gw_hide n | idtac]; try gw_hide idx; try gw_hide r; try gw_hide b; first [clear g | gw_hide g | idtac]; try gw_hide o; try gw_hide m1; try gw_hide st.
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC |- *.
assert (CB : B = r_base r + snd b) by (apply conc_region'; gw_exact Hr).
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
assert (WRs : wr_at segs m1 (P0 - 4) stride) by (eapply wr_at_sub; [gw_exact HWr| unfold P0; lia| unfold P0; lia]).
destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
assert (WR3 : wr_at segs m1 (P0 - 3) 3) by (eapply wr_at_sub; [gw_exact WRs|lia|lia]).
destruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
exists x3, x2, x1.
assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
{ intros d Hd (b' & gh & Hb' & Hf & Hc).
pose proof MR as (WF' & _). destruct WF' as (_ & _ & _ & _ & WG). destruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
clear - Hd Hc AL' B16 SMOD IDX S16 RATP RGOT_SSP RIMG_HI gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay segs RDATA_LO.
destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
set (w := q * idx) in E. clearbody w. Z.div_mod_to_equations. lia. }
pose proof Ybs as (_ & _ & YB).
assert (Y3 : bytes_at segs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
{ split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). gw_exact YB0. }
assert (Y2 : bytes_at segs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
{ split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). gw_exact YB1. }
assert (Y1 : bytes_at segs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
{ split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). gw_exact YB2. }
split; [gw_exact WRs|].
split.
{ rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
- eapply bytes_at_at; [gw_exact Y3| lia]. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
- eapply bytes_at_at; [gw_exact Y2| lia]. }
split.
{ apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
- replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
- eapply bytes_at_at; [gw_exact Y1| lia]. }
split; [gw_exact CB|]. split; [gw_exact R4|]. split; [unfold P0; lia|]. split; [gw_exact RC| apply RI1; unfold P0 in *; lia].
Qed.
End SLOT.

Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
\/ fresh_addr st a.

#[using="Type"] Lemma rmalloc_fp_mono st sta stb lo sp a :
(forall rid r, (s_regions sta) !! rid = Some r ->
exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. clear - st sta stb lo sp a.
intros HR [H|[H|H]]; [| right; left | right; right; gw_exact H].
- destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; gw_exact H| left; right; left; gw_exact H| left; right; right; left; gw_exact H|].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
left. right. right. right. exists rid, r'. split; [gw_exact Hr'|]. split; [congruence|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
- destruct H as (rid & r & Hr & Hn & Ha). destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
exists rid, r'. split; [gw_exact Hr'|]. split; [gw_exact Hn|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

#[using="Type"] Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. clear - st LB sc n g k t st1 mr st2 MF ACT AV K0 LBK N0 NFIT. first [clear NFIT | gw_hide NFIT | idtac]; first [clear N0 | gw_hide N0 | idtac]; first [clear LBK | gw_hide LBK | idtac]; first [clear K0 | gw_hide K0 | idtac]; first [clear AV | gw_hide AV | idtac]; first [clear ACT | gw_hide ACT | idtac]; first [clear MF | gw_hide MF | idtac]; try gw_hide st2; first [clear mr | gw_hide mr | idtac]; first [clear st1 | gw_hide st1 | idtac]; first [clear t | gw_hide t | idtac]; first [clear k | gw_hide k | idtac]; first [clear g | gw_hide g | idtac]; first [clear n | gw_hide n | idtac]; first [clear sc | gw_hide sc | idtac]; first [clear LB | gw_hide LB | idtac]; first [clear st | gw_hide st | idtac]. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

#[using="ref_reserved LB sc MF ACT AV K0 LBK N0 NFIT"] Lemma rfast_slot_ok : exists b r,
slot_ok st2 g b r k n
/\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
free_slot_addr st a)
/\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof. clear - ref_reserved LB sc MF ACT AV K0 LBK N0 NFIT st n g k t st1 mr st2. first [clear st2 | gw_hide st2 | idtac]; try gw_hide mr; first [clear st1 | gw_hide st1 | idtac]; first [clear t | gw_hide t | idtac]; try gw_hide k; try gw_hide g; first [clear n | gw_hide n | idtac]; try gw_hide st.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
unfold UNIT, IB in *.
assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
pose proof (AVAI k K0 TBk) as KAI.
assert (K32 : k < 32) by lia.
assert (P2k : 0 < 2 ^ k <= m_avail mr).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
rewrite LBK in E'. rewrite E'. gw_exact LE'. }
assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
exists b, r. pose proof rget_meta_rec_st2 as E2.
split; [|split; [|split; [gw_exact K32| split; [reflexivity| gw_exact Hr]]]].
- pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
first [ gw_exact Hmem | gw_exact Hr | gw_exact Hk | gw_exact MSL | gw_exact K4 | gw_exact NOGRP | gw_exact N0 | gw_exact SMOD
| (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
cbn [default from_option id snd] in SC; unfold UNIT in SC; gw_exact SC)
| (intros off O0 OF;
assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
apply Z.div_lt_upper_bound; lia)
| lia ].
- intros a Ha. exists g, b, r, k. split; [gw_exact Hmem|]. split; [gw_exact Hr|]. split; [gw_exact Hk|]. split; [gw_exact K0|]. split; [left; gw_exact TBk|].
unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End FASTFACTS.

End RC__1.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q4J3.Mq3 QPjm.Mq4.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rfree_entry rmalloc_entry : Z).
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
Hypothesis AL_rfree_entry : gw_al rfree_entry 4.
Hypothesis AL_rmalloc_entry : gw_al rmalloc_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ralloc_static : ltac:(gw_rebind_ty (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QDXD.Mq3.ralloc_static RATP) (@ralloc_static) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QDXD.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QDXD.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QDXD.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QDXD.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QDXD.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QDXD.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QDXD.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QDXD.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QDXD.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))).
Definition RHEAP : ltac:(gw_rebind_ty (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) gw_tbl_11).
Definition rclient_addr : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) gw_tbl_12).
Definition rheap_pres : ltac:(gw_rebind_ty (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) gw_tbl_13).
Definition rblock_range : ltac:(gw_rebind_ty (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QDXD.Mq3.rblock_range RIMG_HI RC__) (@rblock_range) gw_tbl_14).
Definition raddr_exposed : ltac:(gw_rebind_ty (@QDXD.Mq3.raddr_exposed segs RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QDXD.Mq3.raddr_exposed segs RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QDXD.Mq3.raddr_exposed segs RC__) (@raddr_exposed) gw_tbl_15).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@QDXD.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_16)).
Definition rmalloc_post : ltac:(gw_rebind_ty (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@QDXD.Mq3.rmalloc_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rmalloc_post) gw_tbl_17).
Definition rfree_post : ltac:(gw_rebind_ty (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rfree_post) gw_tbl_18).

Definition rimpl_vis_unfold : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimpl_vis_unfold) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimpl_vis_unfold)).
#[global] Arguments rimpl_vis_unfold {R}%_type_scope n k%_function_scope Q%_function_scope ms.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rfree_entry rmalloc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rfree_entry AL_rmalloc_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

#[using="Type"] Lemma impl_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) Q ms,
impl segs (at_node segs) (QlEo_c1.Mq0.bind _ t f) Q ms ->
impl segs (at_node segs) t (fun r ms' => impl segs (at_node segs) (f r) Q ms') ms.
Proof. clear - segs.
induction t as [r|n k IH]; intros f Q ms H; cbn [QlEo_c1.Mq0.bind] in H.
- cbn. apply evt_done. gw_exact H.
- rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold. eapply evt_mono; [gw_exact H|]. intros ms1 [Hat Hk]. split; [gw_exact Hat|].
intros rsp. apply IH. apply Hk.
Qed.

#[using="Type"] Lemma impl_ebind_inv : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) Q ms,
impl segs (at_node segs) (ebind t f) (epost Q) ms ->
impl segs (at_node segs) t (fun r ms' => match r with
| Ok a => impl segs (at_node segs) (f a) (epost Q) ms'
| Unr => True end) ms.
Proof. clear - segs.
intros A B t f Q ms H. unfold ebind in H. apply impl_bind_inv in H.
eapply impl_mono; [gw_exact H|]. intros [|a] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implM_bind_inv : forall {St A B} (m : @M St A) (f : A -> @M St B) s Q ms,
implM segs (mbind m f) s Q ms ->
implM segs m s (fun a s' ms' => implM segs (f a) s' Q ms') ms.
Proof. clear - segs.
intros St A B m f s Q ms H. unfold implM, mbind in *. apply impl_ebind_inv in H.
eapply impl_mono; [gw_exact H|]. intros [|[a s']] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implM_ret_inv : forall {St A} (a : A) (s : St) Q ms,
implM segs (mret a) s Q ms -> evt segs (Q a s) ms.
Proof. clear - segs. intros St A a s Q ms H. gw_exact H. Qed.

#[using="Type"] Lemma implM_upd_inv : forall {St} (f : St -> St) s Q ms,
implM segs (mupd f) s Q ms -> evt segs (Q tt (f s)) ms.
Proof. clear - segs. intros St f s Q ms H. gw_exact H. Qed.

Definition rmalloc_impl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM segs (raw_malloc n) s
(rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom segs)).

Definition rfree_impl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM segs (raw_free p) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom segs)).

Definition cm_conv (st' : mstate) (n : Z) (p : option cptr) : option bptr :=
match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end.

#[using="Type"] Lemma rmalloc_membed : rmalloc_impl_stmt ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM segs (membed (cmalloc (ps_m s) n)) s
(fun x s' ms' => evt segs (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m
(cm_conv (fst x) n (snd x)) (set_m (fst x) s')) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom segs)).
Proof. clear - segs RATP rmalloc_entry. gw_expose_fam RATP.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N.
pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
HEAP AUXB SB ST CLO LO ERR MI TP HA N) as X.
unfold raw_malloc in X. apply implM_bind_inv in X.

unfold implM, mget in X. cbn [impl] in X. unfold epost in X. cbn [fst snd] in X.
eapply implM_evt; [gw_exact X|]. cbv beta. intros ms1 X1.
apply implM_bind_inv in X1. eapply implM_mono; [gw_exact X1|]. cbv beta.
intros [st' p] s' ms' X2. apply implM_bind_inv in X2. apply implM_upd_inv in X2.
eapply evt_cut; [gw_exact X2|]. cbv beta. intros ms2 X3. apply implM_ret_inv in X3. gw_exact X3.
Qed.

#[using="Type"] Lemma rfree_membed : rfree_impl_stmt ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM segs (membed (cfree (ps_m s) (Some (fst p)))) s
(fun st' s' ms' => evt segs (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m
tt (set_m st' s')) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom segs)).
Proof. clear - segs RATP rfree_entry. gw_expose_fam RATP.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv.
intros HP Hin AV HB ST LO SLO ERR MI TP A0.
pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0) as X.
unfold raw_free in X. apply implM_bind_inv in X.
unfold implM, mget in X. cbn [impl] in X. unfold epost in X. cbn [fst snd] in X.
eapply implM_evt; [gw_exact X|]. cbv beta. intros ms1 X1.
apply implM_bind_inv in X1. eapply implM_mono; [gw_exact X1|]. cbv beta.
intros st' s' ms' X2. apply implM_upd_inv in X2. gw_exact X2.
Qed.

End RC__1.

End G.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenSF GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base divtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2308.

Hypothesis mulhu_shl32 : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.mulhu_shl32 segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 524]%Z in exact T).

Definition divtf3_post := Eval cbv beta delta [QVbl.divtf3_post] in (QVbl.divtf3_post segs).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition saved12 (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (j : list byte) : list cell :=
[CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition DRr (signHi absHi absLo r3Hi r3Lo bHi bLo gt1 : Z) : Z :=
let abs1Lo := add64 absLo gt1 in
let b2Hi := shl64 bHi 1 in
let ca := b2z (Z.ltb abs1Lo absLo) in
let b3Hi0 := mulhu bLo 3 in
let abs1Hi := add64 absHi ca in
let b3Hi1 := add64 b3Hi0 bHi in
let b3Hi := add64 b3Hi1 b2Hi in
let ltInf1 := b2z (Z.ltb abs1Hi INF_HI) in
let gt3 := b2z (if Z.eqb r3Hi b3Hi then Z.ltb (add64 (shl64 bLo 1) bLo) r3Lo else Z.ltb b3Hi r3Hi) in
let inc2 := Z.land ltInf1 gt3 in
let b5Hi0 := mulhu bLo 5 in
let b5Hi1 := add64 b5Hi0 bHi in
let b4Hi := shl64 bHi 2 in
let abs2Lo := add64 abs1Lo inc2 in
let cb := b2z (Z.ltb abs2Lo abs1Lo) in
let abs2Hi := add64 abs1Hi cb in
let b5Hi := add64 b5Hi1 b4Hi in
let ltInf2 := b2z (Z.ltb abs2Hi INF_HI) in
let gt5 := b2z (if Z.eqb r3Hi b5Hi then Z.ltb (add64 (shl64 bLo 2) bLo) r3Lo else Z.ltb b5Hi r3Hi) in
let inc3 := Z.land ltInf2 gt5 in
let resLo := add64 abs2Lo inc3 in
let cc := b2z (Z.ltb resLo abs2Lo) in
let resHi := Z.lor (add64 abs2Hi cc) signHi in
mk128 resHi resLo.

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma div_round_DRr : forall s aH aL rH rL bH bL,
div_round s aH aL rH rL bH bL =
let odd := Z.land aL 1 in
let r3Lo := add64 odd rL in
let rc := b2z (Z.ltb r3Lo odd) in
let r3Hi := add64 rH rc in
DRr s aH aL r3Hi r3Lo bH bL (b2z (if Z.eqb r3Hi bH then Z.ltb bL r3Lo else Z.ltb bH r3Hi)).
Proof. reflexivity. Qed.

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma subw_amt : forall wE, -2^30 < wE < 2^30 ->
bv_swrap 32 (1 - Z.land wE 18446744073709551615) = 1 - wE.
Proof.
intros. rewrite land_W64. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 `div` 2) with (2^31).
Z.div_mod_to_equations. lia.
Qed.

Section IfLemmas.
Context {T : Type}.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_ltb_t x y (A B : T) : x < y -> (if x <? y then A else B) = A.   Proof. intro; now rewrite (proj2 (Z.ltb_lt x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_ltb_f x y (A B : T) : y <= x -> (if x <? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.ltb_ge x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_leb_t x y (A B : T) : x <= y -> (if x <=? y then A else B) = A. Proof. intro; now rewrite (proj2 (Z.leb_le x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_leb_f x y (A B : T) : y < x -> (if x <=? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.leb_gt x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_eqb_t x y (A B : T) : x = y -> (if x =? y then A else B) = A.   Proof. intro; now rewrite (proj2 (Z.eqb_eq x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_eqb_f x y (A B : T) : x <> y -> (if x =? y then A else B) = B.  Proof. intro; now rewrite (proj2 (Z.eqb_neq x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_nltb_t x y (A B : T) : x < y -> (if negb (x <? y) then A else B) = B.   Proof. intro; now rewrite (proj2 (Z.ltb_lt x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_nltb_f x y (A B : T) : y <= x -> (if negb (x <? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.ltb_ge x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_nleb_t x y (A B : T) : x <= y -> (if negb (x <=? y) then A else B) = B. Proof. intro; now rewrite (proj2 (Z.leb_le x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_nleb_f x y (A B : T) : y < x -> (if negb (x <=? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.leb_gt x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_neqb_t x y (A B : T) : x = y -> (if negb (x =? y) then A else B) = B.   Proof. intro; now rewrite (proj2 (Z.eqb_eq x y)). Qed.
#[using="CODE BASE4 BASER mulhu_shl32"] Lemma if_neqb_f x y (A B : T) : x <> y -> (if negb (x =? y) then A else B) = A.  Proof. intro; now rewrite (proj2 (Z.eqb_neq x y)). Qed.
End IfLemmas.
Ltac decide_ifs ::=
repeat (match goal with
| |- context [if (?x <? ?y) then ?A else ?B] => first [rewrite (if_ltb_t x y A B) by lia | rewrite (if_ltb_f x y A B) by lia]
| |- context [if negb (?x <? ?y) then ?A else ?B] => first [rewrite (if_nltb_t x y A B) by lia | rewrite (if_nltb_f x y A B) by lia]
| |- context [if (?x <=? ?y) then ?A else ?B] => first [rewrite (if_leb_t x y A B) by lia | rewrite (if_leb_f x y A B) by lia]
| |- context [if negb (?x <=? ?y) then ?A else ?B] => first [rewrite (if_nleb_t x y A B) by lia | rewrite (if_nleb_f x y A B) by lia]
| |- context [if (?x =? ?y) then ?A else ?B] => first [rewrite (if_eqb_t x y A B) by lia | rewrite (if_eqb_f x y A B) by lia]
| |- context [if negb (?x =? ?y) then ?A else ?B] => first [rewrite (if_neqb_t x y A B) by lia | rewrite (if_neqb_f x y A B) by lia]
end).

Section Walk.
Variables (sp sgw w6 : word).
Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation sgn := (bv_unsigned sgw).
Notation bLo := (bv_unsigned w6).

Ltac hyp :=
match goal with
| H : mem_inv _ ?m |- mem_inv _ ?m => exact H
| H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
| H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
| H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
| H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
| H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
| H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
| |- (_ <= _ <= _)%Z => lia
| |- (0 <= _ < _)%Z => first [zrange2 | lia]
end.
Ltac join L := eapply L; try hyp.

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma Lepi : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1
y1 y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
Z_to_bv 64 (lo64 R) = w0 -> Z_to_bv 64 (hi64 R) = w1 ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 w0 w1 y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x778)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO H0 H1. unfold saved12 in FR.
pose_word_ranges.
do 15 zstep.
release_frame FR ST (bv_unsigned sp).
rewrite <- H0, <- H1. finish.
Qed.

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma Lzero : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w1
y1 y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
R = mk128 (bv_unsigned w1) 0 ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 y10 w1 y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x540)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO HR.
pose_word_ranges.
do 2 zstep. join Lepi; subst R; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; [reflexivity | apply Z_to_bv_bv_unsigned].
Qed.

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma Linf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y1 y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
R = mk128 (Z.lor sgn INF_HI) 0 ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 y10 sgw y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x480)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO HR.
pose_word_ranges.
do 5 zstep. join Lepi; subst R; unfold INF_HI; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; reflexivity.
Qed.

Ltac flag_join n G body K :=
set (G := body);
let w := getreg n in
lazymatch w with Z_to_bv 64 ?e =>
replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
end;
let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma Lround : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (absHi absLo r3Hi r3Lo bHi : Z) (g1 : bool)
y1 y5 y6 y7 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= absHi < 2^64)%Z -> (0 <= absLo < 2^64)%Z -> (0 <= r3Hi < 2^64)%Z -> (0 <= r3Lo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
R = DRr sgn absHi absLo r3Hi r3Lo bHi bLo (Z.b2z g1) ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 absLo) sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 r3Lo) (Z_to_bv 64 absHi) (Z_to_bv 64 r3Hi) (Z_to_bv 64 (Z.b2z g1))
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x6e0)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 HR.
pose_word_ranges.
name_as gt1 (Z.b2z g1).
zstep. model_reg 17 abs1Lo (Z.land (absLo + gt1) 18446744073709551615).
do 3 zstep. model_reg 7 b2Hi (Z.land (Z.shiftl bHi 1) 18446744073709551615).
zstep. model_reg 28 ca (Z.b2z (abs1Lo <? absLo)).
zstep. zstep. model_reg 5 b3Hi0 (Z.shiftr (bLo * 3) 64). mulhu_rng b3Hi0.
zstep. model_reg 15 abs1Hi (Z.land (absHi + ca) 18446744073709551615).
zstep. model_reg 5 b3Hi1 (Z.land (b3Hi0 + bHi) 18446744073709551615).
zstep. model_reg 6 b3Hi (Z.land (b3Hi1 + b2Hi) 18446744073709551615).
zstep. model_reg 5 ltInf1 (Z.b2z (abs1Hi <? 9223090561878065152)).
zstep. if_cases K2; zify_cond K2; [ do 3 zstep | do 2 zstep ];
flag_join 6%Z gt3 (Z.b2z (if r3Hi =? b3Hi then Z.land (Z.land (Z.shiftl bLo 1) 18446744073709551615 + bLo) 18446744073709551615 <? r3Lo else b3Hi <? r3Hi)) K2;
( zstep; model_reg 5 inc2 (Z.land ltInf1 gt3);
do 2 zstep; model_reg 6 b5Hi0 (Z.shiftr (bLo * 5) 64); mulhu_rng b5Hi0;
zstep; model_reg 6 b5Hi1 (Z.land (b5Hi0 + bHi) 18446744073709551615);
zstep; model_reg 7 b4Hi (Z.land (Z.shiftl bHi 2) 18446744073709551615);
zstep; model_reg 13 abs2Lo (Z.land (abs1Lo + inc2) 18446744073709551615);
zstep; model_reg 17 cb (Z.b2z (abs2Lo <? abs1Lo));
zstep; model_reg 15 abs2Hi (Z.land (abs1Hi + cb) 18446744073709551615);
zstep; model_reg 17 b5Hi (Z.land (b5Hi1 + b4Hi) 18446744073709551615);
zstep; model_reg 10 ltInf2 (Z.b2z (abs2Hi <? 9223090561878065152));
zstep; if_cases K3; zify_cond K3; [ do 3 zstep | do 2 zstep ] );
flag_join 12%Z gt5 (Z.b2z (if r3Hi =? b5Hi then Z.land (Z.land (Z.shiftl bLo 2) 18446744073709551615 + bLo) 18446744073709551615 <? r3Lo else b5Hi <? r3Hi)) K3;
( zstep; model_reg 10 inc3 (Z.land ltInf2 gt5);
zstep; model_reg 10 resLo (Z.land (abs2Lo + inc3) 18446744073709551615);
zstep; model_reg 12 cc (Z.b2z (resLo <? abs2Lo));
do 2 zstep; model_reg 11 resHi (Z.lor (Z.land (abs2Hi + cc) 18446744073709551615) sgn);
assert (E : R = mk128 resHi resLo);
[ rewrite HR; change (Z.b2z g1) with gt1; cbv beta delta [DRr]; sf_vocab;
fold_model_lets2;
repeat (first [ progress fold_model_lets2
| match goal with |- (let x := ?b in _) = _ =>
first [ change b with gt3 | change b with gt5 ] end ]);
reflexivity
| join Lepi; rewrite E; rewrite ?lo64_mk128, ?hi64_mk128 by zrange; reflexivity ] ).
Time Qed.

End Walk.

End G.
