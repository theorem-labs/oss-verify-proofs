(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QTp6 Q2qa Qy5Y QDUx Q4J3 QytA Qnxq QJE4 QWTl QPjm QZAi QUZl Q7S0 Ql2m QGeV QLsg QkQT QlkP QM7w QXxF QCwx QFqQ Q98Z QkLq QdZ1 Qv4L QQbX QnkH QmBS Qlfl Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq1.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq8 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb QmBS.Mq1 Qlfl.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AG1.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

#[using="SC"] Lemma rag_entry_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (rt1_regs sc (Z_to_bv 64 0xceb98) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sc * 2))
(wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceb80) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI. unfold rt1_regs, ralloc_meta_entry, RSIZE_CLASSES, RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (size_class_range sc SC) as SZR.
step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
pose proof (rsize_classes_read m sc MI SC) as SCRD. unfold RSIZE_CLASSES in SCRD.
replace (159560 + 2 * sc) with (159560 + sc * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.
step. apply evt_done. reflexivity.
Qed.
End AG1.

#[using="Type"] Lemma rag_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
0 <= gm < 2^64 -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if gm =? 0 then 0xcf200 else 0xceba4)) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceb98) fc None m (seg_rom rsegs)).
Proof.
intros until gm. intros GR MI.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
- subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
- replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.

Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

#[using="SZC CR SMALL"] Lemma rstc_q_eq : j = stc_q (szc * cnt).
Proof.
unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.

#[using="SZC CR SMALL"] Lemma rnest_call_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv rsegs m ->
evt rsegs (fun ms' => exists a2' a3' a4',
ms' = MS (mkR (Z_to_bv 64 0xced80) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2' a3' a4' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz (szc * 16 * cnt)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcecb0) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI.
assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
pose proof rstc_q_eq as STC. fold q in STC.
unfold RSIZE_CLASSES, ralloc_slot_entry in *.

assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
evt rsegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0xced80) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 159560) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 846240) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 159560) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xced74) fc None m (seg_rom rsegs))).
{ intros a0' a2' a3' jv ->.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
step. rewrite Qfw3_c1.Mq2.sextw_small by lia. step. step.
apply evt_done. do 3 eexists. reflexivity. }

step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).

step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
-
apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
-
assert (Q10 : 10 <= q) by (unfold n' in K; nia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].

step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.

step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.

step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.

step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by reflexivity.

step. step. step.
rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.

step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
assert (K13 : 3 <= k <= 12).
{ unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.

step. step. step.
step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (159560 + (i + 1) * 2) with (159560 + 2 * (i + 1)) by lia.
pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
evt rsegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0xced80) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 159560) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 846240) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 159528) (Z_to_bv 64 q) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 159560) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xced58) fc None m (seg_rom rsegs))).
{ intros i1 c Hi1 Hc.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (159560 + i1 * 2) with (159560 + 2 * i1) by lia.
pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End STC.

#[using="Type"] Lemma rnest_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
-1 <= idx < 32 -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if idx =? -1 then 0xcedf8 else 0xced84)) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xced80) fc None m (seg_rom rsegs)).
Proof.
intros until idx. intros IR MI.
step. if_cases K; zify_cond K.
- replace (idx =? -1) with true.
2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [exact E|]. exfalso.
change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia. lia. }
apply evt_done. reflexivity.
- replace (idx =? -1) with false.
2:{ symmetry. apply Z.eqb_neq. intros ->. rewrite Z.land_m1_l in K. cbn in K. lia. }
apply evt_done. reflexivity.
Qed.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6y7 QTyG Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w Q6y7.Mq0 QTyG.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qn9M.Mq0 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb QdZ1.Mq2 QmBS.Mq1 Qlfl.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

#[using="o r N MR UA J HA MSL MW SCg STR SO TK"] Lemma rnenf_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
0 <= c_mmap_counter (ctx st) < 2^32 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
ms' = MS (mkR (Z_to_bv 64 0xcedb0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (RSIZE_CLASSES + j * 2)) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 0xcedb0) fc None m' (seg_rom rsegs)
/\ munch [(P - 3, P)]%Z m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
/\ rmrep (enf0_st st g b idx) m' /\ ticks_ok (enf0_st st g b idx))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 j) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xced84) fc None m1 (seg_rom rsegs)).
Proof.
intros until fc. intros CTR MI.
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
pose proof (size_class_range j J) as SZR.
assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
destruct (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)
as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND.
pose proof (rmeta_chunk_facts st m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
unfold alloc_ceiling in RC, GC.
set (G := conc st g) in *.
pose proof (GDJ (fst b) r Hr Hk) as GR.
change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
pose proof (bytes_at_read rsegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
pose proof (bytes_at_read rsegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
pose proof (bytes_at_read rsegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
rewrite Z.add_0_r in RD4.
replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
pose proof MW as (LI0 & FB0 & SCR0 & ML0).
pose proof MR as (WF' & CX & GL & _). destruct CX as (CH & _). unfold ctx_head_cells in CH.
unfold RSIZE_CLASSES, RMLOCK, RCTX in *.

step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step.

pose proof (rsize_classes_read m1 j MI J) as SCRD. unfold RSIZE_CLASSES in SCRD.
replace (159560 + 2 * j) with (159560 + j * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.

pose proof (rmrep_active_read st m1 j (wa (6566376 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
replace (wa (6566376 + 80 + 8 * j)) with (Z_to_bv 64 (6566368 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.

step. rewrite sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
step.

step.
eapply evt_mono.
{ eapply (renframe_walk (Z_to_bv 64 0xcedb0) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
(pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
| |- mem_inv _ _ => exact MI
| |- wr_at _ _ _ _ => exact WRs
| |- ov_read_bytes _ _ _ 2 = _ => exact RD2
| |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
| |- ov_read_bytes _ _ _ _ = _ => exact RD3
| |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
| |- _ => idtac end.
all: try (rewrite (unsigned_lit G) by lia).
all: try lia.
- subst stride. unfold get_stride, UNIT. reflexivity.
- intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
- exact (so_maplen _ _ _ _ _ _ SO). }

intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
assert (OFF0 : 0 <= off0 < 256).
{ subst off0. destruct (bv_unsigned x3 =? 0).
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
replace (fold_off off0 0) with 0 in EM |- * by lia.
rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
replace (ret_pc (Z_to_bv 64 0xcedb0)) with (Z_to_bv 64 0xcedb0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

assert (S31n : stride - 4 - N < 2^31) by lia.
assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
destruct (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)
as (MRr & TKr & CONCr & FSTr & SNDr). clear T1 T3 T0 TN T4.
rewrite Z.mul_0_r, Z.add_0_r in MRr.
change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
fold P in MRr, EM. rewrite <- EM in MRr.
destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.

assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
{ rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
assert (MU : munch [(P - 3, P)]%Z m1 m').
{ rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
assert (WM : wmono rsegs m1 m').
{ rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
do 14 eexists. exists m'.
split; [unfold P, G; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
#[using="st g b idx j mr stride B P N"] Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.

#[using="m1 r j N MR J SO TK"] Lemma renfD_walk :
forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mt : aptr) (cnt : Z) mC,
meta_slot st mt -> mw_ok (get_meta_rec st mt) -> 1 <= cnt <= 32 ->
rmrep (enf0_st st g b idx) mC -> ticks_ok (enf0_st st g b idx) -> mem_inv rsegs mC ->
evt rsegs (fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (P + 12)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcedd8) fc None m' (seg_rom rsegs)
/\ munch [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC m' /\ wmono rsegs mC m' /\ mem_inv rsegs m'
/\ rmrep (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
(put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))) m'
/\ ticks_ok (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
(put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcedb0) fc None mC (seg_rom rsegs)).
Proof.
intros until mC. intros MST MWT CR MRC TKC MIC.
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
set (st0' := enf0_st st g b idx) in *.
assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
pose proof (rmeta_slot_bounds st0' mC mt MRC MST0) as (Tpos & TC & TI & _ & _).
change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
pose proof (rmeta_chunk_facts st0' mC mt MRC MST0) as (_ & _ & _ & _ & _ & GDJ & _).
assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl rsegs mC) as WM.
pose proof MWT as (LI0 & FB0 & SCR0 & ML0). pose proof (meta_word_range _ MWT) as MWR.
unfold alloc_ceiling in TC.

rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
rmeta_open (conc st mt) MUt WMt.
step.

step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
set (w := meta_word (get_meta_rec st mt)) in *.
rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
rewrite (meta_word_mod4096 st g b idx j _ MWT).
step.
lazymatch goal with H : rw_cells rsegs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
[ eapply rmrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
| clear MUt WMt H ] end.
set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).

pose proof (land31_range idx) as L31.
assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
{ change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
[| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
by (unfold wa; f_equal; unfold P; lia).
step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).

step. rewrite (unsigned_lit cnt), swrap32_small by lia.
step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.

pose proof MR5 as (_ & _ & _ & _ & _ & SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
by (unfold wa; f_equal; unfold P; lia).
st1.
assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
rewrite <- (lor_192 (Z.land idx 31)) by lia.
rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.

step. rewrite ?(unsigned_lit P) by (unfold P; lia).
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.

#[using="m1 r j N MR STR SO"] Lemma rzero_loop_walk : forall k (i szc cnt : Z) stz mC0 mC
(ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
Z.of_nat k = cnt + 1 - i -> 0 <= i <= cnt -> 1 <= szc -> 0 <= cnt < 4096 -> 16 + 16 * szc * cnt <= stride ->
s_regions stz = s_regions st -> s_groups stz = s_groups st ->
rmrep stz mC -> ticks_ok stz -> mem_inv rsegs mC ->
munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 mC -> wmono rsegs mC0 mC ->
evt rsegs (fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (cnt - 1)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf0a8) fc None m' (seg_rom rsegs)
/\ munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 m' /\ wmono rsegs mC0 m' /\ mem_inv rsegs m'
/\ rmrep (zero_hdrs (pp st g b idx) (16 * szc) i k stz) m' /\ ticks_ok (zero_hdrs (pp st g b idx) (16 * szc) i k stz)
/\ s_regions (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_regions st /\ s_groups (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_groups st
/\ (forall x, (forall j, i <= j <= cnt -> bv_unsigned x <> P + 12 + 16 * szc * j) -> m' x = mC x))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt + 1 - i)) (Z_to_bv 64 (P + 12 + 16 * szc * i)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcedd8) fc None mC (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
{ exfalso. lia. }
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).

assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
pose proof MRz as (WFz & _ & _ & _ & _ & SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
by (unfold wa; f_equal; unfold P; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
specialize (MR2 Hr' Hk ltac:(lia)).
assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
{ intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & _ & GWF).
destruct (GWF b0 gh Hb0) as (r0 & _ & _ & _ & _ & M16).
destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).

pose proof STR as STRdep__.
clear - CONTRA E0 E1 E2.
replace (stride * idx) with (16 * (stride / 16) * idx) in CONTRA by (rewrite <- E2; reflexivity).
lia. }
specialize (MR2 NOG ltac:(lia)). clear NOG.
replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
[ intros u Hu Hux;
rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
exfalso; lia
| apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
apply (wmono_write rsegs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
[| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
end;
clear SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
end.

step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
step. rewrite ?unsigned_lit by lia.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
eapply evt_mono.
{ (eapply (IH (i + 1) szc cnt);
[ lia | lia | exact SZC | exact CNT | exact FIT
| rewrite s_regions_wr8; exact RGz
| rewrite s_groups_wr8; exact GRz
| exact MR2
| apply ticks_ok_wr8; exact TKz
| assumption | exact MU | exact WM ]). }
cbv beta. intros ms' (m' & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & PW).
eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
split; [exact X6|]. split; [exact X7|].
intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
-
assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].

step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
apply evt_done. eexists. split; [reflexivity|].
cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.

End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w Q9Ay.Mq3 QTyG.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb QdZ1.Mq2 QmBS.Mq1 Qlfl.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof.
intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.

#[using="Type"] Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
rewrite (mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal.
Qed.

#[using="Type"] Lemma unsigned_mod32_add_not a b : 0 <= b < 2^64 ->
(bv_unsigned (wz (sxv a)) + Z.lxor b 18446744073709551615) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
intros Hb. rewrite zb_lxor_ones by lia. rewrite (wz_unsigned (sxv a)) by (apply sxv_range).
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l.
replace (a + (18446744073709551615 - b)) with ((a - 1 - b) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
#[using="Type"] Lemma unsigned_mod32_swrap_add_not a b :
bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
pose proof (sxv_range b) as RB.
rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia.
unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
clearbody x y. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof.
intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
rewrite <- !Z.land_assoc. reflexivity.
Qed.

Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
(r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

Definition rtailW : list (Z * Z) :=
[(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z.

#[using="r AV FR SC CNT AI ML MST REC Hr Hk P0 P16 PEND GNONE NOGRP OLD12 UR ACT TK"] Lemma rtail_walk :
forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
rmrep stT mC -> mem_inv rsegs mC ->
evt rsegs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf200) fc None m' (seg_rom rsegs)
/\ munch rtailW mC m' /\ wmono rsegs mC m' /\ mem_inv rsegs m'
/\ rmrep (stFin stT sc cnt ai ml mt p) m' /\ ticks_ok (stFin stT sc cnt ai ml mt p))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf0a8) fc None mC (seg_rom rsegs)).
Proof.
intros until mC. intros MR MI.
pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl rsegs mC) as WM. unfold rtailW in MU.
pose proof (rmeta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
pose proof (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
pose proof (AV_FR_range stT cnt ai mt p CNT AI P0) as (AVR & FRR & AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.

destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
unfold RCTX, RMLOCK, alloc_ceiling in *.

pose proof (rmrep_usage_read (stA stT p) mC sc (wa (6566376 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
change (usage (stA stT p) sc) with (usage stT sc) in RDU.
replace (wa (6566376 + 464 + 8 * sc)) with (Z_to_bv 64 (6566368 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
step. clear RDU.

step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.

pose proof MRA as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (usages (stA stT p)) sc (wa (6566376 + 464 + 8 * sc)) USG
ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
replace (wa (6566376 + 464 + 8 * sc)) with (Z_to_bv 64 (6566368 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
rraw_store_finish0 (6566376 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear MRA TKA.

step. rewrite ?(unsigned_lit ai) by lia. rewrite QTyG.sllw2_word by lia.
step.
set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
rmeta_open G MUa WMa.

step. step.
assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
{ subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
rewrite (sx32_congr v3 AV V3).

step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite QTyG.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
step. step.
set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
{ subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }

step. step.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
| clear MUa WMa; rename H into CH1 ] end.
assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear MRB TKB MSTB.

pose proof MRC as (WFC & _ & _ & _ & _ & SHC). pose proof WFC as (_ & _ & DJ & _ & WG).
destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
destruct (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) as (hb & LHB & HB) end.
destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HDR : rw_cells rsegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
[ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
| clear HB LHB ] end.
pose proof (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _).
pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.

step.

step.
pose proof (byte_range y8) as Y8.
step. unfold zxb.

step. rewrite ?(unsigned_lit ai) by lia.
replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
step.
pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
rewrite (land224_m32 (bv_unsigned y8)) by lia.
pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].

set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.

lazymatch goal with H : rw_cells rsegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
rename H into HDR2;
assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
| assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
[ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
| rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
| ] ] end.
{
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
- unfold RCTX in X1. lia.
- unfold RMLOCK in X2. lia.
- unfold RNEED_LOCKS in X3. lia.
- unfold RPAGE_SIZE in X4. lia.
- change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
destruct (rarea_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
- change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
destruct (rgroup_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
+ rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
+ pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
- change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
destruct (N.eq_dec q (fst p)) as [->|NE].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
- unfold RGOT_SSP in X5. lia.
- unfold RSSP_GUARD in X6. lia. }
clear MRC MRC2 MUb WMb HDR2.
assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear TKC MSTC.

pose proof MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
rmchunk MRD MSTD CH.
change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
rmeta_open G MUc WMc.

step. step. step. step. step.
rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
rewrite (unsigned_lit W), EW, land_pg_mask by lia.

step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
step. rewrite ?unsigned_lit by lia.

step. step. step. step.
rewrite ?(unsigned_lit (mask_upto ai)) by lia.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_read rsegs mX (6566376 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (6566376 + 80 + 8 * sc)) H
(actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
replace (wa (6566376 + 80 + 8 * sc)) with (Z_to_bv 64 (6566456 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step. step. step.

lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]
| clear MUc WMc; rename H into CH3 ] end.
{ unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
unfold wz. rewrite !app_nil_r.
rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
fold AV. Z.div_mod_to_equations. lia. }
do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
{ reflexivity. }
{ cbn. tauto. }
assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
clear MRD TKD MSTD.

clear CH3.
lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_store_ok rsegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (6566376 + 80 + 8 * sc)) H
ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
replace (wa (6566376 + 80 + 8 * sc)) with (Z_to_bv 64 (6566456 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
st1.
replace (Z_to_bv 64 (6566456 + 8 * sc + 0)) with (Z_to_bv 64 (6566456 + 8 * sc)) in SOK by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
rraw_store_finish0 (6566376 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.

step.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact MRF| exact TKE].
Qed.
End TAIL.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4 QDUx.Mq7.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w Q9Ay.Mq1.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb QdZ1.Mq2 QmBS.Mq1 Qlfl.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition rseqW : list (Z * Z) := [(RCTX + 848, RCTX + 913)]%Z.

#[using="SC"] Lemma rbounce_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
mem_inv rsegs m ->
evt rsegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef20) fc None m' (seg_rom rsegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch rseqW m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcec6c) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MR SEQ BR USR MI.
pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl rsegs m) as WM. unfold rseqW in MU.
unfold RCTX, RMLOCK in *.

assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
rmrep stX mX -> stX = account_bounce sc st -> mem_inv rsegs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
munch [(6566376 + 848, 6566376 + 913)]%Z m mX -> wmono rsegs m mX ->
evt rsegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 6566368) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef20) fc None m' (seg_rom rsegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch [(6566376 + 848, 6566376 + 913)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 6566368) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef1c) fc None mX (seg_rom rsegs))).
{ intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
pose proof (rmrep_seq_read stX mX (wa (6566376 + 912)) MRX eq_refl) as RDS.
replace (wa (6566376 + 912)) with (Z_to_bv 64 (6566368 + 920)) in RDS by (unfold wa; f_equal; lia).
assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
{ rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite SQX in RDS.
step. rewrite ?zxb_b8 by lia. clear RDS.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }

step. rewrite ?(unsigned_lit sc) by lia. step.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{
assert (HO : sc_in_seq_range sc = false).
{ unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
- replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
step. step.
eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
- unfold account_bounce. rewrite HO. reflexivity.
- unfold is_bouncing. rewrite HO. reflexivity. }
rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
destruct (Z.lt_ge_cases sc 7) as [L7|G7].
{ exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
rewrite Z.mod_small in K by lia.
assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).

step. rewrite ?(unsigned_lit (sc + -7)) by lia.
pose proof (rmrep_bounces_read st m (sc - 7) (wa (6566376 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
replace (wa (6566376 + 880 + (sc - 7))) with (Z_to_bv 64 (6566368 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
step. rewrite ?zxb_b8 by lia. clear RDB.
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_read rsegs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (6566368 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
ltac:(unfold wa, RCTX; f_equal; lia)) as RDU. clear US.
step. rewrite ?zxb_b8 by lia. clear RDU.

step. step.
set (nos := 100 <=? bounces st (sc - 7)).
assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
{ rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
change (bv_wrap 64 100) with 100.
destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
rewrite A3. clear A3.
assert (AB : account_bounce sc st =
(if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
else st)) by (unfold account_bounce; rewrite IN; reflexivity).

step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
{ eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }

pose proof (rmrep_seq_read st m (wa (6566376 + 912)) MR eq_refl) as RDS.
replace (wa (6566376 + 912)) with (Z_to_bv 64 (6566368 + 920)) in RDS by (unfold wa; f_equal; lia).
step. rewrite ?zxb_b8 by lia. clear RDS.
step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
{
apply Z.ltb_lt in K2.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite Bool.andb_false_r. exact MR. }
apply Z.ltb_ge in K2.
assert (AB2 : account_bounce sc st =
(if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
{ rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
clear AB K1 K2.
pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _).
pose proof (u8arr_store_ok rsegs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (6566368 + (sc + -7) + 888)) BA
ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear BA.

step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
-
step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6566376 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. step. st1. rewrite (le1_lit 150) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6566376 + 880 + (sc - 7)) [b8 150] MU WM SOK.
eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="Type"] Lemma rseq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m0 m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> mem_inv rsegs m ->
munch rseqW m0 m -> wmono rsegs m0 m ->
evt rsegs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef4c) fc None m' (seg_rom rsegs)
/\ munch rseqW m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ rmrep (step_seq st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 (wz (c_seq (ctx st))) a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef20) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
set (q := c_seq (ctx st)) in *.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6 & _) & _).
unfold RCTX, RMLOCK in *. unfold ctx_tail_cells in C6.
replace (6566376 + 912) with 6567288 in C6 by reflexivity. replace (6566376 + 848) with 6567224 in US by reflexivity.

assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv rsegs mj ->
munch [(6566376 + 848, 6566376 + 913)]%Z m0 mj -> wmono rsegs m0 mj ->
evt rsegs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 6566368) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef4c) fc None m' (seg_rom rsegs)
/\ munch [(6566376 + 848, 6566376 + 913)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 6566368) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef44) fc None mj (seg_rom rsegs))).
{ intros mj stj ns NS MRj CTj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j & _) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
replace (6566376 + 912) with 6567288 in C6j by reflexivity.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (6566368 + 920)) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.

step. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
rraw_store_finish0 (6566376 + 912) [b8 ns] MUj WMj SOK.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }

step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned q) by lia.
eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
-
pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
pose proof (munch_refl [(6566376 + 848, 6566376 + 880)]%Z m) as MUz. pose proof (wmono_refl rsegs m) as WMz.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UZ : u8arr rsegs mX 6567224 (zeros 32));
[ apply (u8arr_of_rw_cells rsegs mX 6567224 32);
lazymatch goal with H : rw_cells rsegs mX 6567224 _ |- _ =>
apply (rw_cells_congr rsegs mX 6567224 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
pose proof MR as (_ & (_ & _ & _ & _ & _ & C6 & _) & _). unfold ctx_tail_cells, RCTX in C6.
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRz : rmrep stz mX);
[ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia];
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
| clear MUc WMc ] end.

step. step.
lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono rsegs m0 ?mX, MIc : mem_inv rsegs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed.

#[using="SC"] Lemma rmm_seq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
mem_inv rsegs m ->
evt rsegs (fun ms' => exists (t0' t1' a3' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 (Z_to_bv 64 31) a6' a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef4c) fc None m' (seg_rom rsegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch rseqW m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (step_seq (account_bounce sc st)) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcec6c) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MR SEQ BR USR MI.
eapply evt_cut; [eapply rbounce_walk; eassumption|].
cbv beta. intros ms' (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR').
assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
{ unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite <- SEQ'.
eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
cbv beta. intros ms'' (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'').
do 6 eexists. split; [reflexivity|]. subst a3'.
repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.

End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq0 Q9Ay.Mq1 Q9Ay.Mq2.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb QmBS.Mq1 Qlfl.Mq3 Qlfl.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

Definition rmmc_post (ra sp gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(res : Z * Z) : machine_state -> Prop :=
fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (wz (snd res)) s4 s5 s6 s7 s8 (wz (fst res)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf030) fc None m (seg_rom rsegs).

#[using="SZ RQ"] Lemma rj2c_walk :
forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc m (c1 u1 : Z),
1 <= c1 <= 32 -> 0 <= u1 < 2^61 ->
evt rsegs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 s6 s7 (wz size) s10 s11 t3 t4 t5 t6 F fc m
(mm_final size req u1 c1 nos))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) a4 a5 a6 a7
(Z_to_bv 64 req) s3 s4 s5 s6 s7 (wz size) (wz c1) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcefd4) fc None m (seg_rom rsegs)).
Proof.
intros until u1. intros CR UR.
assert (SCR : 16 <= size * c1 < 2^24) by nia.
pose proof (zb_b2z_range nos) as NR.
unfold rmmc_post.

step. rewrite (wz_unsigned size), (wz_unsigned c1) by lia.
step. step. step. step. step. step.
rewrite !land_4095_word. rewrite ?(unsigned_lit (size * c1)) by lia.
replace (-16 + - (size * c1)) with (- (size * c1 + 16)) by lia.
set (nd0 := round_up_pg (size * c1 + 16)).
pose proof (round_up_pg_alt (size * c1 + 16)) as RU. pose proof (round_up_pg_range (size * c1 + 16) ltac:(lia)) as RUR.
replace (size * c1 + Z.land (- (size * c1 + 16)) 4095 + 16) with nd0 by lia.
fold nd0 in RUR.
assert (EF : mm_final size req u1 c1 nos = (if negb nos && (c1 <=? 7) then mm_small size req u1 c1 nd0 else (c1, nd0))).
{ unfold mm_final, UNIT. reflexivity. }

step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
{
apply evt_done. rewrite EF. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]). cbn [negb andb fst snd].
do 9 eexists. reflexivity. }
replace nos with false in EF |- * by (destruct nos; cbn in KN; [lia| reflexivity]). cbn [negb andb] in EF.

step. step. if_cases K7; zify_cond K7; rewrite ?(wz_unsigned c1), ?unsigned_lit in K7 by lia.
{
apply evt_done. rewrite EF. replace (c1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
do 9 eexists. reflexivity. }
replace (c1 <=? 7) with true in EF by (symmetry; apply Z.leb_le; lia).

step. step. step. step. step.
rewrite (Z.land_comm 4095), land_4095_word. rewrite ?(unsigned_lit req) by lia.
replace (-20 + - req) with (- (req + 20)) by lia.
set (rq' := round_up_pg (req + 20)).
pose proof (round_up_pg_alt (req + 20)) as RU2. pose proof (round_up_pg_range (req + 20) ltac:(lia)) as RUR2.
replace (req + Z.land (- (req + 20)) 4095 + 20) with rq' by lia. fold rq' in RUR2.
assert (ES : mm_small size req u1 c1 nd0 = (if (rq' <? size + 16) || ((4 * PGSZ <=? rq') && (u1 <? 2 * c1)) then (1, rq') else (c1, nd0))).
{ unfold mm_small, IB, UNIT. replace (req + 4 + 16) with (req + 20) by lia. reflexivity. }
rewrite ES in EF. clear ES. unfold PGSZ in EF.

step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (size + 16)), ?unsigned_lit in K1 by lia.
-
replace (rq' <? size + 16) with false in EF by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in EF.
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
+
apply evt_done. rewrite EF. replace (4 * 4096 <=? rq') with false by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd].
do 9 eexists. reflexivity.
+ replace (4 * 4096 <=? rq') with true in EF by (symmetry; apply Z.leb_le; lia). cbn [andb] in EF.

step. rewrite (wz_unsigned c1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite swrap32_small by lia.
step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned u1), ?unsigned_lit in K3 by lia.
*
step. step. step.
apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
do 9 eexists. reflexivity.
* apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
do 9 eexists. reflexivity.
-
replace (rq' <? size + 16) with true in EF by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in EF.
step. step. step.
apply evt_done. rewrite EF. cbn [fst snd]. do 9 eexists. reflexivity.
Qed.

#[using="SC SZ"] Lemma rred_walk :
forall (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (cnt u1 : Z),
1 <= cnt <= 32 -> 0 <= u1 < 2^61 ->
evt rsegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcefd4) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5 a6 a7
(Z_to_bv 64 req) (wz cnt) s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef60) fc None m (seg_rom rsegs)).
Proof.
intros until u1. intros CR UR.
assert (SCR : 16 <= size * cnt < 2^24) by nia.
pose proof (zb_b2z_range nos) as NR. pose proof (Q9Ay.Mq2.land3_range sc) as L3.

assert (J28 : forall (a5' a6' a7' t0' s9' : word) (c : Z), c = mm_cnt_red sc size cnt u1 nos ->
evt rsegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcefd4) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) (wz c) s4 s5 s6 s7 (wz size) s9' s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcefd0) fc None m (seg_rom rsegs))).
{ intros a5' a6' a7' t0' s9' c ->. step. apply evt_done. do 5 eexists. reflexivity. }

step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2, swrap32_small by lia. change (2 ^ 2) with 4.
step. if_cases KU; zify_cond KU; rewrite ?(wz_unsigned u1), ?unsigned_lit in KU by lia.
{ eapply J28. unfold mm_cnt_red. replace (u1 <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }

step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
{ eapply J28. unfold mm_cnt_red. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]).
rewrite Bool.andb_false_r. reflexivity. }
assert (EN : nos = false) by (destruct nos; cbn in KN; [lia| reflexivity]).
assert (ER : mm_cnt_red sc size cnt u1 nos =
(if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt)).
{ unfold mm_cnt_red. rewrite EN. replace (u1 <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
unfold PGSZ in ER.

step. rewrite ?(unsigned_lit sc) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 3) with 32768.
step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
-
replace (Z.land sc 3 =? 1) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
+
replace (Z.land sc 3 =? 2) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.

step. step. step.
step. if_cases KC; zify_cond KC.
*
rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
destruct (Z.ltb_spec (Z.land sc 3) 1) as [A1|A1]; destruct (Z.ltb_spec 32768 (size * cnt)) as [LT|GE]; cbn [Z.b2z Z.land] in KC; try (exfalso; apply KC; reflexivity); [].
assert (E0 : Z.land sc 3 = 0) by lia.
step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [exfalso; lia|].
step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [| exfalso; lia].
apply evt_done. rewrite ER, E0. cbn [Z.eqb andb]. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
*
assert (NC : ~ (Z.land sc 3 = 0 /\ 32768 < size * cnt)).
{ intros [E0 LT]. rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
replace (Z.land sc 3 <? 1) with true in KC by (symmetry; apply Z.ltb_lt; lia).
replace (32768 <? size * cnt) with true in KC by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z true)) with 1 in KC. lia. }
clear KC. step. step.
step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
{
apply evt_done. rewrite ER. replace (Z.land sc 3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
do 5 eexists. reflexivity. }
rewrite KD in ER |- *. cbn [Z.eqb andb] in ER.
replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia).

step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [exfalso; lia|].
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 1) with 8192.
step. if_cases KQ; zify_cond KQ; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KQ by lia.
-- eapply J28. rewrite ER. replace (2 * 4096 <? size * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
-- step. eapply (J28 _ _ _ _ _ 5). rewrite ER. replace (2 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+
rewrite KB in ER |- *. cbn [Z.eqb andb] in ER.
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
*
replace (4 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
step. step. step.
step. if_cases KG; zify_cond KG.
{ exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
apply evt_done. rewrite ER. do 5 eexists. reflexivity.
*
step. step. apply evt_done. rewrite ER. replace (4 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
-
rewrite KA in ER |- *. cbn [Z.eqb andb] in ER.
step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
+
replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
step. step. step.
step. if_cases KG; zify_cond KG.
{ exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
apply evt_done. rewrite ER. do 5 eexists. reflexivity.
+
step. step. apply evt_done. rewrite ER. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
Qed.

#[using="SC"] Lemma rusage1_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (u0 : Z),
rmrep st m -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
evt rsegs (fun ms' => exists (a5' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz (mm_usage1 st sc u0)) a1 a2 a3 a4 a5' a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef60) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) a1 a2 a3 a4 (Z_to_bv 64 31) a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef4c) fc None m (seg_rom rsegs)).
Proof.
intros until u0. intros MR UR USR. unfold RMLOCK, RCTX in *.
pose proof (land_upper sc 1 ltac:(lia) ltac:(lia)) as L1R.

step. if_cases K; unfold bv_lts in K; rewrite !signed_lit_small in K by lia.
{ apply Z.ltb_lt in K. apply evt_done. unfold mm_usage1. replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
eexists. reflexivity. }
apply Z.ltb_ge in K.

step. rewrite ?(unsigned_lit sc) by lia.
step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit (Z.land sc 1)) in KO by lia.
{
assert (ODD : Z.even sc = false).
{ rewrite even_of_land1. apply Z.eqb_neq. exact KO. }
apply evt_done. unfold mm_usage1. rewrite ODD. cbn [andb]. eexists. reflexivity. }
assert (EV : Z.even sc = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact KO).

pose proof (rmrep_usage_read st m (sc + 1) (wa (6566376 + 464 + 8 * (sc + 1))) MR ltac:(lia) eq_refl) as RDU.
replace (wa (6566376 + 464 + 8 * (sc + 1))) with (Z_to_bv 64 (6566368 + 8 * sc + 480)) in RDU by (unfold wa; f_equal; lia).
pose proof (USR (sc + 1)) as U1R.
step. clear RDU. step. rewrite (wz_unsigned (usage st (sc + 1))), (wz_unsigned u0) by lia.
apply evt_done. unfold mm_usage1. rewrite EV. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
eexists. unfold wz. rewrite (Z.add_comm (usage st (sc + 1)) u0). reflexivity.
Qed.

#[using="SC SZ RQ"] Lemma rmmc_walk :
forall (ra sp gp tp t0 t1 t2 s1 a6 a7 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (cnt u0 : Z),
rmrep st m -> 1 <= cnt <= 32 -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
evt rsegs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (wz size) s10 s11 t3 t4 t5 t6 F fc m
(mm_final size req (mm_usage1 st sc u0) (mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos) nos))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) (Z_to_bv 64 31) a6 a7
(Z_to_bv 64 req) (wz cnt) s4 s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (wz size) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcef4c) fc None m (seg_rom rsegs)).
Proof.
intros until u0. intros MR CR UR USR.
assert (U1R : 0 <= mm_usage1 st sc u0 < 2^61).
{ unfold mm_usage1. pose proof (USR (sc + 1)). destruct (_ && _); lia. }
eapply evt_cut. { eapply (rusage1_walk _ _ _ _ t0 t1 t2 s1); [exact MR| exact UR| exact USR]. }
cbv beta. intros ms' (a5' & ->).
eapply evt_cut. { eapply (rred_walk _ _ _ _ t0 t1 t2 s1); [exact CR| exact U1R]. }
cbv beta. intros ms'' (a5'' & a6'' & a7'' & t0'' & s3'' & ->).
assert (CRR : 1 <= mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos <= 32).
{ unfold mm_cnt_red. destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia. }
eapply evt_mono. { eapply rj2c_walk; [exact CRR| exact U1R]. }
cbv beta. unfold rmmc_post. intros ms3 (t0x & a0' & a1' & a2' & a3' & a4' & a5x & a6x & a7x & ->).
do 9 eexists. reflexivity.
Qed.
End MMC.

End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnOf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq2.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qn9M.Mq0 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb QdZ1.Mq2 QnkH.Mq6 QmBS.Mq1 Qlfl.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmm_call_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
evt rsegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 0xcf050) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) s3 (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf030) fc None m (seg_rom rsegs)).
Proof.
intros. unfold rmmap_entry.
step. step. step. step. step. step. step. step.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma rmm_ret_fail_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
evt rsegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf178) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf050) fc None m (seg_rom rsegs)).
Proof.
intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
apply evt_done. reflexivity.
Qed.

Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

#[using="SC CNT SZ ND NDA XA XA2 MST REC HC CR"] Lemma rmm_ret_ok_walk :
forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) F fc m,
rmrep st2 m -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf0a8) fc None m' (seg_rom rsegs)
/\ munch [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf050) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MR MI.
pose proof (munch_refl [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold alloc_ceiling, RCTX, RMLOCK in *.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
clear K.

step.
rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
rmeta_open G MUa WMa.
step.

step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
rewrite (divu_word 4080 size) by lia.
pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
set (d := 4080 / size) in *.

pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. rewrite HC in CX1. unfold RCTX in CX1.
step. rewrite (sx32_wz_sxv c) by lia.

step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).

assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
{ unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia. }
step.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
[ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
| clear MUa WMa H ] end.
set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.

pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (6566368 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
clear CX1.
st1.
rewrite le4_swrap_succ by lia.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold RCTX in MR4 end.
clear MR3.
rraw_store_finish0 (6566376 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
{ unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
rewrite <- E4 in MR4.
assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).

step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
evt rsegs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 6566368) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf0a8) fc None m' (seg_rom rsegs)
/\ munch [(G, G + 40); (6566376 + 12, 6566376 + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 6566368) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf094) fc None mX (seg_rom rsegs))) end.
{ intros a2v mn Hmn ->.
assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).

step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
replace (cnt + -1) with (cnt - 1) by lia.
assert (AI : mm_ai cnt size = (if mn =? 0 then 0 else mn - 1)).
{ unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
destruct (Z.ltb_spec cnt d) as [LT|GE].
- replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
- replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eqb_spec d 0) as [E0|NE0].
+ rewrite E0. reflexivity.
+ replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
= Z_to_bv 64 (mm_ai cnt size)).
{ rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
destruct (Z.eqb_spec mn 0) as [E0|NE0].
- rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
- rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
rewrite EA2.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR4| exact C4']. }
if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
-
eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End MMOK.

End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QTyG.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb QdZ1.Mq2 QmBS.Mq1 Qlfl.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_set_free_head : forall st m v,
rmrep st m ->
rmrep (upd_ctx (set_free_meta_head v) st) (write_to_mem m (wa (RCTX + 16)) (le8 (pw st v))).
Proof.
intros st m v MR. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6 & X7) & _).
pose proof (length_le8 (pw st v)) as L8.
pose proof (munch_write [(RCTX + 16, RCTX + 24)] m m (RCTX + 16) (le8 (pw st v)) (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 16)) (le8 (pw st v)) (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia.
- left.
pose proof (rw_cells_write rsegs m RCTX (ctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
cbn [cbytes cell_upd ctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
exact W.
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.

#[using="Type"] Lemma rmrep_extW : forall stX stY m,
rmrep stX m ->
s_regions stY = s_regions stX -> ctx stY = ctx stX -> (forall q, get_meta_rec stY q = get_meta_rec stX q) ->
s_areas stY = s_areas stX -> s_groups stY = s_groups stX -> (forall rid, get_shadow stY rid = get_shadow stX rid) ->
s_reserved stY = s_reserved stX ->
rmrep stY m.
Proof.
intros stX stY m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
- eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.
End RC__1.

Ltac rraw_store_finishF A bs' FR MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.

Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition rfailW (spv : Z) : list (Z * Z) :=
(spv - 144, spv) :: (G, G + 40) :: (RCTX + 16, RCTX + 24)
:: match c_free_meta_head (ctx st) with
| Some h => (conc st h, conc st h + 40)
:: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
| None => []
end.

#[using="MST FL"] Lemma rfailm1_walk :
forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
rmrep st m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
alloc_ceiling <= bv_unsigned sp - 144 ->
evt rsegs (fun ms' => exists (a1' s6' : word) m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf200) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
/\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (as_fm_st st mt) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcedf8) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros MR MI FR SPC.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold rfailW. unfold RCTX, RMLOCK, alloc_ceiling, rta_frame in *.

assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
evt rsegs (fun ms' => exists m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 6566368) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcee54) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (put_meta mt meta0 st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 6566368) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcedf8) fc None m (seg_rom rsegs))).
{ intros W HW1 HW2.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
rmchunk MR MST CH. fold G in CH.

lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
[ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
| clear CH ] end.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.
rmeta_open G MUb WMb.

step. st1. step. st1. step. st1. step. st1. step. st1.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR0 : rmrep (put_meta mt meta0 st) mX);
[ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
| clear H MUb WMb ] end.
lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
[ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
| cbn [cells_size csize] in WR |- *; exact WR]
| clear H ] end.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
split; [assumption|]. split; [assumption| exact MR0]. }
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
-
destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (6566376 + 16, 6566376 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).

rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rewrite HP in CH. cbn [oconc] in CH.
step. clear CH.

rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
rmeta_open G MUb WMb.
st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
[ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
| clear MUb WMb H ] end.
set (st2 := put_meta mt _ st1) in MR2.
assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).

rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rmeta_open (conc st p) MUc WMc.
st1.
lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
[ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st2 mt) with G; reflexivity
| clear MUc WMc H ] end.
set (st3 := put_meta p _ st2) in MR3.
assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).

rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
change (conc st mt) with G in CH.
step. clear CH.

rmchunk MR3 MSh3 CH.
rmeta_open (conc st h) MUd WMd.
st1.
lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
[ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st3 mt) with G; reflexivity
| clear MUd WMd H ] end.

step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
eapply (rmrep_extW _ _ _ MR4); try reflexivity.
intros q. unfold st3, st2, st1, st0, upd_meta.
destruct (decide (q = h)) as [->|NQh].
{ rewrite !get_meta_rec_put_same. f_equal.
destruct (decide (h = p)) as [<-|NHp].
- rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
- rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
destruct (decide (q = p)) as [->|NQp].
{ rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
-
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (6566376 + 16, 6566376 + 24)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1. st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.

step.
pose proof MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (6566368 + 24)) CX1 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
rraw_store_finishF (6566376 + 16) (le8 (wz G)) FR1 MU WM1 SOK.

step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_single. cbn [set_head].
eapply (rmrep_extW _ _ _ MR2); try reflexivity.
intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.

#[using="MST FL"] Lemma rfailm2_walk :
forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
rmrep st m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
alloc_ceiling <= bv_unsigned sp - 144 ->
evt rsegs (fun ms' => exists (s6' : word) m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf200) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
/\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (as_fm_st st mt) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf178) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros MR MI FR SPC.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold rfailW. unfold RCTX, RMLOCK, alloc_ceiling, rta_frame in *.

assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
evt rsegs (fun ms' => exists m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 6566368) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf1d0) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (put_meta mt meta0 st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 6566368) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf178) fc None m (seg_rom rsegs))).
{ intros W HW1 HW2.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
rmchunk MR MST CH. fold G in CH.

lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
[ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
| clear CH ] end.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.
rmeta_open G MUb WMb.

step. st1. step. st1. step. st1. step. st1. step. st1.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR0 : rmrep (put_meta mt meta0 st) mX);
[ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
| clear H MUb WMb ] end.
lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
[ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
| cbn [cells_size csize] in WR |- *; exact WR]
| clear H ] end.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
split; [assumption|]. split; [assumption| exact MR0]. }
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
-
destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (6566376 + 16, 6566376 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).

rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rewrite HP in CH. cbn [oconc] in CH.
step. clear CH.

rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
rmeta_open G MUb WMb.
st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
[ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
| clear MUb WMb H ] end.
set (st2 := put_meta mt _ st1) in MR2.
assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).

rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rmeta_open (conc st p) MUc WMc.
st1.
lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
[ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st2 mt) with G; reflexivity
| clear MUc WMc H ] end.
set (st3 := put_meta p _ st2) in MR3.
assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).

rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
change (conc st mt) with G in CH.
step. clear CH.

step.
rmchunk MR3 MSh3 CH.
rmeta_open (conc st h) MUd WMd.
st1.
lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
[ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st3 mt) with G; reflexivity
| clear MUd WMd H ] end.

step.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
eapply (rmrep_extW _ _ _ MR4); try reflexivity.
intros q. unfold st3, st2, st1, st0, upd_meta.
destruct (decide (q = h)) as [->|NQh].
{ rewrite !get_meta_rec_put_same. f_equal.
destruct (decide (h = p)) as [<-|NHp].
- rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
- rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
destruct (decide (q = p)) as [->|NQp].
{ rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
-
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (6566376 + 16, 6566376 + 24)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1. st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.

step.
pose proof MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (6566368 + 24)) CX1 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
rraw_store_finishF (6566376 + 16) (le8 (wz G)) FR1 MU WM1 SOK.

step.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_single. cbn [set_head].
eapply (rmrep_extW _ _ _ MR2); try reflexivity.
intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
End FAILM.

End RC__2.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QDUx.Mq0 Q9Ay.Mq3 Q9Ay.Mq4 Q9Ay.Mq5 Q9Ay.Mq6 Q9Ay.Mq7 Q9Ay.Mq8 QJE4.Mq3.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qn9M.Mq0 Qv4L.Mq8 Qi8L.Mq4 QdZ1.Mq2 QQbX.Mq2 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb.
Import QmBS.Mq1 Qlfl.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lw_slli52_srli58_sc mq : mw_ok mq ->
Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 (meta_word mq)))) 52))) 58)
= Z_to_bv 64 (m_sizeclass mq).
Proof.
intros MWq. pose proof (meta_word_range _ MWq) as WR. pose proof MWq as (LI & FB & SCR & ML).
f_equal. unfold sx32. rewrite (unsigned_lit (meta_word mq)) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite swrap32_eq'.
unfold meta_word.
Z.div_mod_to_equations. nia.
Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.

#[using="RC__ mr MR MSL AV0"] Lemma ravz_pre_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
bv_unsigned gw = G -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceac8) fc None m (seg_rom rsegs))
(MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceabc) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros HG MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0 in CH. fold G in CH. rewrite <- HG in CH.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
apply evt_done. reflexivity.
Qed.

#[using="b MR MSL AV0 Hmem Hgh AI FR32 MW MASK BNC SC0"] Lemma ravz_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
bv_unsigned gw = G -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz (sxv mask)) a2' a3' a4' a5' a6' a7' s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceb40) fc None m' (seg_rom rsegs)
/\ munch [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep st5 m')
(MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceac8) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros HG MI. unfold rt1_regs.
pose proof (munch_refl [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & G4 & G24). fold G in Gpos, GC, GI, G4, G24.
pose proof (meta_word_range _ MW) as MWR.
assert (AMO : amo_aligned AW (Z_to_bv 64 (bv_unsigned gw + 28)) = true).
{ apply amo_aligned_intro; [unfold alloc_ceiling in GC; lia|]. rewrite HG. clear -G4. Z.div_mod_to_equations. lia. }
clear G4 G24.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.

step.
destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8). unfold wa in RD8.
pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
step.

step. step.
assert (W8M : bv_unsigned w8 mod 32 = ai).
{ unfold ai. rewrite <- L8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
unfold zxb. rewrite (unsigned_lit (bv_unsigned w8)) by lia.
rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite W8M.
set (y := 2 ^ (ai + 1)).

step. step. rewrite negw_word.

pose proof (sxv_range f) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range (y - 1)) as RY1.
step. rewrite sx32_wz_sxv by lia.
step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.

clear CH. rmeta_open G MUa WMa. rewrite <- HG in MUa.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
step. if_false.
amo_step AMO.
step. if_false.
step. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. step. if_false.

step. rewrite addiw_m1_word.
step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
step.

assert (AI31 : Z.land ai 31 = ai).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (ACT : act = y - 1) by (unfold act, mask_upto, y; reflexivity).
assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
assert (Ypos : 0 < y) by (unfold y; apply Z.pow_pos_nonneg; lia).
pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR4 : rmrep st4 mX) end.
{ rewrite HG in MUa, CH. unfold st4. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUa | exact WMa |].
eapply rw_cells_congr; [ | | | exact CH]; [ | reflexivity | cbn; tauto].
unfold meta_cells, pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed oconc].
rewrite meta_word_upd_af. fold mr f. rewrite Hmem, E1. cbn [oconc]. rewrite !le4_sxv by lia. reflexivity. }
clear MUa WMa.

step. if_cases K1; zify_cond K1.
2:{ exfalso. apply MASK. unfold mask. rewrite ACT. apply (proj1 (sxv_zero (Z.land f (y - 1)) ltac:(lia))).
rewrite ?wz_unsigned in K1 by (apply sxv_range). first [exact K1 | change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones in K1 by lia; rewrite Z.mod_small in K1 by apply sxv_range; exact K1]. }
clear K1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HRW : ov_read_bytes rsegs mX (wa (bv_unsigned gw + 32)) 4 = Some (le4 (Z_to_bv 64 (meta_word mr))))
by (destruct CH as [[_ B] _]; rewrite (bytes_at_ov_read rsegs mX (bv_unsigned gw) _ 32 4 B) by (cbn; lia); reflexivity) end.
step. step. step.
rewrite (lw_slli52_srli58_sc mr MW).
pose proof MW as (_ & _ & SCR & _). fold mr in SCR.
set (sc := m_sizeclass mr) in *.

step. step. step. if_cases K2; zify_cond K2; change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia.
-
assert (NR : (7 <=? sc) && (sc <? 39) = false).
{ destruct (Z.lt_ge_cases sc 7); [apply Bool.andb_false_intro1; apply Z.leb_gt; lia|].
apply Bool.andb_false_intro2. apply Z.ltb_ge. rewrite Z.mod_small in K2 by lia. lia. }
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite NR. cbn [andb]. exact MR4.
-
assert (SC7 : 7 <= sc) by (destruct (Z.le_gt_cases 7 sc); [assumption| exfalso; clear -K2 H SCR; Z.div_mod_to_equations; lia]).
rewrite Z.mod_small in K2 by lia.
assert (IR : (7 <=? sc) && (sc <? 39) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).

step.
pose proof (rmrep_bounces_read st4 _ (sc - 7) (wa (6566376 + 880 + (sc - 7))) MR4 ltac:(lia) eq_refl) as RDB.
change (bounces st4 (sc - 7)) with (bounces st (sc - 7)) in RDB.
pose proof (BNC (sc - 7)) as BR.
step. rewrite ?zxb_b8 by lia.

step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
+
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
replace (bounces st (sc - 7) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. exact MR4.
+
step. rewrite ?(wz_unsigned (bounces st (sc - 7))) by lia.
pose proof MR4 as (_ & (_ & _ & _ & _ & X5 & _) & _).
pose proof (u8arr_store_ok rsegs _ _ _ (sc - 7) (Z_to_bv 64 (6566368 + (sc + -7) + 888)) X5
ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear X5 RDB.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st4 mX (sc - 7) (bounces st (sc - 7) - 1) MR4 ltac:(lia)) as MR5; unfold RCTX in MR5 end.
rraw_store_finish0 (6566376 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) - 1)] MU WM SOK.
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|].
split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
replace (bounces st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. exact MR5.
Qed.
End AVZ.

Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

#[using="SZ"] Lemma rspan_loop_walk : forall (F : nat) (c span : Z)
(ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
0 <= c -> 0 <= span -> span + size * (Z.of_nat F + 2) < 2^31 -> c + 1 + Z.of_nat F < 2^31 ->
span_exit F span size = true -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (t0' t1' a6' : word),
ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 (wz (span_loop F (c + 1) span size)) (wz size) a6' (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xceed0) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp (wz span) t1 t2 s0 s1 a0 a1 a2 a3 (wz c) (wz size) (wz (span + size - 1)) (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xceebc) fc None m (seg_rom rsegs)).
Proof.
induction F as [|F IH]; intros until m; intros C0 S0 SB CB EX MI; [discriminate|].
cbn [span_exit] in EX. cbn [span_loop].
rewrite Nat2Z.inj_succ in SB, CB.
pose proof (lxor_range31 span (span + size - 1) ltac:(lia) ltac:(lia)) as XR.

step. rewrite ?wz_unsigned by lia.
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (span + size))) with (wz (span + size)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (c + 1))) with (wz (c + 1)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (span + size - 1 + size))) with (wz (span + size + size - 1)) by (rewrite swrap_word, sxv_small by lia; unfold wz; f_equal; lia).
rewrite (Z.lxor_comm (span + size - 1) span).

step. if_cases K.
-
assert (LT : Z.lxor span (span + size - 1) < 4096).
{ unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_lt in K. exact K. }
replace (Z.lxor span (span + size - 1) <? 4096) with true in EX |- * by (symmetry; apply Z.ltb_lt; exact LT).
replace (c + 2) with (c + 1 + 1) by lia.
eapply (IH (c + 1) (span + size)); try assumption; try lia.
- assert (GE : ~ Z.lxor span (span + size - 1) < 4096).
{ intros LT. unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_ge in K. lia. }
replace (Z.lxor span (span + size - 1) <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
apply evt_done. do 3 eexists. reflexivity.
Qed.
End SPANLOOP.
#[using="Type"] Lemma ai_byte_land224 w v : 0 <= w -> 0 <= v ->
Z.land ((Z.lor (Z.land v 31) (Z.land w 224)) mod 256) 31 = Z.land v 31.
Proof.
intros Hw Hv. apply Z.bits_inj'. intros n Hn.
change 256 with (2^8). change 31 with (Z.ones 5).
rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
replace 224 with (Z.shiftl 7 5) by reflexivity.
destruct (Z.ltb_spec n 5).
- rewrite Z.shiftl_spec_low by lia. replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_true_r, andb_false_r, orb_false_r. reflexivity.
- replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.

Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

Ltac ract_prefix CH w8 :=
rmchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
step;
let RD8 := fresh "RD8" in let L8 := fresh "L8" in
destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8); unfold wa in RD8;
let W8R := fresh "W8R" in
pose proof (bv_unsigned_in_range _ w8) as W8R; change (bv_modulus 8) with 256 in W8R;
step;
let W8M := fresh "W8M" in
assert (W8M : bv_unsigned w8 mod 32 = ai0) by (unfold ai0; rewrite <- L8; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
step; unfold zxb; rewrite (unsigned_lit (bv_unsigned w8)) by lia; rewrite (sllw2_word (bv_unsigned w8)) by lia; rewrite W8M;
step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land.

#[using="RC__ b mr MR MSL Hmem Hgh AI0 MASKR"] Lemma ract_skip_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
Z.land mask (mask_upto ai0) <> 0 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' a3' a4' : word),
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xceabc) fc None m (seg_rom rsegs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcea94) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros NZ MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
pose proof (land_upper (mask_upto ai0) mask ltac:(lia) ltac:(lia)) as LR.
step. if_cases K; zify_cond K.
2:{ exfalso. apply NZ. rewrite Z.land_comm. apply (proj1 (sxv_zero (Z.land (mask_upto ai0) mask) ltac:(lia))).
rewrite ?wz_unsigned in K by (apply sxv_range).
first [exact K | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by apply sxv_range; exact K]. }
apply evt_done. do 4 eexists. reflexivity.
Qed.

#[using="b MR MSL SC Hmem Hgh AI0"] Lemma ract_next_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (mn : aptr),
Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some mn -> mn <> g -> meta_slot st mn -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' a3' a4' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xceabc) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_active sc (Some mn) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcea94) fc None m (seg_rom rsegs)).
Proof.
intros until mn. intros ZR GN NEn MSn MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
assert (NEG : conc st mn <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
step. if_cases K; zify_cond K.
{ exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
clear K.

rewrite GN in CH. cbn [oconc] in CH.
step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.

clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (6566376 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6566376 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.

step.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.

#[using="ai0 MR MSL Hgh AI0"] Lemma rspan_tail_walk :
forall (ra sp gp tp t0 t1 t2 s1 a3 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (cnt2 wv : Z),
1 <= cnt2 <= 32 -> 0 <= wv < 256 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3 a4' a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xceac8) fc None m' (seg_rom rsegs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) (Z_to_bv 64 (conc st b)) (Z_to_bv 64 wv) a3 (Z_to_bv 64 cnt2) a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xceee0) fc None m (seg_rom rsegs)).
Proof.
intros until wv. intros C2R WVR UNK GM AV0 MI.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof MR as (_ & _ & _ & _ & GR & _). destruct (GR b gh Hgh) as (w8o & RWB & Hw8o). clear GR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (munch_refl [(conc st b, conc st b + 9)]%Z m) as MUb. pose proof (wmono_refl rsegs m) as WMb.

step. step. rewrite ?(unsigned_lit (cnt2 + -1)) by lia. step. rewrite ?(unsigned_lit wv) by lia. step.
pose proof (land_upper (cnt2 + -1) 31 ltac:(lia) ltac:(lia)) as L2.
pose proof (land_upper wv 224 ltac:(lia) ltac:(lia)) as L1.
rewrite ?(unsigned_lit (Z.land (cnt2 + -1) 31)), ?(unsigned_lit (Z.land wv 224)) by lia.
set (nbv := Z.lor _ _).

step. rewrite (le1_mod nbv). mem_after_store.
pose proof (Z.lor_nonneg (Z.land (cnt2 + -1) 31) (Z.land wv 224)) as NBpos.
pose proof (Z.mod_pos_bound nbv 256 ltac:(lia)) as NBR.
lazymatch goal with H : rw_cells rsegs ?mX (conc st b) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (set_group_active_idx b (cnt2 - 1) st) mX);
[ eapply (rmrep_set_group_ai st m mX b g (g_active_idx gh) (cnt2 - 1) (b8 (nbv mod 256)) MR); [ | exact UNK | exact MUb | exact WMb | | ]
| ] end.
{ rewrite Hgh. destruct gh as [gm gai]. cbn in GM |- *. subst gm. reflexivity. }
{ lazymatch goal with H : rw_cells rsegs _ (conc st b) _ |- _ => rewrite GM in H; exact H end. }
{ rewrite b8_unsigned by lia. subst nbv. replace (cnt2 - 1) with (cnt2 + -1) by lia. apply ai_byte_land224; lia. }

assert (EA2 : s_areas (set_group_active_idx b (cnt2 - 1) st) = s_areas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (ER2 : s_regions (set_group_active_idx b (cnt2 - 1) st) = s_regions st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (EM2 : s_metas (set_group_active_idx b (cnt2 - 1) st) = s_metas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (MS2 : meta_slot (set_group_active_idx b (cnt2 - 1) st) g) by (eapply meta_slot_same_areas; [exact EA2| exact MSL]).
rmchunk MR2 MS2 CH.
replace (get_meta_rec (set_group_active_idx b (cnt2 - 1) st) g) with mr in CH by (unfold mr, get_meta_rec; rewrite EM2; reflexivity).
replace (conc (set_group_active_idx b (cnt2 - 1) st) g) with G in CH by (unfold G, conc, get_region; rewrite ER2; reflexivity).
rewrite AV0 in CH.
step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MUb|]. split; [exact WMb|]. split; [assumption| exact MR2].
Qed.

#[using="MR MSL Hmem Hgh AI0"] Lemma ract_span_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 ->
mem_inv rsegs m ->
let sc' := m_sizeclass mr in
let cnt := ai0 + 2 in
let size := size_class sc' * UNIT in
let span := UNIT + size * cnt in
let cnt1 := span_loop 300 cnt span size in
let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
evt rsegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xceac8) fc None m' (seg_rom rsegs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcea94) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros ZR GN MW SCR UNK GM AV0 MI sc' cnt size span cnt1 cnt2. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & _ & ML).
pose proof (size_class_range sc' ltac:(lia)) as SZR.
unfold RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES in *.
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
step. if_cases K; zify_cond K.
{ exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
clear K.

rewrite GN, AV0 in CH. cbn [oconc] in CH. fold G in CH.
step.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step. rewrite (unsigned_lit (bv_unsigned w8)) by lia. rewrite L8. fold ai0. step. step. step. step.

assert (W5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
step. rewrite ?(unsigned_lit (meta_word mr)) by lia. step. rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 mr MW). fold sc'.
step.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ =>
pose proof (rsize_classes_read mc sc' HI ltac:(lia)) as SCRD; unfold RSIZE_CLASSES in SCRD end.
step. rewrite zx16_wz by lia. clear SCRD.
fold cnt.
assert (SZB : 16 <= size <= 849368) by (unfold size, UNIT; lia).
assert (CNB : 2 <= cnt <= 33) by (unfold cnt; lia).
assert (PR : 0 <= cnt * size <= 33 * 849368) by nia.
assert (EX : span_exit 300 span size = true) by (unfold span, size, cnt, UNIT; apply span_exit_ok; lia).
assert (SPB : span = cnt * size + 16) by (unfold span, UNIT; lia).
assert (Esz : size = size_class sc' * 16) by reflexivity. assert (Ecnt : cnt = ai0 + 2) by reflexivity.
pose proof (span_loop_bounds 300 cnt span size) as CB. fold cnt1 in CB. change (Z.of_nat 300) with 300 in CB.
assert (Ec2 : cnt2 = (if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1)) by reflexivity.
assert (Ec1 : cnt1 = span_loop 300 cnt span size) by reflexivity.
clearbody size cnt span cnt1 cnt2.

step. step. rewrite (unsigned_lit ai0), Z.shiftl_mul_pow2 by lia. step.
step. rewrite (wz_unsigned (size_class sc')), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite <- Esz.

step. rewrite ?(unsigned_lit (ai0 * 16 + 48)), ?(wz_unsigned (size_class sc')) by lia.
replace ((ai0 * 16 + 48) * size_class sc') with (span + size - 16) by (rewrite SPB, Esz, Ecnt; lia).
step. rewrite ?(unsigned_lit size), ?(unsigned_lit cnt) by lia. replace (size * cnt) with (cnt * size) by lia.
step. rewrite ?(unsigned_lit (span + size - 16)) by lia. rewrite swrap_word, sxv_small by lia.
replace (span + size - 16 + 15) with (span + size - 1) by lia.
step. rewrite ?(unsigned_lit (cnt * size)) by lia. rewrite swrap_word, sxv_small by lia. rewrite <- SPB.
step.

eapply evt_cut.
{ change (Z_to_bv 64 (ai0 + 1)) with (wz (ai0 + 1)). change (Z_to_bv 64 size) with (wz size).
eapply (rspan_loop_walk size ltac:(lia) 300 (ai0 + 1) span); try assumption; try (change (Z.of_nat 300) with 300; lia). }
intros ms' (t0' & t1' & a6' & ->). replace (ai0 + 1 + 1) with cnt by lia. rewrite <- Ec1.

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
step.

step. if_cases K; zify_cond K; rewrite ?(wz_unsigned cnt1), ?unsigned_lit in K by lia.
- replace (wz cnt1) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [lia| reflexivity]).
assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
-
step.
replace (Z_to_bv 64 (m_last_idx mr + 1)) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [reflexivity| f_equal; lia]).
assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
Qed.
End ACT.

End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq1.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qv4L Qv4L.Mqb QnkH QnkH.Mqm QmBS.Mq6 Qlfl.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AG1.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

#[using="SC"] Lemma rag_entry_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (rt1_regs sc (Z_to_bv 64 0xd125c) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sc * 2))
(wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1244) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI. unfold rt1_regs, ralloc_meta_entry, RSIZE_CLASSES, RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (size_class_range sc SC) as SZR.
step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
pose proof (rsize_classes_read m sc MI SC) as SCRD. unfold RSIZE_CLASSES in SCRD.
replace (159656 + 2 * sc) with (159656 + sc * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.
step. apply evt_done. reflexivity.
Qed.
End AG1.

#[using="Type"] Lemma rag_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
0 <= gm < 2^64 -> mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if gm =? 0 then 0xd18c4 else 0xd1268)) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd125c) fc None m (seg_rom usegs)).
Proof.
intros until gm. intros GR MI.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
- subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
- replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.

Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

#[using="SZC CR SMALL"] Lemma rstc_q_eq : j = stc_q (szc * cnt).
Proof.
unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.

#[using="SZC CR SMALL"] Lemma rnest_call_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv usegs m ->
evt usegs (fun ms' => exists a2' a3' a4',
ms' = MS (mkR (Z_to_bv 64 0xd1444) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2' a3' a4' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz (szc * 16 * cnt)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1374) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI.
assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
pose proof rstc_q_eq as STC. fold q in STC.
unfold RSIZE_CLASSES, ralloc_slot_entry in *.

assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
evt usegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0xd1444) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 159656) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 856164) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 159656) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1438) fc None m (seg_rom usegs))).
{ intros a0' a2' a3' jv ->.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
step. rewrite Qfw3_c1.Mq2.sextw_small by lia. step. step.
apply evt_done. do 3 eexists. reflexivity. }

step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).

step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
-
apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
-
assert (Q10 : 10 <= q) by (unfold n' in K; nia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].

step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.

step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.

step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.

step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by reflexivity.

step. step. step.
rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.

step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
assert (K13 : 3 <= k <= 12).
{ unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.

step. step. step.
step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (159656 + (i + 1) * 2) with (159656 + 2 * (i + 1)) by lia.
pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
evt usegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0xd1444) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 159656) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 856164) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 159624) (Z_to_bv 64 q) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 159656) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd141c) fc None m (seg_rom usegs))).
{ intros i1 c Hi1 Hc.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (159656 + i1 * 2) with (159656 + 2 * i1) by lia.
pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End STC.

#[using="Type"] Lemma rnest_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
-1 <= idx < 32 -> mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if idx =? -1 then 0xd14bc else 0xd1448)) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1444) fc None m (seg_rom usegs)).
Proof.
intros until idx. intros IR MI.
step. if_cases K; zify_cond K.
- replace (idx =? -1) with true.
2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [exact E|]. exfalso.
change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia. lia. }
apply evt_done. reflexivity.
- replace (idx =? -1) with false.
2:{ symmetry. apply Z.eqb_neq. intros ->. rewrite Z.land_m1_l in K. cbn in K. lia. }
apply evt_done. reflexivity.
Qed.

End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w Q6y7.Mq0 QTyG.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qn9M Qv4L.Mqb QnkH QnkH.Mqm QdZ1.Mq7 QmBS.Mq6 Qlfl.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

#[using="o r N MR UA J HA MSL MW SCg STR SO TK"] Lemma rnenf_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
0 <= c_mmap_counter (ctx st) < 2^32 -> mem_inv usegs m1 ->
evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
ms' = MS (mkR (Z_to_bv 64 0xd1474) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (RSIZE_CLASSES + j * 2)) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 0xd1474) fc None m' (seg_rom usegs)
/\ munch [(P - 3, P)]%Z m1 m' /\ wmono usegs m1 m' /\ mem_inv usegs m'
/\ rmrep (enf0_st st g b idx) m' /\ ticks_ok (enf0_st st g b idx))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 j) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1448) fc None m1 (seg_rom usegs)).
Proof.
intros until fc. intros CTR MI.
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
pose proof (size_class_range j J) as SZR.
assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
destruct (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)
as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND.
pose proof (rmeta_chunk_facts st m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
unfold alloc_ceiling in RC, GC.
set (G := conc st g) in *.
pose proof (GDJ (fst b) r Hr Hk) as GR.
change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
pose proof (bytes_at_read usegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
pose proof (bytes_at_read usegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
pose proof (bytes_at_read usegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
rewrite Z.add_0_r in RD4.
replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
pose proof MW as (LI0 & FB0 & SCR0 & ML0).
pose proof MR as (WF' & CX & GL & _). destruct CX as (CH & _). unfold ctx_head_cells in CH.
unfold RSIZE_CLASSES, RMLOCK, RCTX in *.

step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step.

pose proof (rsize_classes_read m1 j MI J) as SCRD. unfold RSIZE_CLASSES in SCRD.
replace (159656 + 2 * j) with (159656 + j * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.

pose proof (rmrep_active_read st m1 j (wa (6576296 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
replace (wa (6576296 + 80 + 8 * j)) with (Z_to_bv 64 (6576288 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.

step. rewrite sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
step.

step.
eapply evt_mono.
{ eapply (renframe_walk (Z_to_bv 64 0xd1474) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
(pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
| |- mem_inv _ _ => exact MI
| |- wr_at _ _ _ _ => exact WRs
| |- ov_read_bytes _ _ _ 2 = _ => exact RD2
| |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
| |- ov_read_bytes _ _ _ _ = _ => exact RD3
| |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
| |- _ => idtac end.
all: try (rewrite (unsigned_lit G) by lia).
all: try lia.
- subst stride. unfold get_stride, UNIT. reflexivity.
- intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
- exact (so_maplen _ _ _ _ _ _ SO). }

intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
assert (OFF0 : 0 <= off0 < 256).
{ subst off0. destruct (bv_unsigned x3 =? 0).
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
replace (fold_off off0 0) with 0 in EM |- * by lia.
rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
replace (ret_pc (Z_to_bv 64 0xd1474)) with (Z_to_bv 64 0xd1474) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

assert (S31n : stride - 4 - N < 2^31) by lia.
assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
destruct (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)
as (MRr & TKr & CONCr & FSTr & SNDr). clear T1 T3 T0 TN T4.
rewrite Z.mul_0_r, Z.add_0_r in MRr.
change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
fold P in MRr, EM. rewrite <- EM in MRr.
destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.

assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
{ rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
assert (MU : munch [(P - 3, P)]%Z m1 m').
{ rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [| lia| cbn; lia| cbn; lia].
apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
assert (WM : wmono usegs m1 m').
{ rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
do 14 eexists. exists m'.
split; [unfold P, G; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
#[using="st g b idx j mr stride B P N"] Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.

#[using="m1 r j N MR J SO TK"] Lemma renfD_walk :
forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mt : aptr) (cnt : Z) mC,
meta_slot st mt -> mw_ok (get_meta_rec st mt) -> 1 <= cnt <= 32 ->
rmrep (enf0_st st g b idx) mC -> ticks_ok (enf0_st st g b idx) -> mem_inv usegs mC ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (P + 12)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd149c) fc None m' (seg_rom usegs)
/\ munch [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC m' /\ wmono usegs mC m' /\ mem_inv usegs m'
/\ rmrep (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
(put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))) m'
/\ ticks_ok (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
(put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1474) fc None mC (seg_rom usegs)).
Proof.
intros until mC. intros MST MWT CR MRC TKC MIC.
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
set (st0' := enf0_st st g b idx) in *.
assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
pose proof (rmeta_slot_bounds st0' mC mt MRC MST0) as (Tpos & TC & TI & _ & _).
change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
pose proof (rmeta_chunk_facts st0' mC mt MRC MST0) as (_ & _ & _ & _ & _ & GDJ & _).
assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl usegs mC) as WM.
pose proof MWT as (LI0 & FB0 & SCR0 & ML0). pose proof (meta_word_range _ MWT) as MWR.
unfold alloc_ceiling in TC.

rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
rmeta_open (conc st mt) MUt WMt.
step.

step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
set (w := meta_word (get_meta_rec st mt)) in *.
rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
rewrite (meta_word_mod4096 st g b idx j _ MWT).
step.
lazymatch goal with H : rw_cells usegs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
[ eapply rmrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
| clear MUt WMt H ] end.
set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).

pose proof (land31_range idx) as L31.
assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
{ change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
[| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
by (unfold wa; f_equal; unfold P; lia).
step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).

step. rewrite (unsigned_lit cnt), swrap32_small by lia.
step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.

pose proof MR5 as (_ & _ & _ & _ & _ & SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
pose proof (wr_at_store_ok usegs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
by (unfold wa; f_equal; unfold P; lia).
st1.
assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
rewrite <- (lor_192 (Z.land idx 31)) by lia.
rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.

step. rewrite ?(unsigned_lit P) by (unfold P; lia).
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.

#[using="m1 r j N MR STR SO"] Lemma rzero_loop_walk : forall k (i szc cnt : Z) stz mC0 mC
(ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
Z.of_nat k = cnt + 1 - i -> 0 <= i <= cnt -> 1 <= szc -> 0 <= cnt < 4096 -> 16 + 16 * szc * cnt <= stride ->
s_regions stz = s_regions st -> s_groups stz = s_groups st ->
rmrep stz mC -> ticks_ok stz -> mem_inv usegs mC ->
munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 mC -> wmono usegs mC0 mC ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (cnt - 1)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd176c) fc None m' (seg_rom usegs)
/\ munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 m' /\ wmono usegs mC0 m' /\ mem_inv usegs m'
/\ rmrep (zero_hdrs (pp st g b idx) (16 * szc) i k stz) m' /\ ticks_ok (zero_hdrs (pp st g b idx) (16 * szc) i k stz)
/\ s_regions (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_regions st /\ s_groups (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_groups st
/\ (forall x, (forall j, i <= j <= cnt -> bv_unsigned x <> P + 12 + 16 * szc * j) -> m' x = mC x))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt + 1 - i)) (Z_to_bv 64 (P + 12 + 16 * szc * i)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd149c) fc None mC (seg_rom usegs)).
Proof.
induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
{ exfalso. lia. }
pose proof (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).

assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
pose proof MRz as (WFz & _ & _ & _ & _ & SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
pose proof (wr_at_store_ok usegs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
by (unfold wa; f_equal; unfold P; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
specialize (MR2 Hr' Hk ltac:(lia)).
assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
{ intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & _ & GWF).
destruct (GWF b0 gh Hb0) as (r0 & _ & _ & _ & _ & M16).
destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).

pose proof STR as STRdep__.
clear - CONTRA E0 E1 E2.
replace (stride * idx) with (16 * (stride / 16) * idx) in CONTRA by (rewrite <- E2; reflexivity).
lia. }
specialize (MR2 NOG ltac:(lia)). clear NOG.
replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
[ intros u Hu Hux;
rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
exfalso; lia
| apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
apply (wmono_write usegs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
lazymatch goal with HI : mem_inv usegs mX |- _ =>
apply (mem_inv_store usegs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
[| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
end;
clear SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
end.

step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
step. rewrite ?unsigned_lit by lia.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
eapply evt_mono.
{ (eapply (IH (i + 1) szc cnt);
[ lia | lia | exact SZC | exact CNT | exact FIT
| rewrite s_regions_wr8; exact RGz
| rewrite s_groups_wr8; exact GRz
| exact MR2
| apply ticks_ok_wr8; exact TKz
| assumption | exact MU | exact WM ]). }
cbv beta. intros ms' (m' & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & PW).
eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
split; [exact X6|]. split; [exact X7|].
intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
-
assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].

step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
apply evt_done. eexists. split; [reflexivity|].
cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.

End RC__1.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w Q9Ay.Mq3 QTyG.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qv4L.Mqb QnkH QnkH.Mqm QdZ1.Mq7 QmBS.Mq6 Qlfl.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof.
intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.

#[using="Type"] Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
rewrite (mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal.
Qed.

#[using="Type"] Lemma unsigned_mod32_add_not a b : 0 <= b < 2^64 ->
(bv_unsigned (wz (sxv a)) + Z.lxor b 18446744073709551615) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
intros Hb. rewrite zb_lxor_ones by lia. rewrite (wz_unsigned (sxv a)) by (apply sxv_range).
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l.
replace (a + (18446744073709551615 - b)) with ((a - 1 - b) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
#[using="Type"] Lemma unsigned_mod32_swrap_add_not a b :
bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
pose proof (sxv_range b) as RB.
rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia.
unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
clearbody x y. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof.
intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
rewrite <- !Z.land_assoc. reflexivity.
Qed.

Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
(r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

Definition rtailW : list (Z * Z) :=
[(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z.

#[using="r AV FR SC CNT AI ML MST REC Hr Hk P0 P16 PEND GNONE NOGRP OLD12 UR ACT TK"] Lemma rtail_walk :
forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
rmrep stT mC -> mem_inv usegs mC ->
evt usegs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd18c4) fc None m' (seg_rom usegs)
/\ munch rtailW mC m' /\ wmono usegs mC m' /\ mem_inv usegs m'
/\ rmrep (stFin stT sc cnt ai ml mt p) m' /\ ticks_ok (stFin stT sc cnt ai ml mt p))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd176c) fc None mC (seg_rom usegs)).
Proof.
intros until mC. intros MR MI.
pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl usegs mC) as WM. unfold rtailW in MU.
pose proof (rmeta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
pose proof (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
pose proof (AV_FR_range stT cnt ai mt p CNT AI P0) as (AVR & FRR & AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.

destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
unfold RCTX, RMLOCK, alloc_ceiling in *.

pose proof (rmrep_usage_read (stA stT p) mC sc (wa (6576296 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
change (usage (stA stT p) sc) with (usage stT sc) in RDU.
replace (wa (6576296 + 464 + 8 * sc)) with (Z_to_bv 64 (6576288 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
step. clear RDU.

step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.

pose proof MRA as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok usegs _ _ (usages (stA stT p)) sc (wa (6576296 + 464 + 8 * sc)) USG
ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
replace (wa (6576296 + 464 + 8 * sc)) with (Z_to_bv 64 (6576288 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
rraw_store_finish0 (6576296 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear MRA TKA.

step. rewrite ?(unsigned_lit ai) by lia. rewrite QTyG.sllw2_word by lia.
step.
set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
rmeta_open G MUa WMa.

step. step.
assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
{ subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
rewrite (sx32_congr v3 AV V3).

step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite QTyG.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
step. step.
set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
{ subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }

step. step.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
| clear MUa WMa; rename H into CH1 ] end.
assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear MRB TKB MSTB.

pose proof MRC as (WFC & _ & _ & _ & _ & SHC). pose proof WFC as (_ & _ & DJ & _ & WG).
destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
destruct (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) as (hb & LHB & HB) end.
destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HDR : rw_cells usegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
[ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
| clear HB LHB ] end.
pose proof (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _).
pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl usegs mX) as WMb end.

step.

step.
pose proof (byte_range y8) as Y8.
step. unfold zxb.

step. rewrite ?(unsigned_lit ai) by lia.
replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
step.
pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
rewrite (land224_m32 (bv_unsigned y8)) by lia.
pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].

set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.

lazymatch goal with H : rw_cells usegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
rename H into HDR2;
assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
| assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
[ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
| rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
| ] ] end.
{
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
- unfold RCTX in X1. lia.
- unfold RMLOCK in X2. lia.
- unfold RNEED_LOCKS in X3. lia.
- unfold RPAGE_SIZE in X4. lia.
- change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
destruct (rarea_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
- change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
destruct (rgroup_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
+ rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
+ pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
- change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
destruct (N.eq_dec q (fst p)) as [->|NE].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
- unfold RGOT_SSP in X5. lia.
- unfold RSSP_GUARD in X6. lia. }
clear MRC MRC2 MUb WMb HDR2.
assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear TKC MSTC.

pose proof MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
rmchunk MRD MSTD CH.
change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
rmeta_open G MUc WMc.

step. step. step. step. step.
rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
rewrite (unsigned_lit W), EW, land_pg_mask by lia.

step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
step. rewrite ?unsigned_lit by lia.

step. step. step. step.
rewrite ?(unsigned_lit (mask_upto ai)) by lia.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

lazymatch goal with H : u64arr usegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_read usegs mX (6576296 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (6576296 + 80 + 8 * sc)) H
(actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
replace (wa (6576296 + 80 + 8 * sc)) with (Z_to_bv 64 (6576376 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step. step. step.

lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]
| clear MUc WMc; rename H into CH3 ] end.
{ unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
unfold wz. rewrite !app_nil_r.
rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
fold AV. Z.div_mod_to_equations. lia. }
do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
{ reflexivity. }
{ cbn. tauto. }
assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
clear MRD TKD MSTD.

clear CH3.
lazymatch goal with H : u64arr usegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_store_ok usegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (6576296 + 80 + 8 * sc)) H
ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
replace (wa (6576296 + 80 + 8 * sc)) with (Z_to_bv 64 (6576376 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
st1.
replace (Z_to_bv 64 (6576376 + 8 * sc + 0)) with (Z_to_bv 64 (6576376 + 8 * sc)) in SOK by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
rraw_store_finish0 (6576296 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.

step.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact MRF| exact TKE].
Qed.
End TAIL.

End RC__1.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4 QDUx.Mq7.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w Q9Ay.Mq1.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qv4L.Mqb QnkH QnkH.Mqm QdZ1.Mq7 QmBS.Mq6 Qlfl.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition rseqW : list (Z * Z) := [(RCTX + 848, RCTX + 913)]%Z.

#[using="SC"] Lemma rbounce_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
mem_inv usegs m ->
evt usegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd15e4) fc None m' (seg_rom usegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch rseqW m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1330) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MR SEQ BR USR MI.
pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl usegs m) as WM. unfold rseqW in MU.
unfold RCTX, RMLOCK in *.

assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
rmrep stX mX -> stX = account_bounce sc st -> mem_inv usegs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
munch [(6576296 + 848, 6576296 + 913)]%Z m mX -> wmono usegs m mX ->
evt usegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 6576288) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd15e4) fc None m' (seg_rom usegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch [(6576296 + 848, 6576296 + 913)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 6576288) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd15e0) fc None mX (seg_rom usegs))).
{ intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
pose proof (rmrep_seq_read stX mX (wa (6576296 + 912)) MRX eq_refl) as RDS.
replace (wa (6576296 + 912)) with (Z_to_bv 64 (6576288 + 920)) in RDS by (unfold wa; f_equal; lia).
assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
{ rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite SQX in RDS.
step. rewrite ?zxb_b8 by lia. clear RDS.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }

step. rewrite ?(unsigned_lit sc) by lia. step.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{
assert (HO : sc_in_seq_range sc = false).
{ unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
- replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
step. step.
eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
- unfold account_bounce. rewrite HO. reflexivity.
- unfold is_bouncing. rewrite HO. reflexivity. }
rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
destruct (Z.lt_ge_cases sc 7) as [L7|G7].
{ exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
rewrite Z.mod_small in K by lia.
assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).

step. rewrite ?(unsigned_lit (sc + -7)) by lia.
pose proof (rmrep_bounces_read st m (sc - 7) (wa (6576296 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
replace (wa (6576296 + 880 + (sc - 7))) with (Z_to_bv 64 (6576288 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
step. rewrite ?zxb_b8 by lia. clear RDB.
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_read usegs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (6576288 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
ltac:(unfold wa, RCTX; f_equal; lia)) as RDU. clear US.
step. rewrite ?zxb_b8 by lia. clear RDU.

step. step.
set (nos := 100 <=? bounces st (sc - 7)).
assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
{ rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
change (bv_wrap 64 100) with 100.
destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
rewrite A3. clear A3.
assert (AB : account_bounce sc st =
(if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
else st)) by (unfold account_bounce; rewrite IN; reflexivity).

step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
{ eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }

pose proof (rmrep_seq_read st m (wa (6576296 + 912)) MR eq_refl) as RDS.
replace (wa (6576296 + 912)) with (Z_to_bv 64 (6576288 + 920)) in RDS by (unfold wa; f_equal; lia).
step. rewrite ?zxb_b8 by lia. clear RDS.
step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
{
apply Z.ltb_lt in K2.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite Bool.andb_false_r. exact MR. }
apply Z.ltb_ge in K2.
assert (AB2 : account_bounce sc st =
(if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
{ rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
clear AB K1 K2.
pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _).
pose proof (u8arr_store_ok usegs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (6576288 + (sc + -7) + 888)) BA
ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear BA.

step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
-
step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6576296 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. step. st1. rewrite (le1_lit 150) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6576296 + 880 + (sc - 7)) [b8 150] MU WM SOK.
eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="Type"] Lemma rseq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m0 m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> mem_inv usegs m ->
munch rseqW m0 m -> wmono usegs m0 m ->
evt usegs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1610) fc None m' (seg_rom usegs)
/\ munch rseqW m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ rmrep (step_seq st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 (wz (c_seq (ctx st))) a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd15e4) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
set (q := c_seq (ctx st)) in *.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6 & _) & _).
unfold RCTX, RMLOCK in *. unfold ctx_tail_cells in C6.
replace (6576296 + 912) with 6577208 in C6 by reflexivity. replace (6576296 + 848) with 6577144 in US by reflexivity.

assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv usegs mj ->
munch [(6576296 + 848, 6576296 + 913)]%Z m0 mj -> wmono usegs m0 mj ->
evt usegs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 6576288) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1610) fc None m' (seg_rom usegs)
/\ munch [(6576296 + 848, 6576296 + 913)]%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 6576288) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1608) fc None mj (seg_rom usegs))).
{ intros mj stj ns NS MRj CTj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j & _) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
replace (6576296 + 912) with 6577208 in C6j by reflexivity.
pose proof (rw_cells_store_ok_at usegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (6576288 + 920)) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.

step. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
rraw_store_finish0 (6576296 + 912) [b8 ns] MUj WMj SOK.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }

step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned q) by lia.
eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
-
pose proof (rw_cells_of_u8arr usegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
pose proof (munch_refl [(6576296 + 848, 6576296 + 880)]%Z m) as MUz. pose proof (wmono_refl usegs m) as WMz.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UZ : u8arr usegs mX 6577144 (zeros 32));
[ apply (u8arr_of_rw_cells usegs mX 6577144 32);
lazymatch goal with H : rw_cells usegs mX 6577144 _ |- _ =>
apply (rw_cells_congr usegs mX 6577144 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
pose proof MR as (_ & (_ & _ & _ & _ & _ & C6 & _) & _). unfold ctx_tail_cells, RCTX in C6.
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono usegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRz : rmrep stz mX);
[ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia];
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
| clear MUc WMc ] end.

step. step.
lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono usegs m0 ?mX, MIc : mem_inv usegs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed.

#[using="SC"] Lemma rmm_seq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
mem_inv usegs m ->
evt usegs (fun ms' => exists (t0' t1' a3' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 (Z_to_bv 64 31) a6' a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1610) fc None m' (seg_rom usegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch rseqW m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (step_seq (account_bounce sc st)) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1330) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MR SEQ BR USR MI.
eapply evt_cut; [eapply rbounce_walk; eassumption|].
cbv beta. intros ms' (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR').
assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
{ unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite <- SEQ'.
eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
cbv beta. intros ms'' (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'').
do 6 eexists. split; [reflexivity|]. subst a3'.
repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.

End RC__1.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq0 Q9Ay.Mq1 Q9Ay.Mq2.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qv4L.Mqb QnkH QnkH.Mqm QmBS.Mq6 Qlfl Qlfl.Mq6.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

Definition rmmc_post (ra sp gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(res : Z * Z) : machine_state -> Prop :=
fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (wz (snd res)) s4 s5 s6 s7 s8 (wz (fst res)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd16f4) fc None m (seg_rom usegs).

#[using="SZ RQ"] Lemma rj2c_walk :
forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc m (c1 u1 : Z),
1 <= c1 <= 32 -> 0 <= u1 < 2^61 ->
evt usegs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 s6 s7 (wz size) s10 s11 t3 t4 t5 t6 F fc m
(mm_final size req u1 c1 nos))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) a4 a5 a6 a7
(Z_to_bv 64 req) s3 s4 s5 s6 s7 (wz size) (wz c1) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1698) fc None m (seg_rom usegs)).
Proof.
intros until u1. intros CR UR.
assert (SCR : 16 <= size * c1 < 2^24) by nia.
pose proof (zb_b2z_range nos) as NR.
unfold rmmc_post.

step. rewrite (wz_unsigned size), (wz_unsigned c1) by lia.
step. step. step. step. step. step.
rewrite !land_4095_word. rewrite ?(unsigned_lit (size * c1)) by lia.
replace (-16 + - (size * c1)) with (- (size * c1 + 16)) by lia.
set (nd0 := round_up_pg (size * c1 + 16)).
pose proof (round_up_pg_alt (size * c1 + 16)) as RU. pose proof (round_up_pg_range (size * c1 + 16) ltac:(lia)) as RUR.
replace (size * c1 + Z.land (- (size * c1 + 16)) 4095 + 16) with nd0 by lia.
fold nd0 in RUR.
assert (EF : mm_final size req u1 c1 nos = (if negb nos && (c1 <=? 7) then mm_small size req u1 c1 nd0 else (c1, nd0))).
{ unfold mm_final, UNIT. reflexivity. }

step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
{
apply evt_done. rewrite EF. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]). cbn [negb andb fst snd].
do 9 eexists. reflexivity. }
replace nos with false in EF |- * by (destruct nos; cbn in KN; [lia| reflexivity]). cbn [negb andb] in EF.

step. step. if_cases K7; zify_cond K7; rewrite ?(wz_unsigned c1), ?unsigned_lit in K7 by lia.
{
apply evt_done. rewrite EF. replace (c1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
do 9 eexists. reflexivity. }
replace (c1 <=? 7) with true in EF by (symmetry; apply Z.leb_le; lia).

step. step. step. step. step.
rewrite (Z.land_comm 4095), land_4095_word. rewrite ?(unsigned_lit req) by lia.
replace (-20 + - req) with (- (req + 20)) by lia.
set (rq' := round_up_pg (req + 20)).
pose proof (round_up_pg_alt (req + 20)) as RU2. pose proof (round_up_pg_range (req + 20) ltac:(lia)) as RUR2.
replace (req + Z.land (- (req + 20)) 4095 + 20) with rq' by lia. fold rq' in RUR2.
assert (ES : mm_small size req u1 c1 nd0 = (if (rq' <? size + 16) || ((4 * PGSZ <=? rq') && (u1 <? 2 * c1)) then (1, rq') else (c1, nd0))).
{ unfold mm_small, IB, UNIT. replace (req + 4 + 16) with (req + 20) by lia. reflexivity. }
rewrite ES in EF. clear ES. unfold PGSZ in EF.

step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (size + 16)), ?unsigned_lit in K1 by lia.
-
replace (rq' <? size + 16) with false in EF by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in EF.
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
+
apply evt_done. rewrite EF. replace (4 * 4096 <=? rq') with false by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd].
do 9 eexists. reflexivity.
+ replace (4 * 4096 <=? rq') with true in EF by (symmetry; apply Z.leb_le; lia). cbn [andb] in EF.

step. rewrite (wz_unsigned c1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite swrap32_small by lia.
step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned u1), ?unsigned_lit in K3 by lia.
*
step. step. step.
apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
do 9 eexists. reflexivity.
* apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
do 9 eexists. reflexivity.
-
replace (rq' <? size + 16) with true in EF by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in EF.
step. step. step.
apply evt_done. rewrite EF. cbn [fst snd]. do 9 eexists. reflexivity.
Qed.

#[using="SC SZ"] Lemma rred_walk :
forall (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (cnt u1 : Z),
1 <= cnt <= 32 -> 0 <= u1 < 2^61 ->
evt usegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1698) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5 a6 a7
(Z_to_bv 64 req) (wz cnt) s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1624) fc None m (seg_rom usegs)).
Proof.
intros until u1. intros CR UR.
assert (SCR : 16 <= size * cnt < 2^24) by nia.
pose proof (zb_b2z_range nos) as NR. pose proof (Q9Ay.Mq2.land3_range sc) as L3.

assert (J28 : forall (a5' a6' a7' t0' s9' : word) (c : Z), c = mm_cnt_red sc size cnt u1 nos ->
evt usegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1698) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
(Z_to_bv 64 req) (wz c) s4 s5 s6 s7 (wz size) s9' s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1694) fc None m (seg_rom usegs))).
{ intros a5' a6' a7' t0' s9' c ->. step. apply evt_done. do 5 eexists. reflexivity. }

step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2, swrap32_small by lia. change (2 ^ 2) with 4.
step. if_cases KU; zify_cond KU; rewrite ?(wz_unsigned u1), ?unsigned_lit in KU by lia.
{ eapply J28. unfold mm_cnt_red. replace (u1 <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }

step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
{ eapply J28. unfold mm_cnt_red. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]).
rewrite Bool.andb_false_r. reflexivity. }
assert (EN : nos = false) by (destruct nos; cbn in KN; [lia| reflexivity]).
assert (ER : mm_cnt_red sc size cnt u1 nos =
(if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt)).
{ unfold mm_cnt_red. rewrite EN. replace (u1 <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
unfold PGSZ in ER.

step. rewrite ?(unsigned_lit sc) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 3) with 32768.
step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
-
replace (Z.land sc 3 =? 1) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
+
replace (Z.land sc 3 =? 2) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.

step. step. step.
step. if_cases KC; zify_cond KC.
*
rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
destruct (Z.ltb_spec (Z.land sc 3) 1) as [A1|A1]; destruct (Z.ltb_spec 32768 (size * cnt)) as [LT|GE]; cbn [Z.b2z Z.land] in KC; try (exfalso; apply KC; reflexivity); [].
assert (E0 : Z.land sc 3 = 0) by lia.
step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [exfalso; lia|].
step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [| exfalso; lia].
apply evt_done. rewrite ER, E0. cbn [Z.eqb andb]. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
*
assert (NC : ~ (Z.land sc 3 = 0 /\ 32768 < size * cnt)).
{ intros [E0 LT]. rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
replace (Z.land sc 3 <? 1) with true in KC by (symmetry; apply Z.ltb_lt; lia).
replace (32768 <? size * cnt) with true in KC by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z true)) with 1 in KC. lia. }
clear KC. step. step.
step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
{
apply evt_done. rewrite ER. replace (Z.land sc 3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
do 5 eexists. reflexivity. }
rewrite KD in ER |- *. cbn [Z.eqb andb] in ER.
replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia).

step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [exfalso; lia|].
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 1) with 8192.
step. if_cases KQ; zify_cond KQ; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KQ by lia.
-- eapply J28. rewrite ER. replace (2 * 4096 <? size * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
-- step. eapply (J28 _ _ _ _ _ 5). rewrite ER. replace (2 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+
rewrite KB in ER |- *. cbn [Z.eqb andb] in ER.
step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
*
replace (4 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
step. step. step.
step. if_cases KG; zify_cond KG.
{ exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
apply evt_done. rewrite ER. do 5 eexists. reflexivity.
*
step. step. apply evt_done. rewrite ER. replace (4 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
-
rewrite KA in ER |- *. cbn [Z.eqb andb] in ER.
step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
+
replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
step. step. step.
step. if_cases KG; zify_cond KG.
{ exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
apply evt_done. rewrite ER. do 5 eexists. reflexivity.
+
step. step. apply evt_done. rewrite ER. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
do 5 eexists. reflexivity.
Qed.

#[using="SC"] Lemma rusage1_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (u0 : Z),
rmrep st m -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
evt usegs (fun ms' => exists (a5' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz (mm_usage1 st sc u0)) a1 a2 a3 a4 a5' a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1624) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) a1 a2 a3 a4 (Z_to_bv 64 31) a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1610) fc None m (seg_rom usegs)).
Proof.
intros until u0. intros MR UR USR. unfold RMLOCK, RCTX in *.
pose proof (land_upper sc 1 ltac:(lia) ltac:(lia)) as L1R.

step. if_cases K; unfold bv_lts in K; rewrite !signed_lit_small in K by lia.
{ apply Z.ltb_lt in K. apply evt_done. unfold mm_usage1. replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
eexists. reflexivity. }
apply Z.ltb_ge in K.

step. rewrite ?(unsigned_lit sc) by lia.
step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit (Z.land sc 1)) in KO by lia.
{
assert (ODD : Z.even sc = false).
{ rewrite even_of_land1. apply Z.eqb_neq. exact KO. }
apply evt_done. unfold mm_usage1. rewrite ODD. cbn [andb]. eexists. reflexivity. }
assert (EV : Z.even sc = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact KO).

pose proof (rmrep_usage_read st m (sc + 1) (wa (6576296 + 464 + 8 * (sc + 1))) MR ltac:(lia) eq_refl) as RDU.
replace (wa (6576296 + 464 + 8 * (sc + 1))) with (Z_to_bv 64 (6576288 + 8 * sc + 480)) in RDU by (unfold wa; f_equal; lia).
pose proof (USR (sc + 1)) as U1R.
step. clear RDU. step. rewrite (wz_unsigned (usage st (sc + 1))), (wz_unsigned u0) by lia.
apply evt_done. unfold mm_usage1. rewrite EV. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
eexists. unfold wz. rewrite (Z.add_comm (usage st (sc + 1)) u0). reflexivity.
Qed.

#[using="SC SZ RQ"] Lemma rmmc_walk :
forall (ra sp gp tp t0 t1 t2 s1 a6 a7 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (cnt u0 : Z),
rmrep st m -> 1 <= cnt <= 32 -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
evt usegs (rmmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (wz size) s10 s11 t3 t4 t5 t6 F fc m
(mm_final size req (mm_usage1 st sc u0) (mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos) nos))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) (Z_to_bv 64 31) a6 a7
(Z_to_bv 64 req) (wz cnt) s4 s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (wz size) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1610) fc None m (seg_rom usegs)).
Proof.
intros until u0. intros MR CR UR USR.
assert (U1R : 0 <= mm_usage1 st sc u0 < 2^61).
{ unfold mm_usage1. pose proof (USR (sc + 1)). destruct (_ && _); lia. }
eapply evt_cut. { eapply (rusage1_walk _ _ _ _ t0 t1 t2 s1); [exact MR| exact UR| exact USR]. }
cbv beta. intros ms' (a5' & ->).
eapply evt_cut. { eapply (rred_walk _ _ _ _ t0 t1 t2 s1); [exact CR| exact U1R]. }
cbv beta. intros ms'' (a5'' & a6'' & a7'' & t0'' & s3'' & ->).
assert (CRR : 1 <= mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos <= 32).
{ unfold mm_cnt_red. destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia. }
eapply evt_mono. { eapply rj2c_walk; [exact CRR| exact U1R]. }
cbv beta. unfold rmmc_post. intros ms3 (t0x & a0' & a1' & a2' & a3' & a4' & a5x & a6x & a7x & ->).
do 9 eexists. reflexivity.
Qed.
End MMC.

End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq2.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QnOf QdZ1 Qv4L.Mqk QQbX Qn9M Qv4L.Mqb QnkH QnkH.Mqm QdZ1.Mq7 QnkH.Mqh QmBS.Mq6 Qlfl.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmm_call_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
evt usegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 0xd1714) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) s3 (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd16f4) fc None m (seg_rom usegs)).
Proof.
intros. unfold rmmap_entry.
step. step. step. step. step. step. step. step.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma rmm_ret_fail_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
evt usegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd183c) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1714) fc None m (seg_rom usegs)).
Proof.
intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
apply evt_done. reflexivity.
Qed.

Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

#[using="SC CNT SZ ND NDA XA XA2 MST REC HC CR"] Lemma rmm_ret_ok_walk :
forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) F fc m,
rmrep st2 m -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd176c) fc None m' (seg_rom usegs)
/\ munch [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1714) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MR MI.
pose proof (munch_refl [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold alloc_ceiling, RCTX, RMLOCK in *.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
clear K.

step.
rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
rmeta_open G MUa WMa.
step.

step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
rewrite (divu_word 4080 size) by lia.
pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
set (d := 4080 / size) in *.

pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. rewrite HC in CX1. unfold RCTX in CX1.
step. rewrite (sx32_wz_sxv c) by lia.

step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).

assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
{ unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia. }
step.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
[ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
| clear MUa WMa H ] end.
set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.

pose proof (rw_cells_store_ok_at usegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (6576288 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
clear CX1.
st1.
rewrite le4_swrap_succ by lia.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold RCTX in MR4 end.
clear MR3.
rraw_store_finish0 (6576296 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
{ unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
rewrite <- E4 in MR4.
assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).

step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
evt usegs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 6576288) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd176c) fc None m' (seg_rom usegs)
/\ munch [(G, G + 40); (6576296 + 12, 6576296 + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 6576288) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1758) fc None mX (seg_rom usegs))) end.
{ intros a2v mn Hmn ->.
assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).

step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
replace (cnt + -1) with (cnt - 1) by lia.
assert (AI : mm_ai cnt size = (if mn =? 0 then 0 else mn - 1)).
{ unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
destruct (Z.ltb_spec cnt d) as [LT|GE].
- replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
- replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eqb_spec d 0) as [E0|NE0].
+ rewrite E0. reflexivity.
+ replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
= Z_to_bv 64 (mm_ai cnt size)).
{ rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
destruct (Z.eqb_spec mn 0) as [E0|NE0].
- rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
- rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
rewrite EA2.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR4| exact C4']. }
if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
-
eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End MMOK.

End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QTyG.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qv4L.Mqb QnkH QnkH.Mqm QdZ1.Mq7 QmBS.Mq6 Qlfl.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_set_free_head : forall st m v,
rmrep st m ->
rmrep (upd_ctx (set_free_meta_head v) st) (write_to_mem m (wa (RCTX + 16)) (le8 (pw st v))).
Proof.
intros st m v MR. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6 & X7) & _).
pose proof (length_le8 (pw st v)) as L8.
pose proof (munch_write [(RCTX + 16, RCTX + 24)] m m (RCTX + 16) (le8 (pw st v)) (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
pose proof (wmono_write usegs m m (wa (RCTX + 16)) (le8 (pw st v)) (wmono_refl usegs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia.
- left.
pose proof (rw_cells_write usegs m RCTX (ctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
cbn [cbytes cell_upd ctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
exact W.
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.

#[using="Type"] Lemma rmrep_extW : forall stX stY m,
rmrep stX m ->
s_regions stY = s_regions stX -> ctx stY = ctx stX -> (forall q, get_meta_rec stY q = get_meta_rec stX q) ->
s_areas stY = s_areas stX -> s_groups stY = s_groups stX -> (forall rid, get_shadow stY rid = get_shadow stX rid) ->
s_reserved stY = s_reserved stX ->
rmrep stY m.
Proof.
intros stX stY m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
- eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.
End RC__1.

Ltac rraw_store_finishF A bs' FR MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write usegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv usegs mX |- _ =>
apply (mem_inv_store usegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.

Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition rfailW (spv : Z) : list (Z * Z) :=
(spv - 144, spv) :: (G, G + 40) :: (RCTX + 16, RCTX + 24)
:: match c_free_meta_head (ctx st) with
| Some h => (conc st h, conc st h + 40)
:: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
| None => []
end.

#[using="MST FL"] Lemma rfailm1_walk :
forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
rmrep st m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
alloc_ceiling <= bv_unsigned sp - 144 ->
evt usegs (fun ms' => exists (a1' s6' : word) m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd18c4) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
/\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (as_fm_st st mt) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd14bc) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros MR MI FR SPC.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold rfailW. unfold RCTX, RMLOCK, alloc_ceiling, rta_frame in *.

assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
evt usegs (fun ms' => exists m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 6576288) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1518) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
/\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (put_meta mt meta0 st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 6576288) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd14bc) fc None m (seg_rom usegs))).
{ intros W HW1 HW2.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
rmchunk MR MST CH. fold G in CH.

lazymatch type of CH with rw_cells usegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
assert (CH' : rw_cells usegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
[ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
| clear CH ] end.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with WMs : wmono usegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.
rmeta_open G MUb WMb.

step. st1. step. st1. step. st1. step. st1. step. st1.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR0 : rmrep (put_meta mt meta0 st) mX);
[ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
| clear H MUb WMb ] end.
lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (FR' : rw_cells usegs mX (bv_unsigned sp + -144)
([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
[ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
| cbn [cells_size csize] in WR |- *; exact WR]
| clear H ] end.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
split; [assumption|]. split; [assumption| exact MR0]. }
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
-
destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (6576296 + 16, 6576296 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).

rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rewrite HP in CH. cbn [oconc] in CH.
step. clear CH.

rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
rmeta_open G MUb WMb.
st1.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
[ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
| clear MUb WMb H ] end.
set (st2 := put_meta mt _ st1) in MR2.
assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).

rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rmeta_open (conc st p) MUc WMc.
st1.
lazymatch goal with H : rw_cells usegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
[ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st2 mt) with G; reflexivity
| clear MUc WMc H ] end.
set (st3 := put_meta p _ st2) in MR3.
assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).

rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
change (conc st mt) with G in CH.
step. clear CH.

rmchunk MR3 MSh3 CH.
rmeta_open (conc st h) MUd WMd.
st1.
lazymatch goal with H : rw_cells usegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
[ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st3 mt) with G; reflexivity
| clear MUd WMd H ] end.

step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
eapply (rmrep_extW _ _ _ MR4); try reflexivity.
intros q. unfold st3, st2, st1, st0, upd_meta.
destruct (decide (q = h)) as [->|NQh].
{ rewrite !get_meta_rec_put_same. f_equal.
destruct (decide (h = p)) as [<-|NHp].
- rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
- rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
destruct (decide (q = p)) as [->|NQp].
{ rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
-
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (6576296 + 16, 6576296 + 24)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1. st1.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.

step.
pose proof MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
pose proof (rw_cells_store_ok_at usegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (6576288 + 24)) CX1 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
rraw_store_finishF (6576296 + 16) (le8 (wz G)) FR1 MU WM1 SOK.

step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_single. cbn [set_head].
eapply (rmrep_extW _ _ _ MR2); try reflexivity.
intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.

#[using="MST FL"] Lemma rfailm2_walk :
forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
rmrep st m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
alloc_ceiling <= bv_unsigned sp - 144 ->
evt usegs (fun ms' => exists (s6' : word) m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd18c4) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -144) (rta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
/\ munch (rfailW (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (as_fm_st st mt) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd183c) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros MR MI FR SPC.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold rfailW. unfold RCTX, RMLOCK, alloc_ceiling, rta_frame in *.

assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
evt usegs (fun ms' => exists m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 6576288) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1894) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
/\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (put_meta mt meta0 st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 6576288) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd183c) fc None m (seg_rom usegs))).
{ intros W HW1 HW2.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
rmchunk MR MST CH. fold G in CH.

lazymatch type of CH with rw_cells usegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
assert (CH' : rw_cells usegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
[ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
| clear CH ] end.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with WMs : wmono usegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.
rmeta_open G MUb WMb.

step. st1. step. st1. step. st1. step. st1. step. st1.

step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR0 : rmrep (put_meta mt meta0 st) mX);
[ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
| clear H MUb WMb ] end.
lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (FR' : rw_cells usegs mX (bv_unsigned sp + -144)
([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
[ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
| cbn [cells_size csize] in WR |- *; exact WR]
| clear H ] end.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
split; [assumption|]. split; [assumption| exact MR0]. }
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
-
destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (6576296 + 16, 6576296 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).

rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rewrite HP in CH. cbn [oconc] in CH.
step. clear CH.

rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
rmeta_open G MUb WMb.
st1.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
[ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
| clear MUb WMb H ] end.
set (st2 := put_meta mt _ st1) in MR2.
assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).

rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rmeta_open (conc st p) MUc WMc.
st1.
lazymatch goal with H : rw_cells usegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
[ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st2 mt) with G; reflexivity
| clear MUc WMc H ] end.
set (st3 := put_meta p _ st2) in MR3.
assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).

rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
change (conc st mt) with G in CH.
step. clear CH.

step.
rmchunk MR3 MSh3 CH.
rmeta_open (conc st h) MUd WMd.
st1.
lazymatch goal with H : rw_cells usegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
[ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st3 mt) with G; reflexivity
| clear MUd WMd H ] end.

step.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
eapply (rmrep_extW _ _ _ MR4); try reflexivity.
intros q. unfold st3, st2, st1, st0, upd_meta.
destruct (decide (q = h)) as [->|NQh].
{ rewrite !get_meta_rec_put_same. f_equal.
destruct (decide (h = p)) as [<-|NHp].
- rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
- rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
destruct (decide (q = p)) as [->|NQp].
{ rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
-
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (6576296 + 16, 6576296 + 24)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1. st1.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.

step.
pose proof MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
pose proof (rw_cells_store_ok_at usegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (6576288 + 24)) CX1 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
rraw_store_finishF (6576296 + 16) (le8 (wz G)) FR1 MU WM1 SOK.

step.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_single. cbn [set_head].
eapply (rmrep_extW _ _ _ MR2); try reflexivity.
intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
End FAILM.

End RC__2.
End Mqe.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnOf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnOf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn9M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi8L.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.Mqm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmBS.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlfl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlfl.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma lw_slli52_srli58_sc mq : mw_ok mq ->
Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 (meta_word mq)))) 52))) 58)
= Z_to_bv 64 (m_sizeclass mq).
Proof.
intros MWq. pose proof (meta_word_range _ MWq) as WR. pose proof MWq as (LI & FB & SCR & ML).
f_equal. unfold sx32. rewrite (unsigned_lit (meta_word mq)) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite swrap32_eq'.
unfold meta_word.
Z.div_mod_to_equations. nia.
Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.

#[using="RC__ mr MR MSL AV0"] Lemma ravz_pre_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
bv_unsigned gw = G -> mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd118c) fc None m (seg_rom usegs))
(MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1180) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros HG MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0 in CH. fold G in CH. rewrite <- HG in CH.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
apply evt_done. reflexivity.
Qed.

#[using="b MR MSL AV0 Hmem Hgh AI FR32 MW MASK BNC SC0"] Lemma ravz_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
bv_unsigned gw = G -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz (sxv mask)) a2' a3' a4' a5' a6' a7' s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1204) fc None m' (seg_rom usegs)
/\ munch [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep st5 m')
(MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd118c) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros HG MI. unfold rt1_regs.
pose proof (munch_refl [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & G4 & G24). fold G in Gpos, GC, GI, G4, G24.
pose proof (meta_word_range _ MW) as MWR.
assert (AMO : amo_aligned AW (Z_to_bv 64 (bv_unsigned gw + 28)) = true).
{ apply amo_aligned_intro; [unfold alloc_ceiling in GC; lia|]. rewrite HG. clear -G4. Z.div_mod_to_equations. lia. }
clear G4 G24.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.

step.
destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8). unfold wa in RD8.
pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
step.

step. step.
assert (W8M : bv_unsigned w8 mod 32 = ai).
{ unfold ai. rewrite <- L8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
unfold zxb. rewrite (unsigned_lit (bv_unsigned w8)) by lia.
rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite W8M.
set (y := 2 ^ (ai + 1)).

step. step. rewrite negw_word.

pose proof (sxv_range f) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range (y - 1)) as RY1.
step. rewrite sx32_wz_sxv by lia.
step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.

clear CH. rmeta_open G MUa WMa. rewrite <- HG in MUa.
rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
step. if_false.
amo_step AMO.
step. if_false.
step. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. step. if_false.

step. rewrite addiw_m1_word.
step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
step.

assert (AI31 : Z.land ai 31 = ai).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (ACT : act = y - 1) by (unfold act, mask_upto, y; reflexivity).
assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
assert (Ypos : 0 < y) by (unfold y; apply Z.pow_pos_nonneg; lia).
pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR4 : rmrep st4 mX) end.
{ rewrite HG in MUa, CH. unfold st4. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUa | exact WMa |].
eapply rw_cells_congr; [ | | | exact CH]; [ | reflexivity | cbn; tauto].
unfold meta_cells, pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed oconc].
rewrite meta_word_upd_af. fold mr f. rewrite Hmem, E1. cbn [oconc]. rewrite !le4_sxv by lia. reflexivity. }
clear MUa WMa.

step. if_cases K1; zify_cond K1.
2:{ exfalso. apply MASK. unfold mask. rewrite ACT. apply (proj1 (sxv_zero (Z.land f (y - 1)) ltac:(lia))).
rewrite ?wz_unsigned in K1 by (apply sxv_range). first [exact K1 | change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones in K1 by lia; rewrite Z.mod_small in K1 by apply sxv_range; exact K1]. }
clear K1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HRW : ov_read_bytes usegs mX (wa (bv_unsigned gw + 32)) 4 = Some (le4 (Z_to_bv 64 (meta_word mr))))
by (destruct CH as [[_ B] _]; rewrite (bytes_at_ov_read usegs mX (bv_unsigned gw) _ 32 4 B) by (cbn; lia); reflexivity) end.
step. step. step.
rewrite (lw_slli52_srli58_sc mr MW).
pose proof MW as (_ & _ & SCR & _). fold mr in SCR.
set (sc := m_sizeclass mr) in *.

step. step. step. if_cases K2; zify_cond K2; change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia.
-
assert (NR : (7 <=? sc) && (sc <? 39) = false).
{ destruct (Z.lt_ge_cases sc 7); [apply Bool.andb_false_intro1; apply Z.leb_gt; lia|].
apply Bool.andb_false_intro2. apply Z.ltb_ge. rewrite Z.mod_small in K2 by lia. lia. }
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite NR. cbn [andb]. exact MR4.
-
assert (SC7 : 7 <= sc) by (destruct (Z.le_gt_cases 7 sc); [assumption| exfalso; clear -K2 H SCR; Z.div_mod_to_equations; lia]).
rewrite Z.mod_small in K2 by lia.
assert (IR : (7 <=? sc) && (sc <? 39) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).

step.
pose proof (rmrep_bounces_read st4 _ (sc - 7) (wa (6576296 + 880 + (sc - 7))) MR4 ltac:(lia) eq_refl) as RDB.
change (bounces st4 (sc - 7)) with (bounces st (sc - 7)) in RDB.
pose proof (BNC (sc - 7)) as BR.
step. rewrite ?zxb_b8 by lia.

step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
+
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
replace (bounces st (sc - 7) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. exact MR4.
+
step. rewrite ?(wz_unsigned (bounces st (sc - 7))) by lia.
pose proof MR4 as (_ & (_ & _ & _ & _ & X5 & _) & _).
pose proof (u8arr_store_ok usegs _ _ _ (sc - 7) (Z_to_bv 64 (6576288 + (sc + -7) + 888)) X5
ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear X5 RDB.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st4 mX (sc - 7) (bounces st (sc - 7) - 1) MR4 ltac:(lia)) as MR5; unfold RCTX in MR5 end.
rraw_store_finish0 (6576296 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) - 1)] MU WM SOK.
apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
split; [rewrite ?HG in MU; exact MU|].
split; [exact WM|]. split; [assumption|].
unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
replace (bounces st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. exact MR5.
Qed.
End AVZ.

Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

#[using="SZ"] Lemma rspan_loop_walk : forall (F : nat) (c span : Z)
(ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
0 <= c -> 0 <= span -> span + size * (Z.of_nat F + 2) < 2^31 -> c + 1 + Z.of_nat F < 2^31 ->
span_exit F span size = true -> mem_inv usegs m ->
evt usegs (fun ms' => exists (t0' t1' a6' : word),
ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 (wz (span_loop F (c + 1) span size)) (wz size) a6' (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1594) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp (wz span) t1 t2 s0 s1 a0 a1 a2 a3 (wz c) (wz size) (wz (span + size - 1)) (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1580) fc None m (seg_rom usegs)).
Proof.
induction F as [|F IH]; intros until m; intros C0 S0 SB CB EX MI; [discriminate|].
cbn [span_exit] in EX. cbn [span_loop].
rewrite Nat2Z.inj_succ in SB, CB.
pose proof (lxor_range31 span (span + size - 1) ltac:(lia) ltac:(lia)) as XR.

step. rewrite ?wz_unsigned by lia.
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (span + size))) with (wz (span + size)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (c + 1))) with (wz (c + 1)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
step. rewrite ?wz_unsigned by lia.
replace (Z_to_bv 64 (bv_swrap 32 (span + size - 1 + size))) with (wz (span + size + size - 1)) by (rewrite swrap_word, sxv_small by lia; unfold wz; f_equal; lia).
rewrite (Z.lxor_comm (span + size - 1) span).

step. if_cases K.
-
assert (LT : Z.lxor span (span + size - 1) < 4096).
{ unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_lt in K. exact K. }
replace (Z.lxor span (span + size - 1) <? 4096) with true in EX |- * by (symmetry; apply Z.ltb_lt; exact LT).
replace (c + 2) with (c + 1 + 1) by lia.
eapply (IH (c + 1) (span + size)); try assumption; try lia.
- assert (GE : ~ Z.lxor span (span + size - 1) < 4096).
{ intros LT. unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_ge in K. lia. }
replace (Z.lxor span (span + size - 1) <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
apply evt_done. do 3 eexists. reflexivity.
Qed.
End SPANLOOP.
#[using="Type"] Lemma ai_byte_land224 w v : 0 <= w -> 0 <= v ->
Z.land ((Z.lor (Z.land v 31) (Z.land w 224)) mod 256) 31 = Z.land v 31.
Proof.
intros Hw Hv. apply Z.bits_inj'. intros n Hn.
change 256 with (2^8). change 31 with (Z.ones 5).
rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
replace 224 with (Z.shiftl 7 5) by reflexivity.
destruct (Z.ltb_spec n 5).
- rewrite Z.shiftl_spec_low by lia. replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_true_r, andb_false_r, orb_false_r. reflexivity.
- replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.

Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

Ltac ract_prefix CH w8 :=
rmchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
step;
let RD8 := fresh "RD8" in let L8 := fresh "L8" in
destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8); unfold wa in RD8;
let W8R := fresh "W8R" in
pose proof (bv_unsigned_in_range _ w8) as W8R; change (bv_modulus 8) with 256 in W8R;
step;
let W8M := fresh "W8M" in
assert (W8M : bv_unsigned w8 mod 32 = ai0) by (unfold ai0; rewrite <- L8; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
step; unfold zxb; rewrite (unsigned_lit (bv_unsigned w8)) by lia; rewrite (sllw2_word (bv_unsigned w8)) by lia; rewrite W8M;
step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land.

#[using="RC__ b mr MR MSL Hmem Hgh AI0 MASKR"] Lemma ract_skip_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
Z.land mask (mask_upto ai0) <> 0 -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a1' a2' a3' a4' : word),
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1180) fc None m (seg_rom usegs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1158) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros NZ MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
pose proof (land_upper (mask_upto ai0) mask ltac:(lia) ltac:(lia)) as LR.
step. if_cases K; zify_cond K.
2:{ exfalso. apply NZ. rewrite Z.land_comm. apply (proj1 (sxv_zero (Z.land (mask_upto ai0) mask) ltac:(lia))).
rewrite ?wz_unsigned in K by (apply sxv_range).
first [exact K | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by apply sxv_range; exact K]. }
apply evt_done. do 4 eexists. reflexivity.
Qed.

#[using="b MR MSL SC Hmem Hgh AI0"] Lemma ract_next_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (mn : aptr),
Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some mn -> mn <> g -> meta_slot st mn -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a1' a2' a3' a4' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1180) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (set_active sc (Some mn) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1158) fc None m (seg_rom usegs)).
Proof.
intros until mn. intros ZR GN NEn MSn MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
assert (NEG : conc st mn <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
step. if_cases K; zify_cond K.
{ exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
clear K.

rewrite GN in CH. cbn [oconc] in CH.
step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.

clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (6576296 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6576296 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.

step.
apply evt_done. do 5 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.

#[using="ai0 MR MSL Hgh AI0"] Lemma rspan_tail_walk :
forall (ra sp gp tp t0 t1 t2 s1 a3 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (cnt2 wv : Z),
1 <= cnt2 <= 32 -> 0 <= wv < 256 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a1' a2' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3 a4' a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd118c) fc None m' (seg_rom usegs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) (Z_to_bv 64 (conc st b)) (Z_to_bv 64 wv) a3 (Z_to_bv 64 cnt2) a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd15a4) fc None m (seg_rom usegs)).
Proof.
intros until wv. intros C2R WVR UNK GM AV0 MI.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof MR as (_ & _ & _ & _ & GR & _). destruct (GR b gh Hgh) as (w8o & RWB & Hw8o). clear GR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (munch_refl [(conc st b, conc st b + 9)]%Z m) as MUb. pose proof (wmono_refl usegs m) as WMb.

step. step. rewrite ?(unsigned_lit (cnt2 + -1)) by lia. step. rewrite ?(unsigned_lit wv) by lia. step.
pose proof (land_upper (cnt2 + -1) 31 ltac:(lia) ltac:(lia)) as L2.
pose proof (land_upper wv 224 ltac:(lia) ltac:(lia)) as L1.
rewrite ?(unsigned_lit (Z.land (cnt2 + -1) 31)), ?(unsigned_lit (Z.land wv 224)) by lia.
set (nbv := Z.lor _ _).

step. rewrite (le1_mod nbv). mem_after_store.
pose proof (Z.lor_nonneg (Z.land (cnt2 + -1) 31) (Z.land wv 224)) as NBpos.
pose proof (Z.mod_pos_bound nbv 256 ltac:(lia)) as NBR.
lazymatch goal with H : rw_cells usegs ?mX (conc st b) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (set_group_active_idx b (cnt2 - 1) st) mX);
[ eapply (rmrep_set_group_ai st m mX b g (g_active_idx gh) (cnt2 - 1) (b8 (nbv mod 256)) MR); [ | exact UNK | exact MUb | exact WMb | | ]
| ] end.
{ rewrite Hgh. destruct gh as [gm gai]. cbn in GM |- *. subst gm. reflexivity. }
{ lazymatch goal with H : rw_cells usegs _ (conc st b) _ |- _ => rewrite GM in H; exact H end. }
{ rewrite b8_unsigned by lia. subst nbv. replace (cnt2 - 1) with (cnt2 + -1) by lia. apply ai_byte_land224; lia. }

assert (EA2 : s_areas (set_group_active_idx b (cnt2 - 1) st) = s_areas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (ER2 : s_regions (set_group_active_idx b (cnt2 - 1) st) = s_regions st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (EM2 : s_metas (set_group_active_idx b (cnt2 - 1) st) = s_metas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
assert (MS2 : meta_slot (set_group_active_idx b (cnt2 - 1) st) g) by (eapply meta_slot_same_areas; [exact EA2| exact MSL]).
rmchunk MR2 MS2 CH.
replace (get_meta_rec (set_group_active_idx b (cnt2 - 1) st) g) with mr in CH by (unfold mr, get_meta_rec; rewrite EM2; reflexivity).
replace (conc (set_group_active_idx b (cnt2 - 1) st) g) with G in CH by (unfold G, conc, get_region; rewrite ER2; reflexivity).
rewrite AV0 in CH.
step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MUb|]. split; [exact WMb|]. split; [assumption| exact MR2].
Qed.

#[using="MR MSL Hmem Hgh AI0"] Lemma ract_span_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 ->
mem_inv usegs m ->
let sc' := m_sizeclass mr in
let cnt := ai0 + 2 in
let size := size_class sc' * UNIT in
let span := UNIT + size * cnt in
let cnt1 := span_loop 300 cnt span size in
let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
evt usegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd118c) fc None m' (seg_rom usegs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1158) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros ZR GN MW SCR UNK GM AV0 MI sc' cnt size span cnt1 cnt2. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & _ & ML).
pose proof (size_class_range sc' ltac:(lia)) as SZR.
unfold RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES in *.
ract_prefix CH w8.
pose proof (QDUx.Mqb.mask_upto_range ai0 AI0) as MUR.
step. if_cases K; zify_cond K.
{ exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
clear K.

rewrite GN, AV0 in CH. cbn [oconc] in CH. fold G in CH.
step.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

step. rewrite (unsigned_lit (bv_unsigned w8)) by lia. rewrite L8. fold ai0. step. step. step. step.

assert (W5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
step. rewrite ?(unsigned_lit (meta_word mr)) by lia. step. rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 mr MW). fold sc'.
step.
lazymatch goal with HI : mem_inv usegs ?mc |- _ =>
pose proof (rsize_classes_read mc sc' HI ltac:(lia)) as SCRD; unfold RSIZE_CLASSES in SCRD end.
step. rewrite zx16_wz by lia. clear SCRD.
fold cnt.
assert (SZB : 16 <= size <= 881216) by (unfold size, UNIT; lia).
assert (CNB : 2 <= cnt <= 33) by (unfold cnt; lia).
assert (PR : 0 <= cnt * size <= 33 * 881216) by nia.
assert (EX : span_exit 300 span size = true) by (unfold span, size, cnt, UNIT; apply span_exit_ok; lia).
assert (SPB : span = cnt * size + 16) by (unfold span, UNIT; lia).
assert (Esz : size = size_class sc' * 16) by reflexivity. assert (Ecnt : cnt = ai0 + 2) by reflexivity.
pose proof (span_loop_bounds 300 cnt span size) as CB. fold cnt1 in CB. change (Z.of_nat 300) with 300 in CB.
assert (Ec2 : cnt2 = (if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1)) by reflexivity.
assert (Ec1 : cnt1 = span_loop 300 cnt span size) by reflexivity.
clearbody size cnt span cnt1 cnt2.

step. step. rewrite (unsigned_lit ai0), Z.shiftl_mul_pow2 by lia. step.
step. rewrite (wz_unsigned (size_class sc')), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite <- Esz.

step. rewrite ?(unsigned_lit (ai0 * 16 + 48)), ?(wz_unsigned (size_class sc')) by lia.
replace ((ai0 * 16 + 48) * size_class sc') with (span + size - 16) by (rewrite SPB, Esz, Ecnt; lia).
step. rewrite ?(unsigned_lit size), ?(unsigned_lit cnt) by lia. replace (size * cnt) with (cnt * size) by lia.
step. rewrite ?(unsigned_lit (span + size - 16)) by lia. rewrite swrap_word, sxv_small by lia.
replace (span + size - 16 + 15) with (span + size - 1) by lia.
step. rewrite ?(unsigned_lit (cnt * size)) by lia. rewrite swrap_word, sxv_small by lia. rewrite <- SPB.
step.

eapply evt_cut.
{ change (Z_to_bv 64 (ai0 + 1)) with (wz (ai0 + 1)). change (Z_to_bv 64 size) with (wz size).
eapply (rspan_loop_walk size ltac:(lia) 300 (ai0 + 1) span); try assumption; try (change (Z.of_nat 300) with 300; lia). }
intros ms' (t0' & t1' & a6' & ->). replace (ai0 + 1 + 1) with cnt by lia. rewrite <- Ec1.

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
step.

step. if_cases K; zify_cond K; rewrite ?(wz_unsigned cnt1), ?unsigned_lit in K by lia.
- replace (wz cnt1) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [lia| reflexivity]).
assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
-
step.
replace (Z_to_bv 64 (m_last_idx mr + 1)) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [reflexivity| f_equal; lia]).
assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
Qed.
End ACT.

End RC__1.
