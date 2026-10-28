(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0pa X0p9 X0qn X0py X0qd X0qg X0qe X0qf X0qh X0qj X0qk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0ql X0q1 X0o1 X0o2 X0ns X0o5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1ky X1lz X1m0 X1m1 X1lw X1lx X1m4 X1lb X1k8 X1jk X1ly X1k4 X1k6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section AG1.
Context {RCEIL : RunCeiling}.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

#[using="SC"] Lemma rag_entry_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (rt1_regs sc (Z_to_bv 64 0x328f8) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (RSIZE_CLASSES + sc * 2)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sc * 2))
(wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x328e0) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI. unfold rt1_regs, ralloc_meta_entry, RSIZE_CLASSES, RCTX, RMLOCK, RSSP_GUARD in *.
pose proof (size_class_range sc SC) as SZR.
step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
pose proof (rsize_classes_read m sc MI SC) as SCRD. unfold RSIZE_CLASSES in SCRD.
replace (88424 + 2 * sc) with (88424 + sc * 2) in SCRD by lia.
step. rewrite zx16_wz by lia. clear SCRD.
step. apply evt_done. reflexivity.
Qed.
End AG1.

Lemma rag_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
0 <= gm < 2^64 -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if gm =? 0 then 0x32f60 else 0x32904)) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x328f8) fc None m (seg_rom rsegs)).
Proof.
intros until gm. intros GR MI.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
- subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
- replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.

Section STC.
Context {RCEIL : RunCeiling}.
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
ms' = MS (mkR (Z_to_bv 64 0x32ae0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2' a3' a4' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz (szc * 16 * cnt)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32a10) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI.
assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
pose proof rstc_q_eq as STC. fold q in STC.
unfold RSIZE_CLASSES, ralloc_slot_entry in *.

assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
evt rsegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0x32ae0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 88424) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 206592) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 88424) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32ad4) fc None m (seg_rom rsegs))).
{ intros a0' a2' a3' jv ->.
pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
step. rewrite X1cc.sextw_small by lia. step. step.
apply evt_done. sf_eexists 3%nat. reflexivity. }

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
step. replace (88424 + (i + 1) * 2) with (88424 + 2 * (i + 1)) by lia.
pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
evt rsegs (fun ms' => exists a2'' a3'' a4'',
ms' = MS (mkR (Z_to_bv 64 0x32ae0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 88424) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 206592) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 88392) (Z_to_bv 64 q) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 88424) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32ab8) fc None m (seg_rom rsegs))).
{ intros i1 c Hi1 Hc.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (88424 + i1 * 2) with (88424 + 2 * i1) by lia.
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

Lemma rnest_ret_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
-1 <= idx < 32 -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if idx =? -1 then 0x32b58 else 0x32ae4)) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32ae0) fc None m (seg_rom rsegs)).
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
