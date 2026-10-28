(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0pa X0qn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1lb.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition rre_stc_post (ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (n : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t1 a4 a5 a7,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (size_to_class n + 1)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x335f4) fc None m (seg_rom rsegs).

Lemma rre_stc_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n : Z),
a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD -> a5 = Z_to_bv 64 RSIZE_CLASSES -> mem_inv rsegs m ->
evt rsegs (rre_stc_post ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 n F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x33464) fc None m (seg_rom rsegs)).
Proof.
intros until n. intros HA N HA5 MI. subst a1 a5. unfold RSIZE_CLASSES.
pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.

assert (J2 : forall (x6 x14 x15 x17 : word) (v : Z), v = size_to_class n ->
evt rsegs (rre_stc_post ra sp gp tp t0 t2 s0 s1 a0 (Z_to_bv 64 n) a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 n F fc m)
(MS (mkR ra sp gp tp t0 x6 t2 s0 s1 a0 (Z_to_bv 64 n) (Z_to_bv 64 v) a3 x14 x15 a6 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x335f0) fc None m (seg_rom rsegs))).
{ intros x6 x14 x15 x17 v ->. step. rewrite ?unsigned_lit, ?swrap32_small by lia. unfold rre_stc_post. finish. }

step. step. step.
rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
-
apply J2. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
-
assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
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

step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.
assert (K13 : 3 <= k <= 12) by (apply LG; lia).

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
assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (88424 + (i + 1) * 2) with (88424 + 2 * (i + 1)) by lia.
pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (x6 : word) (c : Z),
c = (if size_class (i + 1) <? x then i + 2 else i) - i + 120 ->
evt rsegs (rre_stc_post ra sp gp tp t0 t2 s0 s1 a0 (Z_to_bv 64 n) a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 n F fc m)
(MS (mkR ra sp gp tp t0 x6 t2 s0 s1 a0 (Z_to_bv 64 n) (Z_to_bv 64 q) a3 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 88424) a6 (Z_to_bv 64 c)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x335d4) fc None m (seg_rom rsegs))).
{ intros x6 c Hc. set (i1 := if size_class (i + 1) <? x then i + 2 else i) in *.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (88424 + i1 * 2) with (88424 + 2 * i1) by lia.
pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply J2. rewrite STC, STQ. cbv zeta. fold i1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply J2. rewrite STC, STQ. cbv zeta. fold i1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
