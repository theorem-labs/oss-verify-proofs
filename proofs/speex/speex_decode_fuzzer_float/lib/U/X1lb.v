(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0qn X0py X0qd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0pa.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition rDB32 : Z := 125613361.
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RDEBRUIJN 32 with Some bs => bs | None => [] end).

Lemma rdebruijn_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.

Lemma rdebruijn_read : forall m k, mem_inv rsegs m -> 0 <= k < 32 ->
ov_read_bytes rsegs m (wa (RDEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof.
intros m k MI Hk.
destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (rdbi_range k) as R.
rewrite (bytes_at_read rsegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
destruct Hn as (n & -> & Hn).
Ltac solve_db := vm_compute; reflexivity.
do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

Lemma mul_srliw27 k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof.
intros Hk. unfold rdbi.
assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
rewrite unsigned_lit by (unfold rDB32; nia).
change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rclz_v4 (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) x in
let v2 := Z.lor v1 (Z.shiftr x 1) in
let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
let w3 := Z.lor (Z.shiftr w2 4) w2 in
Z.lor (Z.shiftr w3 8) w3.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof.
intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
apply andb_prop in X. destruct X as [X1 X2].
apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.

Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.

Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof. intros Ha He.
assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3259c) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma rmalloc_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
stk rsegs m lo (bv_unsigned sp) -> 0x6e000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
rw_cells rsegs m RNEED_LOCKS [C1 (b8 0)] ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
intros until n. intros HA N ST ILO LO MI NL. subst a0.
pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry, RNEED_LOCKS in *.
step. carve_frame 48%nat ST. step. step. step. step. step. step.

step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.

step. step. step. step. step.
step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.

step. step. step. step. step.
rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).

assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
sc = size_to_class n ->
mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 448219 [C1 (b8 0)] ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 448328) a0' a1' a2' a3' a4 a5 a6 a7
s2 (Z_to_bv 64 88392) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32584) fc None mj (seg_rom rsegs))).
{ intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
apply evt_done. unfold rentry_post, RMLOCK, RDEBRUIJN. sf_eexists 5%nat. split; [reflexivity|].
split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
-
apply LOCKJ; try assumption.
rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
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
step.
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
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.
assert (K13 : 3 <= k <= 12) by (apply LG; lia).

step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step.
rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.

step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step. replace (88424 + (i + 1) * 2) with (88424 + 2 * (i + 1)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.

step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z) (mj : mem),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 448219 [C1 (b8 0)] ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 448328)
(Z_to_bv 64 (120 - i)) (Z_to_bv 64 88424) (Z_to_bv 64 c) (Z_to_bv 64 (88424 + 2 * (i + 1))) a4 a5 a6 a7
s2 (Z_to_bv 64 88392) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32568) fc None mj (seg_rom rsegs))).
{ intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (88424 + i1 * 2) with (88424 + 2 * i1) by lia.
pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32404) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma rentry_big_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^32 ->
stk rsegs m lo (bv_unsigned sp) -> 0x6e000 <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
evt rsegs (rentry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
intros until n. intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.
step. step. step. step. step.
step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.
apply evt_done. unfold rentry_big_post, RMLOCK. sf_eexists 2%nat. split; [reflexivity|].
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
