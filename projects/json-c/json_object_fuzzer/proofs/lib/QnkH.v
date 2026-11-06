(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qc3B QZAi QdBa QfYR QnDM_c1 QDUx Q9Ay QX7A QhY6 QGmo QvBB QTp6 QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QdBa QfYR.
Import QnDM_c1 QDUx Q9Ay.
Import QX7A QhY6 QGmo QvBB.Mq1.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Import QZAa.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Definition SCALBNL : Z := 0xd86b4.
Definition COPYSIGNL : Z := 0xd83a4.
Definition FABSL : Z := 0xd86a8.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Lemma testbit_small_high : forall x k i, (0 <= x < 2^k)%Z -> (0 <= k <= i)%Z -> Z.testbit x i = false.
Proof.
intros x k i Hx Hk. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_low_high : forall x y k, (0 <= x < 2^k)%Z -> (0 <= y)%Z -> (0 <= k)%Z -> Z.lor x (y * 2^k) = (x + y * 2^k)%Z.
Proof.
intros x y k Hx Hy Hk. apply lor_disjoint_add.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k).
- rewrite Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
- rewrite (testbit_small_high x k i) by lia. reflexivity.
Qed.

Lemma land_highmask : forall x k, (0 <= x < 2^64)%Z -> (0 <= k < 64)%Z ->
Z.land x (2^64 - 2^k) = (x - x mod 2^k)%Z.
Proof.
intros x k Hx Hk. rewrite <- (zb_shr_shl x k) by lia.
replace (2^64 - 2^k)%Z with (Z.shiftl (Z.ones (64 - k)) k).
2:{ rewrite Z.shiftl_mul_pow2, Z.ones_equiv by lia. rewrite Z.mul_pred_l, <- Z.pow_add_r by lia. replace (64 - k + k)%Z with 64%Z by lia. lia. }
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i k).
- rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
- rewrite !Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - k + k)%Z with i by lia.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
+ rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry. apply (testbit_small_high x 64 i); lia.
Qed.

Lemma land_bit63 : forall x, (0 <= x < 2^64)%Z -> Z.land x 9223372036854775808 = (x - x mod 2^63)%Z.
Proof. intros x Hx. change 9223372036854775808%Z with (2^64 - 2^63)%Z. apply land_highmask; lia. Qed.
Lemma land_m63 : forall x, Z.land x 9223372036854775807 = (x mod 2^63)%Z.
Proof. intros. change 9223372036854775807%Z with (2^63 - 1)%Z. apply zb_land_mask. lia. Qed.
Lemma land_m48 : forall x, Z.land x 281474976710655 = (x mod 2^48)%Z.
Proof. intros. change 281474976710655%Z with (2^48 - 1)%Z. apply zb_land_mask. lia. Qed.

Lemma copysign_hi_eq : forall xh yh, (0 <= xh < 2^64)%Z -> (0 <= yh < 2^64)%Z ->
Z.lor (Z.land (Z.shiftl (Z.lor (Z.land (Z.shiftl (Z.shiftr yh 63) 15) 18446744073709551615)
(Z.shiftr (Z.land (Z.shiftl xh 1) 18446744073709551615) 49)) 48) 18446744073709551615)
(Z.land xh 281474976710655)
= Z.lor (Z.land xh 9223372036854775807) (Z.land yh 9223372036854775808).
Proof.
intros xh yh Hx Hy.
rewrite !land_W64, land_m48, land_m63, land_bit63 by lia.
rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
set (s := (yh / 2^63)%Z). assert (Hs : (0 <= s <= 1)%Z) by (subst s; Z.div_mod_to_equations; lia).
rewrite (Z.mod_small (s * 2^15)) by lia.
set (b := ((xh * 2 ^ 1) mod 2 ^ 64 / 2 ^ 49)%Z). assert (Hb : (0 <= b < 2^15)%Z) by (subst b; Z.div_mod_to_equations; lia).
rewrite (Z.lor_comm (s * 2^15) b), lor_low_high by lia.
rewrite (Z.mod_small ((b + s * 2^15) * 2^48)) by lia.
rewrite (Z.lor_comm ((b + s * 2^15) * 2^48)), lor_low_high by (try (Z.div_mod_to_equations; lia); lia).
replace (yh - yh mod 2^63)%Z with (s * 2^63)%Z by (subst s; Z.div_mod_to_equations; lia).
rewrite lor_low_high by (try (Z.div_mod_to_equations; lia); lia).
subst b s. Z.div_mod_to_equations. lia.
Qed.

Definition leafq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Lemma land63_range : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.land x 0x7fffffffffffffff < 2^64)%Z.
Proof. intros x Hx. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; lia. Qed.

Lemma fabsl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv rsegs m ->
evt rsegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FABSL) fc None m (seg_rom rsegs)).
Proof.
intros until X. intros MI. unfold FABSL.
pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH. pose proof (land63_range (hi64 X) ltac:(lia)) as R63.
zs. zs. zs.
apply evt_done. unfold leafq_post. repeat (lazymatch goal with |- ex _ => eexists end).
unfold m_fabsl. rewrite lo64_mk128, hi64_mk128 by lia.
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma copysignl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
mem_inv rsegs m ->
evt rsegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom rsegs)).
Proof.
intros until Y. intros MI. unfold COPYSIGNL.
pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH. pose proof (lo64_range Y) as RLY. pose proof (hi64_range Y) as RHY.
do 9 zs. zs.
apply evt_done. unfold leafq_post. repeat (lazymatch goal with |- ex _ => eexists end).
unfold m_copysignl. rewrite copysign_hi_eq by lia.
assert (R1 : (0 <= Z.lor (Z.land (hi64 X) 9223372036854775807) (Z.land (hi64 Y) 9223372036854775808) < 2^64)%Z).
{ apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; lia. }
rewrite lo64_mk128, hi64_mk128 by lia.
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma land_m16 : forall x, Z.land x 65535 = (x mod 2^16)%Z.
Proof. intros. change 65535%Z with (2^16 - 1)%Z. apply zb_land_mask. lia. Qed.

Lemma scal_hi_eq : forall n h, (-2^20 <= n < 2^20)%Z -> (0 <= h < 2^64)%Z ->
Z_to_bv 64 (Z.lor (Z.land (Z.shiftl (Z.land n 18446744073709551615) 48) 18446744073709551615) (Z.land h 281474976710655) + 4611404543450677248)
= Z_to_bv 64 (Z.lor (Z.land h 281474976710655) (Z.shiftl (Z.land (16383 + n) 65535) 48)).
Proof.
intros n h Hn Hh. apply Z_to_bv_eqm.
rewrite !land_W64, !land_m48, land_m16, !Z.shiftl_mul_pow2 by lia.
rewrite (Z.lor_comm _ (h mod 2^48)).
replace ((n mod 2 ^ 64 * 2 ^ 48) mod 2 ^ 64)%Z with ((n mod 2^16) * 2^48)%Z by (Z.div_mod_to_equations; nia).
rewrite !lor_low_high by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. nia.
Qed.
Definition scal_reduce (x n : Z) : Z * Z :=
(if 16383 <? n then
let x := f128_mul x C_2P16383 in let n := n - 16383 in
if 16383 <? n then
let x := f128_mul x C_2P16383 in let n := n - 16383 in (x, if 16383 <? n then 16383 else n)
else (x, n)
else if n <? -16382 then
let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in
if n <? -16382 then
let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in (x, if n <? -16382 then -16382 else n)
else (x, n)
else (x, n))%Z.
Definition U1 : Z := f128_of_d (bv_unsigned D_ONE).
Definition scal_u (n : Z) : Z :=
mk128 (Z.lor (Z.land (hi64 U1) 0x0000ffffffffffff) (Z.shiftl (Z.land (0x3fff + n)%Z 0xffff) 48)) (lo64 U1).
Lemma m_scalbnl_eq : forall x n, m_scalbnl x n = f128_mul (fst (scal_reduce x n)) (scal_u (snd (scal_reduce x n))).
Proof.
intros x n. unfold m_scalbnl, scal_reduce, scal_u, U1.
destruct (16383 <? n); [destruct (16383 <? n - 16383); reflexivity|].
destruct (n <? -16382)%Z; [destruct (n + (16382 - 113) <? -16382)%Z; reflexivity|]. reflexivity.
Qed.

Definition scalbnl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 D_ONE F) (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 112, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 112) q.

Definition scalbnl_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n : Z),
stk rsegs m (q - 112) q -> (4096 <= q - 112)%Z -> (q < 2^63)%Z ->
(-2^31 <= n < 2^31)%Z ->
mem_inv rsegs m ->
evt rsegs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_scalbnl X n) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCALBNL) fc None m (seg_rom rsegs)).

Lemma scalbnl_spec : scalbnl_stmt.
Proof.
unfold scalbnl_stmt. intros until n. intros ST Q0 Q1 Hn MI.
pose proof (munch_refl [(q - 112, q)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH.
rewrite m_scalbnl_eq. unfold SCALBNL.
zs. carve_frame 32%nat ST.
zs. zs. zs. zs. zs. zs.

assert (FIN : forall mf (x1 x10 x11 x12 x13 x14 x15 x16 x17 x5 x6 x7 x28 x29 x30 x31 : word) x' n',
mem_inv rsegs mf -> munch [(q - 112, q)]%Z m mf -> wmono rsegs m mf ->
stk rsegs mf (q - 112) (q + -32) ->
rw_cells rsegs mf (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
(-2^20 <= n' < 2^20)%Z ->
fst (scal_reduce X n) = x' -> snd (scal_reduce X n) = n' ->
evt rsegs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_mul (fst (scal_reduce X n)) (scal_u (snd (scal_reduce X n)))) m)
(MS (mkR x1 (Z_to_bv 64 (q + -32)) gp tp x5 x6 x7 (Z_to_bv 64 n') (Z_to_bv 64 (hi64 x')) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 x')) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd87b4) fc None mf (seg_rom rsegs))).
{ clear MU WM MI ST FR. intros mf x1 x10 x11 x12 x13 x14 x15 x16 x17 x5 x6 x7 x28 x29 x30 x31 x' n' MI MU WM ST FR Rn Ex En.
rewrite Ex, En. pose proof (lo64_range x') as RL'. pose proof (hi64_range x') as RH'.
zs. zs.
zs. callw (eapply extenddftf2_callv; [hyp | lia]).
change 4607182418800017408%Z with (bv_unsigned D_ONE). fold U1.
pose proof (lo64_range U1) as RLU. pose proof (hi64_range U1) as RHU.
do 10 zs.
rewrite (scal_hi_eq n' (hi64 U1)) by lia.
assert (RU : (0 <= Z.lor (Z.land (hi64 U1) 281474976710655) (Z.shiftl (Z.land (16383 + n') 65535) 48) < 2^64)%Z).
{ apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; [apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; lia|]. rewrite Z.shiftl_mul_pow2, land_m16 by lia. Z.div_mod_to_equations. lia. }
replace (Z_to_bv 64 (lo64 U1)) with (Z_to_bv 64 (lo64 (scal_u n'))) by (unfold scal_u; rewrite lo64_mk128 by lia; reflexivity).
replace (Z_to_bv 64 (Z.lor (Z.land (hi64 U1) 281474976710655) (Z.shiftl (Z.land (16383 + n') 65535) 48))) with (Z_to_bv 64 (hi64 (scal_u n')))
by (unfold scal_u; rewrite hi64_mk128 by lia; reflexivity).
zs. callw (eapply multf3_callq; [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
do 6 zs.
match goal with H : stk _ _ _ _ |- _ => rename H into ST2 end. replace (q + -32 - 80)%Z with (q - 112)%Z in ST2 by lia.
release_frame FR ST2 q.
apply evt_done. unfold scalbnl_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp | exact ST2]. }

Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
Ltac decb := repeat match goal with |- context [Z.ltb ?a ?b] =>
first [replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; mlia2) | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; mlia2)] end.
Ltac fin F x n := eapply (F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x n); [hyp | hyp | hyp | hyp | hyp | | unfold scal_reduce; decb; cbn [fst snd]; reflexivity | unfold scal_reduce; decb; cbn [fst snd]; lia]; try mlia2.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  zs. zs. zs. fin FIN X n.
+
zs. zs. zs. zs.
zs. callw (eapply multf3_callq with (X := X) (Y := C_2PM16269); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
set (X1 := f128_mul X C_2PM16269) in *. pose proof (lo64_range X1) as RL1. pose proof (hi64_range X1) as RH1.
zs. zs. zs. (if_cases K3; zify_cond K3; try (rewrite ?signed_of_Z in K3 by lia)).
*  zs. zs. zs. zs. zs. fin FIN X1 (n + 16269)%Z.
* zs. zs. zs. callw (eapply multf3_callq with (X := X1) (Y := C_2PM16269); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
set (X2 := f128_mul X1 C_2PM16269) in *. pose proof (lo64_range X2) as RL2. pose proof (hi64_range X2) as RH2.
zs. zs. zs. zs. zs. (if_cases K4; zify_cond K4; try (rewrite ?signed_of_Z in K4 by lia)).
-- zs. zs. zs. zs. fin FIN X2 (n + 32538)%Z.
-- zs. zs. zs. zs. zs. eapply (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 (-48920 + 32538)%Z); [hyp | hyp | hyp | hyp | hyp | lia | unfold scal_reduce; decb | unfold scal_reduce; decb];
destruct (Z.ltb_spec0 (n + (16382 - 113) + (16382 - 113)) (-16382)); cbn [fst snd]; first [reflexivity | mlia2].
-
zs. zs. zs. zs.
zs. callw (eapply multf3_callq with (X := X) (Y := C_2P16383); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
set (X1 := f128_mul X C_2P16383) in *. pose proof (lo64_range X1) as RL1. pose proof (hi64_range X1) as RH1.
zs. zs. zs. (if_cases K3; zify_cond K3; try (rewrite ?signed_of_Z in K3 by lia)).
+  zs. zs. zs. zs. zs. zs. fin FIN X1 (n - 16383)%Z.
+ zs. zs. zs. callw (eapply multf3_callq with (X := X1) (Y := C_2P16383); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
set (X2 := f128_mul X1 C_2P16383) in *. pose proof (lo64_range X2) as RL2. pose proof (hi64_range X2) as RH2.
zs. zs. zs. zs. zs. (if_cases K4; zify_cond K4; try (rewrite ?signed_of_Z in K4 by lia)).
* zs. zs. zs. zs. fin FIN X2 (n - 32766)%Z.
* zs. zs. zs. zs. zs. eapply (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 (49149 - 32766)%Z); [hyp | hyp | hyp | hyp | hyp | lia | unfold scal_reduce; decb | unfold scal_reduce; decb];
destruct (Z.ltb_spec0 16383 (n - 16383 - 16383)); cbn [fst snd]; first [reflexivity | mlia2].
Qed.

End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC Lib.SepCache Qy5Y Qbf8 QSzV G.T_rfj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import Qbf8 QSzV QvBB.Mq1.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Definition SHLIM : Z := 0xd6294.
Definition SHGETC : Z := 0xd62cc.
Definition UFLOW : Z := 0xd2e90.
Definition TOREAD : Z := 0xd2f1c.
Definition STRING_READ : Z := 0xd262c.

Definition got_ssp := 0xe6b80%Z.
Definition ssp_guard := 0x642ea0%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].

Notation rfj := G.T_rfj.rfj.
Notation mkJ := G.T_rfj.mkJ.
Notation j_flags := G.T_rfj.j_flags.
Notation j_pad0 := G.T_rfj.j_pad0.
Notation j_close := G.T_rfj.j_close.
Notation j_wend := G.T_rfj.j_wend.
Notation j_wpos := G.T_rfj.j_wpos.
Notation j_mbz1 := G.T_rfj.j_mbz1.
Notation j_wbase := G.T_rfj.j_wbase.
Notation j_read := G.T_rfj.j_read.
Notation j_write := G.T_rfj.j_write.
Notation j_seek := G.T_rfj.j_seek.
Notation j_bufsize := G.T_rfj.j_bufsize.
Notation j_prev := G.T_rfj.j_prev.
Notation j_next := G.T_rfj.j_next.
Notation j_fd := G.T_rfj.j_fd.
Notation j_ppid := G.T_rfj.j_ppid.
Notation j_lockcount := G.T_rfj.j_lockcount.
Notation j_mode := G.T_rfj.j_mode.
Notation j_lock := G.T_rfj.j_lock.
Notation j_lbf := G.T_rfj.j_lbf.
Notation j_pad1 := G.T_rfj.j_pad1.
Notation j_cookie := G.T_rfj.j_cookie.
Notation j_off := G.T_rfj.j_off.
Notation j_getln := G.T_rfj.j_getln.
Notation j_mbz2 := G.T_rfj.j_mbz2.
Notation j_pl := G.T_rfj.j_pl.
Notation j_nl := G.T_rfj.j_nl.
Notation j_locale := G.T_rfj.j_locale.

Definition M64 : Z := 18446744073709551615.

Definition rf_rend (T p : Z) (w : bool) (f : shfile) : Z :=
if sh_stdio f then (if w then T + p else T) else M64.

Definition rf_cells (T p : Z) (w : bool) (f : shfile) (J : rfj) : list cell :=
let rend := rf_rend T p w f in
[C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)); C8 (Z_to_bv 64 (- sh_cnt0 f));
C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

Definition rf_cells_raw (T p : Z) (w : bool) (f : shfile) (J : rfj) (she shl shc : word) : list cell :=
let rend := rf_rend T p w f in
[C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
C8 she; C8 shl; C8 shc;
C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

Lemma rf_cells_raw_eq : forall T p w f J,
rf_cells T p w f J = rf_cells_raw T p w f J (Z_to_bv 64 (rf_rend T p w f)) (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. reflexivity. Qed.

Lemma rf_cells_size : forall T p w f J, length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat -> cells_size (rf_cells T p w f J) = 232%nat.
Proof. intros. reflexivity. Qed.

Definition ssJ : rfj :=
mkJ (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 STRING_READ) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 M64) (Z_to_bv 64 M64) (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

Definition RFI (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
sh_ok T txt f /\ (-1 <= c < 256)%Z /\
(sh_shlim_neg f = false -> kmin <= sh_rpos f)%Z /\
(sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
(sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
(w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ /\ 0 <= sh_cnt0 f <= sh_rpos f)%Z.

Definition shlim_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (w : bool) (f : shfile) (J : rfj) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(Fp, Fp + 232)%Z] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' Fp (rf_cells T p w (sh_lim0 f) J).

Definition shlim_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (txt : list Z) (f : shfile) (J : rfj) (she shl shc : word),
rw_cells rsegs m Fp (rf_cells_raw T p w f J she shl shc) ->
sh_ok T txt f -> length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat ->
(0 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= p <= zlength txt)%Z ->
mem_inv rsegs m ->
evt rsegs (shlim_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p w f J m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHLIM) fc None m (seg_rom rsegs)).

Ltac show_goal := match goal with |- ?g => idtac g end.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
end.
Lemma sx32_M64 : sx32 (Z_to_bv 64 18446744073709551615) = Z_to_bv 64 18446744073709551615.
Proof. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit by lia. vm_compute. reflexivity. Qed.
Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Lemma shlim_spec : shlim_stmt.
Proof.
unfold shlim_stmt. intros until shc. intros FC OK L0 L1 T0 T1 Hp MI.
pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold rf_cells_raw in FC, B. cbn [cells_size csize Nat.add] in B.
destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold SHLIM.
assert (RR : (0 <= rf_rend T p w f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); [destruct w|]; lia).
unfold M64 in RR. pose_word_ranges.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)); change (Z.b2z (0 <? 0)) with 0%Z in K1; rewrite Z.land_0_l in K1; [clear K1 | exfalso; apply K1; reflexivity].
zs. zs.
apply evt_done. unfold shlim_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold rf_cells, sh_lim0. cbn [sh_rpos sh_cnt0 sh_stdio sh_shlim_neg sh_n sh_buf].
unfold rf_rend in *. cbn [sh_stdio].
replace (- sh_rpos f)%Z with (T - (T + sh_rpos f))%Z by lia. hyp.
Qed.

Definition zero4 : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition w0 : word := Z_to_bv 64 0.

Definition ss_cells (T rpos rend : Z) (mode : word) (cookie shend : Z) (shl shc : word) : list cell :=
[C4 w0; CB 4 zero4; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend);
C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C8 (Z_to_bv 64 STRING_READ); C8 w0; C8 w0;
C8 (Z_to_bv 64 T); C8 w0; C8 w0; C8 w0; C4 w0; C4 w0; C8 w0;
C4 mode; C4 (Z_to_bv 64 M64); C4 w0; CB 4 zero4;
C8 (Z_to_bv 64 cookie); C8 w0; C8 w0; C8 w0;
C8 (Z_to_bv 64 shend); C8 shl; C8 shc;
C8 w0; C8 w0; C8 w0].

Lemma rf_cells_ss : forall T p w f, sh_stdio f = true ->
rf_cells T p w f ssJ = ss_cells T (T + sh_rpos f) (rf_rend T p w f) (Z_to_bv 64 M64) (rf_rend T p w f) (rf_rend T p w f)
(Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. intros T p w f ST. unfold rf_cells, ss_cells. rewrite ST. reflexivity. Qed.

Definition toread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T cookie shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 16, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 16) (q)
/\ rw_cells rsegs m' Fp (ss_cells T T T (Z_to_bv 64 M64) cookie shend shl shc).

Definition toread_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T rpos rend cookie shend : Z) (mode shl shc : word),
rw_cells rsegs m Fp (ss_cells T rpos rend mode cookie shend shl shc) ->
(mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
(0 <= T /\ T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= cookie < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
stk rsegs m (q - 16) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (toread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T cookie shend shl shc m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TOREAD) fc None m (seg_rom rsegs)).

Lemma toread_spec : toread_stmt.
Proof.
unfold toread_stmt. intros until shc. intros FC Hmode RT Rrp Rre Rck Rsh ST SPLO SPF SPF2 Q0 Q1 MI.
pose proof (munch_refl [(q - 16, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold ss_cells, w0 in FC. cbn [cells_size csize Nat.add] in B.
unfold TOREAD, M64 in *. pose_word_ranges.
zs. carve_frame 16%nat ST.
zs. zs. zs.
destruct Hmode as [-> | ->].
all: zs; rewrite ?(sx32_small 0), ?sx32_M64 by lia.
all: do 6 zs.
all: (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
all: zs; rewrite (zx32_lit 0) by lia.
all: do 5 zs.
all: (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ exfalso; lia | ]).
all: do 8 zs.
all: zs; zs; zs; zs.
all: release_frame FR ST q.
all: apply evt_done; unfold toread_post; repeat (lazymatch goal with |- ex _ => eexists end).
all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|].
all: unfold ss_cells, w0; replace (T + 0)%Z with T by lia; hyp.
Qed.

End Mq1.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QUZl Q7S0 Ql2m QGeV QLsg QkQT QWTl QM7w QCwx QFqQ QQbX Qv4L Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QWTl.Mq0 QM7w.
Import QCwx.Mq1 QFqQ.Mq0 QQbX.Mq3 Qv4L.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Notation RISTF := (@ISTF_g ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved rc_secret).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rimplT_steq {R} o (t1 t2 : QUZl.M R) s Q ms :
steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof.
intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|exact H]. apply eruns_steq. exact Hs.
Qed.

#[using="Type"] Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> QUZl.M R') -> QUZl.M R' -> QUZl.M R')
(k : X -> Y -> QUZl.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
rimplT o (P _ kS bS) s QS ms ->
(forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
(forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
rimplT o (P R k bail) s Q ms.
Proof.
intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
eapply rimplT_bind; [eapply rimplT_reach; exact H|].
intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
(exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
/\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

Definition ras_post2
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
(st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
/\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
/\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
/\ mrel st st1 /\ brk_link_ps st1 s'
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ as_inv2 st0 st st1 sc idx
/\ 0 <= c_mmap_counter (ctx st1) < 2^32
/\ ((idx = -1 /\ errv' = Z_to_bv 64 12)
\/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
/\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

#[using="Type"] Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof. reflexivity. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
forall (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).

#[using="Type"] Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
forall (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
Proof.
intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot _ R' full_lay fuel st sc req k' b') k bail s
(fun r s' ms' => match r with
| Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
| None => False end)).
- apply alloc_slot_nat.
- eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
- intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
- intros s' ms' [].
Qed.

#[using="Type"] Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
forall (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 0x622e60 ->
(forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
rimplT o (k st1 mo) s' Q ms') ->
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs)).
Proof.
intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta _ R' st k' b') k bail s
(fun r s' ms' => match r with
| Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
| None => False end)).
- apply alloc_meta_nat.
- eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
- intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
- intros s' ms' [].
Qed.

End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm Q98Z QkLq QnOf QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QTp6.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 QDUx.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq2 QQbX.Mq1 QdZ1.Mq0 Qv4L.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_disp_fin : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (p : aptr) (r : region),
rmrep st m -> c_avail_meta_area_count (ctx st) <> 0 -> 0 <= c_avail_meta_area_count (ctx st) < 2^64 ->
c_avail_meta_areas (ctx st) = Some p -> (s_regions st) !! (fst p) = Some r -> pgal (snd p) -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce600) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce460) fc None m (seg_rom rsegs)).
Proof.
intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite AMA in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). unfold alloc_ceiling in RBC.
pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
assert (AL : Z.land (conc st p) 4095 = 0).
{ rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
assert (PB : 0 <= conc st p < 2^64) by lia.
clear RBAL RU RBC RL0 WR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.

st1. st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
rewrite CF.

st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
st1. st1.

st1. st1. rewrite ?AL, ?AL'. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma ram_to_mprotect : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (P : Z),
evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xce610) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P)
(Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce600) fc None m (seg_rom rsegs)).
Proof.
intros.

st1. st1. st1. st1.
apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.

#[using="Type"] Lemma ram_mp_ok0 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte),
evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce570) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce610) fc None m (seg_rom rsegs)).
Proof.
intros.
st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma ram_mp_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo e : Z) (st : mstate),
rmrep st m -> mem_inv rsegs m -> tp = Z_to_bv 64 0x622e60 ->
rw_cells rsegs m (errno_addr tp) [C4 (Z_to_bv 64 e)] -> 1 <= e <= 4095 -> e <> 38 ->
rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (fun ms' => ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0) ms'
/\ rw_cells rsegs (ms_mem ms') (errno_addr tp) [C4 (Z_to_bv 64 e)])
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce610) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
subst tp. rewrite (unsigned_lit 0x622e60) in * by lia. change (6434400 + -164) with 6434236 in *.
change (Z_to_bv 64 e) with (wz e) in ERR.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.

st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.

st1. st1. st1. st1.

st1. rewrite sx32_wz by lia. st1. st1.
assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
rewrite CF; clear CF.

st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. split.
- unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
- cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed.

End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QTp6.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 Q9Ay.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq2 QQbX.Mq1 QdZ1.Mq0 Qv4L.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_disp_dead : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkDead ->
evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce510) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce460) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6566376 + 912) with 6567288 in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.

st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma ram_to_mmap : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> 0 <= c_meta_alloc_shift (ctx st) <= 40 ->
let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xce53c) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n)
(Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce510) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR SH n.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
unfold RCTX, RMLOCK, RSSP_GUARD in *.

st1. st1. st1.
rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
{ rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }

st1. st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.

#[using="Type"] Lemma ram_mm_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate),
rmrep st m -> mem_inv rsegs m ->
rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce53c) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.

st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed.

#[using="Type"] Lemma ram_mm_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo x n : Z) (st0 st : mstate) (rid : N) (r : region),
rmrep st m -> mem_inv rsegs m -> (forall a, ram_fp st0 lo (bv_unsigned sp) a -> ram_fp st lo (bv_unsigned sp) a) ->
(s_regions st) !! rid = Some r -> r_base r = x -> x mod 4096 = 0 -> 0 < x -> x + 8192 <= alloc_ceiling -> 1 <= n < 2^62 ->
0 <= c_meta_alloc_shift (ctx st) < 2^62 ->
rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (fun ms' => exists m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (x + 4096)) (Z_to_bv 64 0)
(Z_to_bv 64 (c_meta_alloc_shift (ctx st) + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce600) fc None m' (seg_rom rsegs)
/\ rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw)
/\ stk rsegs m' lo (bv_unsigned sp + -64)
/\ rmrep (mm_ok_st st rid n) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce53c) fc None m (seg_rom rsegs)).
Proof.
intros until r. intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
assert (AL : Z.land (x + 4096) 4095 = 0).
{ change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
change (x mod 4096 = 0) with (pgal x) in XAL.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.

st1.
assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.

st1. st1. st1. st1. st1. st1.
replace ((n + -1) * 1) with (n - 1) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.

st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
lazymatch goal with H : rw_cells rsegs ?mX 6566376 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.

st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
- intros y Hy. apply ram_fp_stack. lia.
- intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed.

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1.
Import QTp6.
Import QWTl.Mq5.
Import Q2qa.Mq1 QytA Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq1 QDUx.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 Qv4L.Mqa QdZ1.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := QWTl.Mq5.
Module RA2 := Qv4L.Mqa.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_agree_but_ctx : forall st st' m m',
rmrep st m ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
A2.agree_on m m' RMLOCK 4 -> A2.agree_on m m' RLIBC 0x68 -> A2.agree_on m m' RGOT_SSP 8 -> A2.agree_on m m' RSSP_GUARD 8 -> A2.agree_on m m' RVMLOCK 4 ->
(forall a ar, (s_areas st) !! a = Some ar -> A2.agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> A2.agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> A2.agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
rmrep_ctx st' m' ->
rmrep st' m'.
Proof.
intros st st' m m' (WF & CX & GL & AR & GR & SH) ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGV AGA AGG AGR CX'.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [exact CX'|split; [|split; [|split]]]].
- destruct WF as (RS & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG, ERs. split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA| exact WG].
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply RA2.rrw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G4|]. eapply A2.agree_on_sub; [exact AGS1| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G5|]. eapply A2.agree_on_sub; [exact AGS2| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G6|]. eapply A2.agree_on_sub; [exact AGV| lia| cbn; lia].
- intros a ar Ha. rewrite EA in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
unfold rarea_rep. rewrite !Hconc.
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
rewrite PW. split; [|split].
+ eapply RA2.rrw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
+ intros k Hk. rewrite MC, GM. eapply RA2.rrw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
+ eapply RA2.rrw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
eapply RA2.rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
+ eapply RA2.rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply RA2.rbytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.

#[using="Type"] Lemma rmrep_ctx_mid_agree : forall st st' m m',
rmrep st m -> ctx st' = ctx st \/ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
/\ (forall i, unmap_seq st' i = unmap_seq st i) /\ (forall i, bounces st' i = bounces st i) ->
s_regions st' = s_regions st ->
A2.agree_on m m' (RCTX + 80) 832 ->
u64arr rsegs m' (RCTX + 80) (actives st') /\ u64arr rsegs m' (RCTX + 464) (usages st')
/\ u8arr rsegs m' (RCTX + 848) (unmap_seqs st') /\ u8arr rsegs m' (RCTX + 880) (bouncess st').
Proof.
intros st st' m m' (WF & (C1 & C2 & C3 & C4 & C5 & C6 & C7) & _) HX ER AG.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
assert (E3 : usages st' = usages st).
{ unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st).
{ unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
assert (E5 : bouncess st' = bouncess st).
{ unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
rewrite E2, E3, E4, E5.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold RCTX in *.
split; [|split; [|split]].
- eapply RA2.ru64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.

#[using="Type"] Lemma rarea_in_live : forall st a ar r x, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
intros st a ar r x WF Ha Hr Hx. destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.

#[using="Type"] Lemma rgroup_in_live : forall st b gh r x, rregions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
intros st b gh r x WF Hb Hr Hx. destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

#[using="Type"] Lemma rimage_clear_of_ranges_free st lo n x : s_reserved st = ref_reserved -> ranges_free (live_ranges st) lo n = true ->
0x10000 <= x < 0x645000 -> ~ (lo <= x < lo + n).
Proof.
intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

#[using="Hr"] Lemma rgr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="Type"] Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rgr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
- rewrite lookup_insert_eq in H. left. split; congruence.
- rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
#[using="Type"] Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
#[using="Hr"] Lemma rgr_conc q : conc st' q = conc st q.
Proof.
unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
- rewrite E, rgr_lookup_new, Hr. reflexivity.
- rewrite rgr_lookup_old by exact NE. reflexivity.
Qed.
#[using="RC__ OFF OAL"] Lemma rgr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

#[using="m MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rgr_regions_wf : rregions_wf st'.
Proof.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
split; [exact RS|]. split; [|split; [|split]].
- intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
apply ranges_free_intro. intros b n HI.
pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite RS; exact HI)).
destruct HI as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
- intros q1 r1 q2 r2 H1 H2 NE.
assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
{ intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
- left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
- right. exact D. }
destruct (rgr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rgr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ exact (OLD q2 r2 H2' NE2).
+ destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO).
destruct (decide (fst a = rid)) as [E|NE].
+ exists r'. rewrite E in Hra |- *. rewrite rgr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
cbn [r_base r_len r_kind r']. rewrite rgr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
rewrite LEN in A1. repeat split; try assumption; lia.
+ exists ra. rewrite rgr_lookup_old by exact NE. repeat split; assumption.
- intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
exists rb. rewrite rgr_lookup_old by exact NE. auto.
Qed.

#[using="MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rmrep_grow_region : rmrep st' m.
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH).
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
split; [exact rgr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
replace (ctx_head_cells st') with (ctx_head_cells st) by (unfold ctx_head_cells; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
replace (ctx_tail_cells st') with (ctx_tail_cells st).
2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6| exact C7].
- intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4).
unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
- intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8).
exists w8. rewrite rgr_conc, PW. split; assumption.
- intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
+ exfalso. apply NK. exact Hk.
+ exact (SH q rq H Hk).
Qed.

#[using="Type"] Lemma rptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End GROW.

#[using="Type"] Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
(forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
impl rsegs (at_node rsegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof.
intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec' rsp) as [a|] eqn:E.
- destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
- cbn. apply evt_done. exact I.
Qed.

End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq7.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq3 QQbX.Mq3 Qn9M.Mq0 Qv4L.Mqa.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rzeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
(forall o, 0 <= o < Z.of_nat k -> bytes_at rsegs m (x + o) [b8 0]) -> bytes_at rsegs m x (zeros k).
Proof.
intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
rewrite nth_error_repeat by exact Hi.
destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
rewrite Z.add_0_r in HB. exact HB.
Qed.

#[using="Type"] Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof.
intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
{ change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
rewrite T4064.
destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.

#[using="Type"] Lemma rbig_word_eq rid n : 0 <= n < 2^63 ->
Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof.
intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
replace (n + 4064 + 51) with (n + 4115) by lia.
assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
destruct (Z.lt_ge_cases i 12).
- rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma le4_sxv_succ c : 0 <= c -> le4 (Z_to_bv 64 (bv_unsigned (wz (sxv c)) + 1)) = le4 (wz (u32 (c + 1))).
Proof.
intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
unfold u32. rewrite (QnDM_c1.Mq0.mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[using="Type"] Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof.
intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma rbig_fail1_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
evt rsegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom rsegs)
/\ stk rsegs m lo (bv_unsigned sp))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce6c8) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros FR ST LO SP48.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity| exact ST].
Qed.

#[using="Type"] Lemma rbig_fail2b_walk :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
evt rsegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom rsegs)
/\ stk rsegs m lo (bv_unsigned sp))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce894) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros FR ST LO SP48.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity| exact ST].
Qed.

#[using="Type"] Lemma rbig_fail2a_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
rw_cells rsegs m RMLOCK [C4 (wz 0)] ->
evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xce894) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) xw ndw a2 a3 a4 a5 a6 a7
s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom rsegs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz 0) a1 a2 a3 a4 a5 a6 a7
s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce7bc) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros LK. unfold RMLOCK in *.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
step. step. step.
eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0xce888)) with (Z_to_bv 64 0xce888) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists (a0 a1 : word) m',
ms' = MS (mkR (Z_to_bv 64 0xce7bc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
/\ rmrep st' m'.

#[using="Type"] Lemma rbig_seq_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
(lo n : Z) (st : mstate),
rmrep st m -> 0 <= c_seq (ctx st) < 256 ->
bv_unsigned xw <> 2^64 - 1 ->
rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo -> mem_inv rsegs m ->
evt rsegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce6c8) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR SEQ XNE FR ST LO ILO MI.
pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6 & _) & (_ & NL & _) & _).
unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry, alloc_ceiling in *. unfold ctx_tail_cells in C6.
replace (6566376 + 912) with 6567288 in C6 by reflexivity. replace (6566376 + 848) with 6567224 in US by reflexivity.

step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.

step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.

step. rewrite ?zxb_b8 by lia. step.

assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk rsegs mj lo (bv_unsigned sp + -48) -> mem_inv rsegs mj ->
munch [(6566376 + 848, 6566376 + 880); (6566376 + 912, 6566376 + 913)]%Z m mj -> wmono rsegs m mj ->
evt rsegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 6566368)
(Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce7b4) fc None mj (seg_rom rsegs))).
{ intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j & _) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
replace (6566376 + 912) with 6567288 in C6j by reflexivity.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 6567288) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
raw_store_finishR (6566376 + 912) [b8 ns] FRj STj MUj WMj SOK.

step.
apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. do 3 eexists. split; [reflexivity|].
split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
-
pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
assert (UZ : u8arr rsegs m1 6567224 (zeros 32)).
{ apply (u8arr_of_rw_cells rsegs m1 6567224 32). apply (rw_cells_congr rsegs m1 6567224 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
clear USC.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with MUc : munch _ m m1, WMc : wmono rsegs m m1 |- _ =>
assert (MRz : rmrep stz m1);
[ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| left; unfold RCTX; replace (6566376 + 912) with 6567288 by reflexivity;
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.

step. step.
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX, FRc : rw_cells rsegs ?mX (bv_unsigned sp + -48) _, STc : stk rsegs ?mX _ _, MIc : mem_inv rsegs ?mX |- _ =>
eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^63 - 4097.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="MR TK G0 MSL RR GN AN SHN HC CR NR CLO"] Lemma rbig_succ_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
bv_unsigned gw = G ->
rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a0' a1' : word) m',
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce954) fc None m' (seg_rom rsegs)
/\ munch [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
/\ rmrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce7bc) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
change (meta_word meta0) with 0 in CH.
destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].

destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
assert (HDR : rw_cells rsegs m x [C8 (wz 0); C1 (b8 0)]).
{ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
- cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
apply rzeros_bytes_at; [lia| cbn; unfold alloc_ceiling in XC; lia|].
intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
- cbn. eapply wr_at_sub; [exact XW| lia| lia]. }

pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
rewrite <- HG in CH.
unfold alloc_ceiling, RCTX, RMLOCK in *.

step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.

unfold ctx_head_cells in CX1. rewrite HC in CX1.
pose proof (rw_cells_prefix rsegs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

step. step.

pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl rsegs m) as WMa.
step.
assert (PWX : pw st (Some (rid, 0)) = wz x).
{ unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CHA : rw_cells rsegs mX (conc st g) (meta_cells st (big_metaA rid)));
[ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
| pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
clear MUa WMa CHA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
cbv delta [wz]. step.
set (stA := put_meta g (big_metaA rid) st) in MRA.
destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
{ eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
- unfold RCTX in R1. lia.
- unfold RMLOCK in R2. lia.
- unfold RNEED_LOCKS in R3. lia.
- unfold RPAGE_SIZE in R4. lia.
- change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
destruct (N.eq_dec q rid) as [->|NE].
+ rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- unfold RGOT_SSP in R5. lia.
- unfold RSSP_GUARD in R6. lia. }
clear MRB0 MUb WMb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
{ eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
clear MRB1.

step. step. step. step. step. step.
rewrite (unsigned_lit (n + 4115)) by lia.
assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
step. step. step.
set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CHC : rw_cells rsegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
[ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
| pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
clear MUc WMc CHC MRB.

step. rewrite (sx32_wz_sxv c) by lia. step.

lazymatch goal with H : rw_cells rsegs ?mX 6566376 _ |- _ =>
pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 6566388) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
clear H end.
st1. rewrite le4_swrap_succ by lia.
set (stC := put_meta g (big_meta rid n) stB) in MRC.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
clear MRC.
raw_store_finishR (6566376 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.

step.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [exact MRD| exact TKB].
Qed.
End SUCC.

End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa.
Import QCwx.Mq1 QFqQ.Mq0 QdZ1.Mq3 QQbX.Mq3 Qv4L.Mq7 Qv4L.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
(t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
(forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
0 <= c_mmap_counter (ctx st2) < 2^32 ->
slot_ok st2 g b r idx n ->
(expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 (Some (g, idx))) s' Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce954) fc None m1 (seg_rom rsegs)).

Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st2 m1 -> ticks_ok st2 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> errv = Z_to_bv 64 12 -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 None) s' Q
(MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs)).

#[using="Type"] Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
lo <= a < sp \/ a < alloc_ceiling.
Proof.
intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold RCTX in H. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

#[using="Type"] Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs :
rmrep st m0 -> rmrep st2 m2 ->
rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells rsegs m A cs ->
sp' <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

#[using="Type"] Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof.
intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

#[using="Type"] Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

#[using="Type"] Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
0xe2000 <= a < 0x645000 -> RCTX <= a < RCTX + 928 \/ 0x622dbc <= a < 0x622dc0.
Proof.
intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
/\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
{ intros P. split; intros rid r Hr Ha.
- destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
- destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
-
exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

#[using="Type"] Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B :
rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QWTl.Mq4 QDUx.Mqb.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QdZ1.Mq2 Qv4L.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma testbit_false_ge a n : 0 <= a < 2^n -> 0 <= n -> forall k, n <= k -> Z.testbit a k = false.
Proof.
intros Ha Hn k Hk. destruct (Z.eq_dec a 0) as [->|NE]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|].
assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

#[using="Type"] Lemma lor_lxor_ones64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 ->
Z.lor (Z.lxor a 18446744073709551615) (Z.lxor b 18446744073709551615) = Z.lxor (Z.land a b) 18446744073709551615.
Proof.
intros Ha Hb. change 18446744073709551615 with (Z.ones 64).
apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !Z.lxor_spec, Z.land_spec.
destruct (Z.lt_ge_cases n 64) as [L|G].
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite (testbit_false_ge a 64), (testbit_false_ge b 64) by lia. reflexivity.
Qed.

#[using="Type"] Lemma usage_sub_word u w : 0 <= u < 2^64 -> 0 <= w < 2^64 ->
Z_to_bv 64 (u + Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor w 18446744073709551615))) 18446744073709551584)
= wz (u - (Z.land w 31 + 1)).
Proof.
intros Hu Hw.
assert (HX : 0 <= Z.lxor w 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
rewrite unsigned_lit by lia.
change 18446744073709551584 with (Z.lxor 31 18446744073709551615).
rewrite lor_lxor_ones64 by lia.
assert (HL : 0 <= Z.land w 31 < 32).
{ split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite zb_lxor_ones by lia. unfold wz.
rewrite <- (Z_to_bv_mod64 (u + _)), <- (Z_to_bv_mod64 (u - _)). f_equal.
replace (u + (18446744073709551615 - Z.land w 31)) with ((u - (Z.land w 31 + 1)) + 1 * 2^64) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition rfg_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc W : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a3 a4 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz W) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce1dc) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rntf_fg : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv rsegs m -> meta_slot st g ->
mw_ok mr ->
(m_sizeclass mr < 48 -> 0 <= usage st (m_sizeclass mr) < 2^64) ->
rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rfg_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(fg_usage_st st g) g (m_sizeclass mr) (meta_word mr) fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce1a8) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros mr MR MI MSL MW UR FR FRL ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (meta_word_range mr MW) as MWR.
pose proof MW as (LI & FB & SCR & ML).
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
unfold alloc_ceiling, RCTX in *.
assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
rmeta_chunk MR MSL CH. fold mr in CH.
st1. st1. st1. rewrite MW2. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
clear CH.
unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with false by (symmetry; apply Z.ltb_ge; lia).
apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply rpres_except_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR].
- unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
specialize (UR ltac:(lia)).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (6566376, 6566376 + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (rmrep_usage_read st m (m_sizeclass mr) (wa (RCTX + 464 + 8 * m_sizeclass mr)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
st1. rewrite ?(unsigned_lit (m_sizeclass mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
st1.
replace (wa (6566376 + 464 + 8 * m_sizeclass mr)) with (Z_to_bv 64 (6566376 + m_sizeclass mr * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.

st1. st1. st1.
rewrite (usage_sub_word (usage st (m_sizeclass mr)) (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).

pose proof MR as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (usages st) (m_sizeclass mr) (Z_to_bv 64 (6566376 + m_sizeclass mr * 8 + 464)) USG
ltac:(rewrite usages_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage st mX (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
clear USG.
rraw_store_finish (6566376 + 464 + 8 * m_sizeclass mr) (le8 (wz (usage st (m_sizeclass mr) - (m_last_idx mr + 1)))) FR ST MU WM SOK.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CH' : rw_cells rsegs mX (conc st g) (meta_cells st mr)) end.
{ pose proof (rmrep_meta_chunk _ _ _ MR2 (meta_slot_set_usage _ _ _ _ MSL)) as X.
rewrite conc_set_usage, rec_set_usage in X. fold mr in X.
replace (meta_cells (set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st) mr) with (meta_cells st mr) in X; [exact X|].
unfold meta_cells, pw. rewrite !oconc_set_usage. reflexivity. }
clear CH. unfold meta_cells in CH'.
st1. clear CH'.
apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 Q9Ay.Mqb QDUx.Mqb.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 Qv4L.Mq4 QdZ1.Mq2 Qv4L.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rntf_seq : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc ns lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr ->
sc = m_sizeclass mr -> m_mem mr = Some p -> 0 <= ns < 256 ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (Z_to_bv 64 ns) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce23c) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold alloc_ceiling, RCTX, rntf_frame in *.

st1. rewrite ?(unsigned_lit sc) by lia. st1.

pose proof MR as (_ & (_ & _ & _ & _ & _ & C6 & _) & _).
pose proof (rw_cells_store_ok_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (6566376 + 912)) C6 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq st mX ns MR NS) as MR1; unfold RCTX in MR1 end.
rraw_store_finish (6566376 + 912) [b8 ns] FR ST MU WM SOK.
set (st1 := upd_ctx (set_seq ns) st) in MR1.

st1.
assert (JOIN : forall m2 (a1' : word),
rmrep (seq_st ns sc st) m2 -> mem_inv rsegs m2 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (6566376, 6566376 + 928)] m0 m2 -> wmono rsegs m0 m2 ->
stk rsegs m2 lo (bv_unsigned sp + -96) -> rw_cells rsegs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 rc_canary; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 6566376) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce254) fc None m2 (seg_rom rsegs))).
{ intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); exact MSL).
rmeta_chunk MR2 MS2 CH.
assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.

st1. st1. st1. st1. clear CH.
rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
eapply evt_mono.
{ eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
first [exact MR2 | exact MI2 | exact MS2 | exact S1 | exact FR2 | exact ST2 | unfold alloc_ceiling; lia | lia | idtac].
unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; exact FMF. }
intros ms' PO. unfold rntf_ret_post in PO |- *.
destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR').
do 14 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans.
- apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [exact MU2|exact WM2|].
cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; unfold RCTX; lia].
- eapply rpres_except_mono; [exact PE|]. intros a Ha.
eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try exact Ha; try lia;
unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
split; [eapply wmono_trans; [exact WM2|exact WM']|]. split; [exact MI'|]. split; [exact ST'|exact MR']. }
if_cases K; zify_cond K.
-
assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K).
eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. exact MR1.
- assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }

st1.
pose proof MR1 as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_store_ok rsegs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 (6566376 + (sc + -7) + 848)) US
ltac:(rewrite unmap_seqs_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
clear US.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish (6566376 + 848 + (sc - 7)) [b8 ns] FR ST MU WM SOK.
eapply JOIN; try eassumption.
unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [exact MR2|] end.
unfold upd_ctx. cbn. reflexivity.
Qed.

#[using="Type"] Lemma zeros32_cells : cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] = zeros 32.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma rntf_top : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr ->
sc = m_sizeclass mr -> m_mem mr = Some p -> m_maplen mr <> 0 ->
0 <= c_seq (ctx st) < 256 ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (record_seq sc (step_seq st)) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce1dc) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_maplen _ MW) as M12.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold alloc_ceiling, RCTX, rntf_frame in *.

st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.

pose proof (rmrep_seq_read st m (wa (RCTX + 912)) MR eq_refl) as RDS. unfold RCTX, wa in RDS.
st1. clear RDS. st1.

st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
-
st1.
replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
first [exact MR | exact MI | exact MSL | exact MW | exact HSC | exact Hmem | exact FMF | exact S1 | exact ER | exact ES | exact EG | exact MU | exact WM | exact FR | exact ST | unfold alloc_ceiling; lia].
-
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (rw_cells_of_u8arr rsegs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. unfold RCTX in UB.
replace (6566376 + 848) with 6567224 in UB by reflexivity.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(6566376 + 848, 6566376 + 880)]%Z mX) as MUz; pose proof (wmono_refl rsegs mX) as WMz end.
st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UA' : u8arr rsegs mX (RCTX + 848) (zeros 32))
by (apply (u8arr_of_rw_cells rsegs mX _ 32); unfold RCTX; eapply rw_cells_congr; [| | | exact UB]; [exact zeros32_cells| reflexivity| cbn; tauto]) end.
clear UB.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
{ eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- left. unfold stz. rewrite unmap_seqs_empty. exact UA'.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }

st1. st1.
replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by reflexivity.
replace (conc st p) with (conc stz p) by reflexivity.
change (get_meta_rec st g) with (get_meta_rec stz g).
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
first [exact MRz | assumption | exact MSL | exact MW | exact HSC | exact Hmem | exact S1 | exact ER | exact ES | exact EG | exact FR | exact ST | unfold alloc_ceiling; lia
| apply fm_facts_ctx; [reflexivity| exact FMF] ].
Qed.

End RC__1.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QDUx.Mqb QPjm.Mq3.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 Q98Z.Mq1 QdZ1.Mq2 Qv4L.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0xce208) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdf80) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rntf_nest_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g p base1 g1 : aptr) (ghp gh1 : ghdr) (ar1 : area) (b3 lo8 hi8 off16 lo : Z),
let mr := get_meta_rec st g in
let mr1 := get_meta_rec st g1 in
let idx1 := Z.land b3 31 in
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> mw_ok mr -> m_maplen mr = 0 -> m_mem mr = Some p ->
(s_groups st) !! p = Some ghp ->
(forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
bytes_at rsegs m (conc st p - 4) [b8 0; b8 b3; b8 lo8; b8 hi8] ->
0 <= b3 < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> off16 = lo8 + 256 * hi8 ->
base1 = aadd p (- (UNIT * off16) - UNIT) ->
(s_groups st) !! base1 = Some gh1 -> g_meta gh1 = Some g1 -> meta_slot st g1 -> m_mem mr1 = Some base1 ->
0 <= m_avail mr1 < 2^32 -> 0 <= m_freed mr1 < 2^32 -> 0 <= m_last_idx mr1 < 32 -> 0 <= m_freeable mr1 < 2 ->
0 <= m_sizeclass mr1 < 64 -> 0 <= m_maplen mr1 < 2^40 ->
(s_areas st) !! (area_of g1) = Some ar1 -> a_check ar1 = c_secret (ctx st) -> 0 <= c_secret (ctx st) < 2^64 ->
idx1 <= m_last_idx mr1 -> Z.testbit (m_avail mr1) idx1 = false -> Z.testbit (m_freed mr1) idx1 = false ->
(m_sizeclass mr1 < 48 -> size_class (m_sizeclass mr1) * idx1 <= off16 < size_class (m_sizeclass mr1) * (idx1 + 1)) ->
(48 <= m_sizeclass mr1 -> m_sizeclass mr1 = 63) ->
(m_maplen mr1 <> 0 -> off16 <= m_maplen mr1 * 256 - 1) ->
rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rnest_call_post sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (grp_del st g p) g p (conc st g1) idx1 fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce1dc) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_maplen _ MW) as M12.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).

destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
{ rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
pose proof MS1 as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
assert (Hao : area_of g1 = a).
{ rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
{ rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
unfold alloc_ceiling, RCTX, AREA_HDR, META_SIZE, NSLOTS in *.
assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.

change (frozen (conc st p mod 16 = 0)) in P16m.
change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
clear HGm AAL RBAL RgBAL SpA BbA.
destruct GB as (GB0 & GB1 & GB2 & _). destruct G1B as (G1B0 & G1B1 & G1B2 & _).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.

st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
pose proof (rmrep_ctx_secret_read st mX MR) as RC;
pose proof (bytes_at_read rsegs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
pose proof (bytes_at_read rsegs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
pose proof (bytes_at_read rsegs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
end.
rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
rewrite Hchk in RA. rewrite Hao, (conc_region' st a rg Hrg) in RA. unfold RCTX in RC.
change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.

st1.
eapply evt_cut.
{ eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
(m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
(m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) (c_secret (ctx st))).
all: lazymatch goal with
| |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
| |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
| |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
| |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
| |- ov_read_bytes _ _ (wa 6566376) 8 = _ => exact RC
| |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
| |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
| |- rw_cells _ _ (conc _ _) _ => exact MM
| |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
| |- _ => idtac
end.
all: first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
| lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
replace (ret_pc (Z_to_bv 64 0xce1f4)) with (Z_to_bv 64 0xce1f4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

st1.
unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
st1.

clear CH MM RG RA RC R4 R2.
pose proof MR as (_ & _ & _ & _ & GR0 & _). destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rw_cells_store_ok_at rsegs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
clear RWp.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) ltac:(eassumption) Hp UNK (length_le8 _)) as MR2
end.
rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
apply (rmrep_grp_del_eq st _ g p) in MR2.

st1. st1.
apply evt_done. unfold rnest_call_post. do 14 eexists.
split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
cbv delta [mkR]. unfold RCTX. reflexivity. }
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_group; [exact Hp | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.

#[using="Type"] Lemma rntf_nest_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) (st0 st : mstate) (g : aptr) (lo : Z),
rmrep st m -> mem_inv rsegs m -> meta_slot st g -> fm_facts st g ->
conc st g = conc st0 g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells rsegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt rsegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a0 a1)
(MS (mkR (Z_to_bv 64 0xce208) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st0 g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce208) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in *.
st1. st1. st1.
rewrite <- Hcg.
eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | unfold alloc_ceiling; lia].
Qed.

End RC__1.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_set_bounce : forall st m i v,
rmrep st m -> 0 <= i < 32 ->
rmrep (set_bounce i v st) (write_to_mem m (wa (RCTX + 880 + i)) [b8 v]).
Proof.
intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6 & X7) & _).
pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
apply (u8arr_write rsegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
- right. split; [| rctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.
End RC__1.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.

Ltac rraw_store_finish0 A bs' MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
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

#[using="Type"] Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
conc st q = conc st g -> q = g.
Proof.
intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
- rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
- exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.
End RC__2.

Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; tauto]);
clear MUq WMq CH end.

Ltac rmchunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_regroup : forall st m m' b gh g ai (w8' : byte),
rmrep st m -> (s_groups st) !! b = Some gh ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
munch [(conc st b, conc st b + 9)]%Z m m' -> wmono rsegs m m' ->
rw_cells rsegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
rmrep (put_group b (Some g) ai st) m'.
Proof.
intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
pose proof (rmrep_del_group st m b MR) as MR1.
assert (MR2 : rmrep (del_group b st) m').
{ eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
pose proof (round_up_pg_ge (r_len r)).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
- unfold RCTX in R1. lia.
- unfold RMLOCK in R2. lia.
- unfold RNEED_LOCKS in R3. lia.
- unfold RPAGE_SIZE in R4. lia.
- change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
- unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
rewrite lookup_delete_ne in Hb2 by congruence.
destruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
+ rewrite E, Hr in Hr2. inversion Hr2; subst r2.
assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
+ destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
- change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
destruct (N.eq_dec q (fst b)) as [->|NE].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
- unfold RGOT_SSP in R8. lia.
- unfold RSSP_GUARD in R9. lia. }
rewrite <- put_group_del.
eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

#[using="Type"] Lemma rmrep_set_group_ai : forall st m m' b g ai0 ai (w8' : byte),
rmrep st m -> (s_groups st) !! b = Some (mkGhdr (Some g) ai0) ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
munch [(conc st b, conc st b + 9)]%Z m m' -> wmono rsegs m m' ->
rw_cells rsegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
rmrep (set_group_active_idx b ai st) m'.
Proof.
intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
eapply rmrep_regroup; eauto.
Qed.

#[using="Type"] Lemma rmrep_ctr_byte_read : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
ov_read_bytes rsegs m (wa (RCTX + 12)) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof.
intros st m (_ & (HD & _) & _) CR.
destruct HD as [[_ HB] _]. unfold ctx_head_cells in HB. cbn [cells_bytes cbytes app] in HB.
rewrite (bytes_at_read rsegs m RCTX _ 12 1 HB).
all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
change (Z.to_nat 12) with 12%nat.
unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

End RC__3.
End Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkAv QvVw Q7ap QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QdBa QfYR.
Import QnDM_c1 QDUx Q9Ay.
Import QkAv QvVw Q7ap QvBB.Mq2.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Import QZAa.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Definition SCALBNL : Z := 0xdad78.
Definition COPYSIGNL : Z := 0xdaa68.
Definition FABSL : Z := 0xdad6c.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Lemma testbit_small_high : forall x k i, (0 <= x < 2^k)%Z -> (0 <= k <= i)%Z -> Z.testbit x i = false.
Proof.
intros x k i Hx Hk. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_low_high : forall x y k, (0 <= x < 2^k)%Z -> (0 <= y)%Z -> (0 <= k)%Z -> Z.lor x (y * 2^k) = (x + y * 2^k)%Z.
Proof.
intros x y k Hx Hy Hk. apply lor_disjoint_add.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k).
- rewrite Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
- rewrite (testbit_small_high x k i) by lia. reflexivity.
Qed.

Lemma land_highmask : forall x k, (0 <= x < 2^64)%Z -> (0 <= k < 64)%Z ->
Z.land x (2^64 - 2^k) = (x - x mod 2^k)%Z.
Proof.
intros x k Hx Hk. rewrite <- (zb_shr_shl x k) by lia.
replace (2^64 - 2^k)%Z with (Z.shiftl (Z.ones (64 - k)) k).
2:{ rewrite Z.shiftl_mul_pow2, Z.ones_equiv by lia. rewrite Z.mul_pred_l, <- Z.pow_add_r by lia. replace (64 - k + k)%Z with 64%Z by lia. lia. }
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i k).
- rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
- rewrite !Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - k + k)%Z with i by lia.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
+ rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry. apply (testbit_small_high x 64 i); lia.
Qed.

Lemma land_bit63 : forall x, (0 <= x < 2^64)%Z -> Z.land x 9223372036854775808 = (x - x mod 2^63)%Z.
Proof. intros x Hx. change 9223372036854775808%Z with (2^64 - 2^63)%Z. apply land_highmask; lia. Qed.
Lemma land_m63 : forall x, Z.land x 9223372036854775807 = (x mod 2^63)%Z.
Proof. intros. change 9223372036854775807%Z with (2^63 - 1)%Z. apply zb_land_mask. lia. Qed.
Lemma land_m48 : forall x, Z.land x 281474976710655 = (x mod 2^48)%Z.
Proof. intros. change 281474976710655%Z with (2^48 - 1)%Z. apply zb_land_mask. lia. Qed.

Lemma copysign_hi_eq : forall xh yh, (0 <= xh < 2^64)%Z -> (0 <= yh < 2^64)%Z ->
Z.lor (Z.land (Z.shiftl (Z.lor (Z.land (Z.shiftl (Z.shiftr yh 63) 15) 18446744073709551615)
(Z.shiftr (Z.land (Z.shiftl xh 1) 18446744073709551615) 49)) 48) 18446744073709551615)
(Z.land xh 281474976710655)
= Z.lor (Z.land xh 9223372036854775807) (Z.land yh 9223372036854775808).
Proof.
intros xh yh Hx Hy.
rewrite !land_W64, land_m48, land_m63, land_bit63 by lia.
rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
set (s := (yh / 2^63)%Z). assert (Hs : (0 <= s <= 1)%Z) by (subst s; Z.div_mod_to_equations; lia).
rewrite (Z.mod_small (s * 2^15)) by lia.
set (b := ((xh * 2 ^ 1) mod 2 ^ 64 / 2 ^ 49)%Z). assert (Hb : (0 <= b < 2^15)%Z) by (subst b; Z.div_mod_to_equations; lia).
rewrite (Z.lor_comm (s * 2^15) b), lor_low_high by lia.
rewrite (Z.mod_small ((b + s * 2^15) * 2^48)) by lia.
rewrite (Z.lor_comm ((b + s * 2^15) * 2^48)), lor_low_high by (try (Z.div_mod_to_equations; lia); lia).
replace (yh - yh mod 2^63)%Z with (s * 2^63)%Z by (subst s; Z.div_mod_to_equations; lia).
rewrite lor_low_high by (try (Z.div_mod_to_equations; lia); lia).
subst b s. Z.div_mod_to_equations. lia.
Qed.

Definition leafq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs)
/\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m.

Lemma land63_range : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.land x 0x7fffffffffffffff < 2^64)%Z.
Proof. intros x Hx. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; lia. Qed.

Lemma fabsl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv usegs m ->
evt usegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FABSL) fc None m (seg_rom usegs)).
Proof.
intros until X. intros MI. unfold FABSL.
pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH. pose proof (land63_range (hi64 X) ltac:(lia)) as R63.
zs. zs. zs.
apply evt_done. unfold leafq_post. repeat (lazymatch goal with |- ex _ => eexists end).
unfold m_fabsl. rewrite lo64_mk128, hi64_mk128 by lia.
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma copysignl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
mem_inv usegs m ->
evt usegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom usegs)).
Proof.
intros until Y. intros MI. unfold COPYSIGNL.
pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH. pose proof (lo64_range Y) as RLY. pose proof (hi64_range Y) as RHY.
do 9 zs. zs.
apply evt_done. unfold leafq_post. repeat (lazymatch goal with |- ex _ => eexists end).
unfold m_copysignl. rewrite copysign_hi_eq by lia.
assert (R1 : (0 <= Z.lor (Z.land (hi64 X) 9223372036854775807) (Z.land (hi64 Y) 9223372036854775808) < 2^64)%Z).
{ apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; lia. }
rewrite lo64_mk128, hi64_mk128 by lia.
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma land_m16 : forall x, Z.land x 65535 = (x mod 2^16)%Z.
Proof. intros. change 65535%Z with (2^16 - 1)%Z. apply zb_land_mask. lia. Qed.

Lemma scal_hi_eq : forall n h, (-2^20 <= n < 2^20)%Z -> (0 <= h < 2^64)%Z ->
Z_to_bv 64 (Z.lor (Z.land (Z.shiftl (Z.land n 18446744073709551615) 48) 18446744073709551615) (Z.land h 281474976710655) + 4611404543450677248)
= Z_to_bv 64 (Z.lor (Z.land h 281474976710655) (Z.shiftl (Z.land (16383 + n) 65535) 48)).
Proof.
intros n h Hn Hh. apply Z_to_bv_eqm.
rewrite !land_W64, !land_m48, land_m16, !Z.shiftl_mul_pow2 by lia.
rewrite (Z.lor_comm _ (h mod 2^48)).
replace ((n mod 2 ^ 64 * 2 ^ 48) mod 2 ^ 64)%Z with ((n mod 2^16) * 2^48)%Z by (Z.div_mod_to_equations; nia).
rewrite !lor_low_high by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. nia.
Qed.
Definition scal_reduce (x n : Z) : Z * Z :=
(if 16383 <? n then
let x := f128_mul x C_2P16383 in let n := n - 16383 in
if 16383 <? n then
let x := f128_mul x C_2P16383 in let n := n - 16383 in (x, if 16383 <? n then 16383 else n)
else (x, n)
else if n <? -16382 then
let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in
if n <? -16382 then
let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in (x, if n <? -16382 then -16382 else n)
else (x, n)
else (x, n))%Z.
Definition U1 : Z := f128_of_d (bv_unsigned D_ONE).
Definition scal_u (n : Z) : Z :=
mk128 (Z.lor (Z.land (hi64 U1) 0x0000ffffffffffff) (Z.shiftl (Z.land (0x3fff + n)%Z 0xffff) 48)) (lo64 U1).
Lemma m_scalbnl_eq : forall x n, m_scalbnl x n = f128_mul (fst (scal_reduce x n)) (scal_u (snd (scal_reduce x n))).
Proof.
intros x n. unfold m_scalbnl, scal_reduce, scal_u, U1.
destruct (16383 <? n); [destruct (16383 <? n - 16383); reflexivity|].
destruct (n <? -16382)%Z; [destruct (n + (16382 - 113) <? -16382)%Z; reflexivity|]. reflexivity.
Qed.

Definition scalbnl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 D_ONE F) (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - 112, q)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - 112) q.

Definition scalbnl_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n : Z),
stk usegs m (q - 112) q -> (4096 <= q - 112)%Z -> (q < 2^63)%Z ->
(-2^31 <= n < 2^31)%Z ->
mem_inv usegs m ->
evt usegs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_scalbnl X n) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCALBNL) fc None m (seg_rom usegs)).

Lemma scalbnl_spec : scalbnl_stmt.
Proof.
unfold scalbnl_stmt. intros until n. intros ST Q0 Q1 Hn MI.
pose proof (munch_refl [(q - 112, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH.
rewrite m_scalbnl_eq. unfold SCALBNL.
zs. carve_frame 32%nat ST.
zs. zs. zs. zs. zs. zs.

assert (FIN : forall mf (x1 x10 x11 x12 x13 x14 x15 x16 x17 x5 x6 x7 x28 x29 x30 x31 : word) x' n',
mem_inv usegs mf -> munch [(q - 112, q)]%Z m mf -> wmono usegs m mf ->
stk usegs mf (q - 112) (q + -32) ->
rw_cells usegs mf (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
(-2^20 <= n' < 2^20)%Z ->
fst (scal_reduce X n) = x' -> snd (scal_reduce X n) = n' ->
evt usegs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_mul (fst (scal_reduce X n)) (scal_u (snd (scal_reduce X n)))) m)
(MS (mkR x1 (Z_to_bv 64 (q + -32)) gp tp x5 x6 x7 (Z_to_bv 64 n') (Z_to_bv 64 (hi64 x')) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 x')) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xdae78) fc None mf (seg_rom usegs))).
{ clear MU WM MI ST FR. intros mf x1 x10 x11 x12 x13 x14 x15 x16 x17 x5 x6 x7 x28 x29 x30 x31 x' n' MI MU WM ST FR Rn Ex En.
rewrite Ex, En. pose proof (lo64_range x') as RL'. pose proof (hi64_range x') as RH'.
zs. zs.
zs. callw (eapply extenddftf2_callv; [hyp | lia]).
change 4607182418800017408%Z with (bv_unsigned D_ONE). fold U1.
pose proof (lo64_range U1) as RLU. pose proof (hi64_range U1) as RHU.
do 10 zs.
rewrite (scal_hi_eq n' (hi64 U1)) by lia.
assert (RU : (0 <= Z.lor (Z.land (hi64 U1) 281474976710655) (Z.shiftl (Z.land (16383 + n') 65535) 48) < 2^64)%Z).
{ apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; [apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; lia|]. rewrite Z.shiftl_mul_pow2, land_m16 by lia. Z.div_mod_to_equations. lia. }
replace (Z_to_bv 64 (lo64 U1)) with (Z_to_bv 64 (lo64 (scal_u n'))) by (unfold scal_u; rewrite lo64_mk128 by lia; reflexivity).
replace (Z_to_bv 64 (Z.lor (Z.land (hi64 U1) 281474976710655) (Z.shiftl (Z.land (16383 + n') 65535) 48))) with (Z_to_bv 64 (hi64 (scal_u n')))
by (unfold scal_u; rewrite hi64_mk128 by lia; reflexivity).
zs. callw (eapply multf3_callq; [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
do 6 zs.
match goal with H : stk _ _ _ _ |- _ => rename H into ST2 end. replace (q + -32 - 80)%Z with (q - 112)%Z in ST2 by lia.
release_frame FR ST2 q.
apply evt_done. unfold scalbnl_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp | exact ST2]. }

Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
Ltac decb := repeat match goal with |- context [Z.ltb ?a ?b] =>
first [replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; mlia2) | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; mlia2)] end.
Ltac fin F x n := eapply (F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x n); [hyp | hyp | hyp | hyp | hyp | | unfold scal_reduce; decb; cbn [fst snd]; reflexivity | unfold scal_reduce; decb; cbn [fst snd]; lia]; try mlia2.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  zs. zs. zs. fin FIN X n.
+
zs. zs. zs. zs.
zs. callw (eapply multf3_callq with (X := X) (Y := C_2PM16269); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
set (X1 := f128_mul X C_2PM16269) in *. pose proof (lo64_range X1) as RL1. pose proof (hi64_range X1) as RH1.
zs. zs. zs. (if_cases K3; zify_cond K3; try (rewrite ?signed_of_Z in K3 by lia)).
*  zs. zs. zs. zs. zs. fin FIN X1 (n + 16269)%Z.
* zs. zs. zs. callw (eapply multf3_callq with (X := X1) (Y := C_2PM16269); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
set (X2 := f128_mul X1 C_2PM16269) in *. pose proof (lo64_range X2) as RL2. pose proof (hi64_range X2) as RH2.
zs. zs. zs. zs. zs. (if_cases K4; zify_cond K4; try (rewrite ?signed_of_Z in K4 by lia)).
-- zs. zs. zs. zs. fin FIN X2 (n + 32538)%Z.
-- zs. zs. zs. zs. zs. eapply (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 (-48920 + 32538)%Z); [hyp | hyp | hyp | hyp | hyp | lia | unfold scal_reduce; decb | unfold scal_reduce; decb];
destruct (Z.ltb_spec0 (n + (16382 - 113) + (16382 - 113)) (-16382)); cbn [fst snd]; first [reflexivity | mlia2].
-
zs. zs. zs. zs.
zs. callw (eapply multf3_callq with (X := X) (Y := C_2P16383); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
set (X1 := f128_mul X C_2P16383) in *. pose proof (lo64_range X1) as RL1. pose proof (hi64_range X1) as RH1.
zs. zs. zs. (if_cases K3; zify_cond K3; try (rewrite ?signed_of_Z in K3 by lia)).
+  zs. zs. zs. zs. zs. zs. fin FIN X1 (n - 16383)%Z.
+ zs. zs. zs. callw (eapply multf3_callq with (X := X1) (Y := C_2P16383); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
set (X2 := f128_mul X1 C_2P16383) in *. pose proof (lo64_range X2) as RL2. pose proof (hi64_range X2) as RH2.
zs. zs. zs. zs. zs. (if_cases K4; zify_cond K4; try (rewrite ?signed_of_Z in K4 by lia)).
* zs. zs. zs. zs. fin FIN X2 (n - 32766)%Z.
* zs. zs. zs. zs. zs. eapply (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 (49149 - 32766)%Z); [hyp | hyp | hyp | hyp | hyp | lia | unfold scal_reduce; decb | unfold scal_reduce; decb];
destruct (Z.ltb_spec0 16383 (n - 16383 - 16383)); cbn [fst snd]; first [reflexivity | mlia2].
Qed.

End Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import QeTw Q1BE QvBB.Mq2.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Definition SHLIM : Z := 0xd8958.
Definition SHGETC : Z := 0xd8990.
Definition UFLOW : Z := 0xd5554.
Definition TOREAD : Z := 0xd55e0.
Definition STRING_READ : Z := 0xd4cf0.

Definition got_ssp := 0xe8f90%Z.
Definition ssp_guard := 0x645560%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].

Notation rfj := G.T_rfj.rfj.
Notation mkJ := G.T_rfj.mkJ.
Notation j_flags := G.T_rfj.j_flags.
Notation j_pad0 := G.T_rfj.j_pad0.
Notation j_close := G.T_rfj.j_close.
Notation j_wend := G.T_rfj.j_wend.
Notation j_wpos := G.T_rfj.j_wpos.
Notation j_mbz1 := G.T_rfj.j_mbz1.
Notation j_wbase := G.T_rfj.j_wbase.
Notation j_read := G.T_rfj.j_read.
Notation j_write := G.T_rfj.j_write.
Notation j_seek := G.T_rfj.j_seek.
Notation j_bufsize := G.T_rfj.j_bufsize.
Notation j_prev := G.T_rfj.j_prev.
Notation j_next := G.T_rfj.j_next.
Notation j_fd := G.T_rfj.j_fd.
Notation j_ppid := G.T_rfj.j_ppid.
Notation j_lockcount := G.T_rfj.j_lockcount.
Notation j_mode := G.T_rfj.j_mode.
Notation j_lock := G.T_rfj.j_lock.
Notation j_lbf := G.T_rfj.j_lbf.
Notation j_pad1 := G.T_rfj.j_pad1.
Notation j_cookie := G.T_rfj.j_cookie.
Notation j_off := G.T_rfj.j_off.
Notation j_getln := G.T_rfj.j_getln.
Notation j_mbz2 := G.T_rfj.j_mbz2.
Notation j_pl := G.T_rfj.j_pl.
Notation j_nl := G.T_rfj.j_nl.
Notation j_locale := G.T_rfj.j_locale.

Definition M64 : Z := 18446744073709551615.

Definition rf_rend (T p : Z) (w : bool) (f : shfile) : Z :=
if sh_stdio f then (if w then T + p else T) else M64.

Definition rf_cells (T p : Z) (w : bool) (f : shfile) (J : rfj) : list cell :=
let rend := rf_rend T p w f in
[C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)); C8 (Z_to_bv 64 (- sh_cnt0 f));
C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

Definition rf_cells_raw (T p : Z) (w : bool) (f : shfile) (J : rfj) (she shl shc : word) : list cell :=
let rend := rf_rend T p w f in
[C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
C8 she; C8 shl; C8 shc;
C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

Lemma rf_cells_raw_eq : forall T p w f J,
rf_cells T p w f J = rf_cells_raw T p w f J (Z_to_bv 64 (rf_rend T p w f)) (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. reflexivity. Qed.

Lemma rf_cells_size : forall T p w f J, length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat -> cells_size (rf_cells T p w f J) = 232%nat.
Proof. intros. reflexivity. Qed.

Definition ssJ : rfj :=
mkJ (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 STRING_READ) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 M64) (Z_to_bv 64 M64) (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

Definition RFI (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
sh_ok T txt f /\ (-1 <= c < 256)%Z /\
(sh_shlim_neg f = false -> kmin <= sh_rpos f)%Z /\
(sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
(sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
(w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ /\ 0 <= sh_cnt0 f <= sh_rpos f)%Z.

Definition shlim_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (w : bool) (f : shfile) (J : rfj) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(Fp, Fp + 232)%Z] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' Fp (rf_cells T p w (sh_lim0 f) J).

Definition shlim_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (txt : list Z) (f : shfile) (J : rfj) (she shl shc : word),
rw_cells usegs m Fp (rf_cells_raw T p w f J she shl shc) ->
sh_ok T txt f -> length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat ->
(0 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= p <= zlength txt)%Z ->
mem_inv usegs m ->
evt usegs (shlim_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p w f J m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHLIM) fc None m (seg_rom usegs)).

Ltac show_goal := match goal with |- ?g => idtac g end.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
end.
Lemma sx32_M64 : sx32 (Z_to_bv 64 18446744073709551615) = Z_to_bv 64 18446744073709551615.
Proof. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit by lia. vm_compute. reflexivity. Qed.
Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Lemma shlim_spec : shlim_stmt.
Proof.
unfold shlim_stmt. intros until shc. intros FC OK L0 L1 T0 T1 Hp MI.
pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold rf_cells_raw in FC, B. cbn [cells_size csize Nat.add] in B.
destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold SHLIM.
assert (RR : (0 <= rf_rend T p w f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); [destruct w|]; lia).
unfold M64 in RR. pose_word_ranges.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)); change (Z.b2z (0 <? 0)) with 0%Z in K1; rewrite Z.land_0_l in K1; [clear K1 | exfalso; apply K1; reflexivity].
zs. zs.
apply evt_done. unfold shlim_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold rf_cells, sh_lim0. cbn [sh_rpos sh_cnt0 sh_stdio sh_shlim_neg sh_n sh_buf].
unfold rf_rend in *. cbn [sh_stdio].
replace (- sh_rpos f)%Z with (T - (T + sh_rpos f))%Z by lia. hyp.
Qed.

Definition zero4 : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition w0 : word := Z_to_bv 64 0.

Definition ss_cells (T rpos rend : Z) (mode : word) (cookie shend : Z) (shl shc : word) : list cell :=
[C4 w0; CB 4 zero4; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend);
C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C8 (Z_to_bv 64 STRING_READ); C8 w0; C8 w0;
C8 (Z_to_bv 64 T); C8 w0; C8 w0; C8 w0; C4 w0; C4 w0; C8 w0;
C4 mode; C4 (Z_to_bv 64 M64); C4 w0; CB 4 zero4;
C8 (Z_to_bv 64 cookie); C8 w0; C8 w0; C8 w0;
C8 (Z_to_bv 64 shend); C8 shl; C8 shc;
C8 w0; C8 w0; C8 w0].

Lemma rf_cells_ss : forall T p w f, sh_stdio f = true ->
rf_cells T p w f ssJ = ss_cells T (T + sh_rpos f) (rf_rend T p w f) (Z_to_bv 64 M64) (rf_rend T p w f) (rf_rend T p w f)
(Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. intros T p w f ST. unfold rf_cells, ss_cells. rewrite ST. reflexivity. Qed.

Definition toread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T cookie shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - 16, q); (Fp, Fp + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - 16) (q)
/\ rw_cells usegs m' Fp (ss_cells T T T (Z_to_bv 64 M64) cookie shend shl shc).

Definition toread_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T rpos rend cookie shend : Z) (mode shl shc : word),
rw_cells usegs m Fp (ss_cells T rpos rend mode cookie shend shl shc) ->
(mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
(0 <= T /\ T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= cookie < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
stk usegs m (q - 16) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv usegs m ->
evt usegs (toread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T cookie shend shl shc m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TOREAD) fc None m (seg_rom usegs)).

Lemma toread_spec : toread_stmt.
Proof.
unfold toread_stmt. intros until shc. intros FC Hmode RT Rrp Rre Rck Rsh ST SPLO SPF SPF2 Q0 Q1 MI.
pose proof (munch_refl [(q - 16, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold ss_cells, w0 in FC. cbn [cells_size csize Nat.add] in B.
unfold TOREAD, M64 in *. pose_word_ranges.
zs. carve_frame 16%nat ST.
zs. zs. zs.
destruct Hmode as [-> | ->].
all: zs; rewrite ?(sx32_small 0), ?sx32_M64 by lia.
all: do 6 zs.
all: (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
all: zs; rewrite (zx32_lit 0) by lia.
all: do 5 zs.
all: (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ exfalso; lia | ]).
all: do 8 zs.
all: zs; zs; zs; zs.
all: release_frame FR ST q.
all: apply evt_done; unfold toread_post; repeat (lazymatch goal with |- ex _ => eexists end).
all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|].
all: unfold ss_cells, w0; replace (T + 0)%Z with T by lia; hyp.
Qed.

End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QBpX.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 QDUx.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QnOf QdZ1.Mq7 QQbX.Mq5 QdZ1.Mq5 Qv4L.Mqc.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_disp_fin : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (p : aptr) (r : region),
rmrep st m -> c_avail_meta_area_count (ctx st) <> 0 -> 0 <= c_avail_meta_area_count (ctx st) < 2^64 ->
c_avail_meta_areas (ctx st) = Some p -> (s_regions st) !! (fst p) = Some r -> pgal (snd p) -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0cc4) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b24) fc None m (seg_rom usegs)).
Proof.
intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite AMA in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). unfold alloc_ceiling in RBC.
pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
assert (AL : Z.land (conc st p) 4095 = 0).
{ rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
assert (PB : 0 <= conc st p < 2^64) by lia.
clear RBAL RU RBC RL0 WR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.

st1. st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
rewrite CF.

st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
st1. st1.

st1. st1. rewrite ?AL, ?AL'. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma ram_to_mprotect : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (P : Z),
evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xd0cd4) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P)
(Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0cc4) fc None m (seg_rom usegs)).
Proof.
intros.

st1. st1. st1. st1.
apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.

#[using="Type"] Lemma ram_mp_ok0 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte),
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0c34) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0cd4) fc None m (seg_rom usegs)).
Proof.
intros.
st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma ram_mp_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo e : Z) (st : mstate),
rmrep st m -> mem_inv usegs m -> tp = Z_to_bv 64 0x625520 ->
rw_cells usegs m (errno_addr tp) [C4 (Z_to_bv 64 e)] -> 1 <= e <= 4095 -> e <> 38 ->
rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (fun ms' => ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0) ms'
/\ rw_cells usegs (ms_mem ms') (errno_addr tp) [C4 (Z_to_bv 64 e)])
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0cd4) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
subst tp. rewrite (unsigned_lit 0x625520) in * by lia. change (6444320 + -164) with 6444156 in *.
change (Z_to_bv 64 e) with (wz e) in ERR.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.

st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.

st1. st1. st1. st1.

st1. rewrite sx32_wz by lia. st1. st1.
assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
rewrite CF; clear CF.

st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. split.
- unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
- cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed.

End RC__1.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QBpX.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 Q9Ay.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QnOf QdZ1.Mq7 QQbX.Mq5 QdZ1.Mq5 Qv4L.Mqc.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_disp_dead : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkDead ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0bd4) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b24) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6576296 + 912) with 6577208 in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.

st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma ram_to_mmap : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> 0 <= c_meta_alloc_shift (ctx st) <= 40 ->
let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xd0c00) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n)
(Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0bd4) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR SH n.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
unfold RCTX, RMLOCK, RSSP_GUARD in *.

st1. st1. st1.
rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
{ rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }

st1. st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.

#[using="Type"] Lemma ram_mm_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate),
rmrep st m -> mem_inv usegs m ->
rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0c00) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.

st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed.

#[using="Type"] Lemma ram_mm_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo x n : Z) (st0 st : mstate) (rid : N) (r : region),
rmrep st m -> mem_inv usegs m -> (forall a, ram_fp st0 lo (bv_unsigned sp) a -> ram_fp st lo (bv_unsigned sp) a) ->
(s_regions st) !! rid = Some r -> r_base r = x -> x mod 4096 = 0 -> 0 < x -> x + 8192 <= alloc_ceiling -> 1 <= n < 2^62 ->
0 <= c_meta_alloc_shift (ctx st) < 2^62 ->
rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (x + 4096)) (Z_to_bv 64 0)
(Z_to_bv 64 (c_meta_alloc_shift (ctx st) + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0cc4) fc None m' (seg_rom usegs)
/\ rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
/\ rw_cells usegs m' (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw)
/\ stk usegs m' lo (bv_unsigned sp + -64)
/\ rmrep (mm_ok_st st rid n) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0c00) fc None m (seg_rom usegs)).
Proof.
intros until r. intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
assert (AL : Z.land (x + 4096) 4095 = 0).
{ change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
change (x mod 4096 = 0) with (pgal x) in XAL.
unfold alloc_ceiling, RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.

st1.
assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.

st1. st1. st1. st1. st1. st1.
replace ((n + -1) * 1) with (n - 1) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.

st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
lazymatch goal with H : rw_cells usegs ?mX 6576296 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc.

st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
- intros y Hy. apply ram_fp_stack. lia.
- intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed.

End RC__1.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1.
Import QBpX.
Import QWTl.Mq5.
Import Q2qa.Mq1 QytA Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq1 QDUx.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq QkLq.Mq3 Qv4L.Mqk QdZ1.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := QWTl.Mq5.
Module RA2 := Qv4L.Mqk.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_agree_but_ctx : forall st st' m m',
rmrep st m ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
A2.agree_on m m' RMLOCK 4 -> A2.agree_on m m' RLIBC 0x68 -> A2.agree_on m m' RGOT_SSP 8 -> A2.agree_on m m' RSSP_GUARD 8 -> A2.agree_on m m' RVMLOCK 4 ->
(forall a ar, (s_areas st) !! a = Some ar -> A2.agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> A2.agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> A2.agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
rmrep_ctx st' m' ->
rmrep st' m'.
Proof.
intros st st' m m' (WF & CX & GL & AR & GR & SH) ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGV AGA AGG AGR CX'.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [exact CX'|split; [|split; [|split]]]].
- destruct WF as (RS & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG, ERs. split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA| exact WG].
- destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
split; [|split; [|split; [|split; [|split]]]].
+ eapply RA2.rrw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G4|]. eapply A2.agree_on_sub; [exact AGS1| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G5|]. eapply A2.agree_on_sub; [exact AGS2| lia| cbn; lia].
+ eapply RA2.rrw_cells_agree; [exact G6|]. eapply A2.agree_on_sub; [exact AGV| lia| cbn; lia].
- intros a ar Ha. rewrite EA in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
unfold rarea_rep. rewrite !Hconc.
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
rewrite PW. split; [|split].
+ eapply RA2.rrw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
+ intros k Hk. rewrite MC, GM. eapply RA2.rrw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
+ eapply RA2.rrw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
eapply RA2.rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
+ eapply RA2.rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply RA2.rbytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.

#[using="Type"] Lemma rmrep_ctx_mid_agree : forall st st' m m',
rmrep st m -> ctx st' = ctx st \/ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
/\ (forall i, unmap_seq st' i = unmap_seq st i) /\ (forall i, bounces st' i = bounces st i) ->
s_regions st' = s_regions st ->
A2.agree_on m m' (RCTX + 80) 832 ->
u64arr usegs m' (RCTX + 80) (actives st') /\ u64arr usegs m' (RCTX + 464) (usages st')
/\ u8arr usegs m' (RCTX + 848) (unmap_seqs st') /\ u8arr usegs m' (RCTX + 880) (bouncess st').
Proof.
intros st st' m m' (WF & (C1 & C2 & C3 & C4 & C5 & C6 & C7) & _) HX ER AG.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
assert (E3 : usages st' = usages st).
{ unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st).
{ unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
assert (E5 : bouncess st' = bouncess st).
{ unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
rewrite E2, E3, E4, E5.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold RCTX in *.
split; [|split; [|split]].
- eapply RA2.ru64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
- eapply RA2.ru8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.

#[using="Type"] Lemma rarea_in_live : forall st a ar r x, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
intros st a ar r x WF Ha Hr Hx. destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.

#[using="Type"] Lemma rgroup_in_live : forall st b gh r x, rregions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
intros st b gh r x WF Hb Hr Hx. destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

#[using="Type"] Lemma rimage_clear_of_ranges_free st lo n x : s_reserved st = ref_reserved -> ranges_free (live_ranges st) lo n = true ->
0x10000 <= x < 0x647000 -> ~ (lo <= x < lo + n).
Proof.
intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

#[using="Hr"] Lemma rgr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="Type"] Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rgr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
- rewrite lookup_insert_eq in H. left. split; congruence.
- rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
#[using="Type"] Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
#[using="Hr"] Lemma rgr_conc q : conc st' q = conc st q.
Proof.
unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
- rewrite E, rgr_lookup_new, Hr. reflexivity.
- rewrite rgr_lookup_old by exact NE. reflexivity.
Qed.
#[using="RC__ OFF OAL"] Lemma rgr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

#[using="m MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rgr_regions_wf : rregions_wf st'.
Proof.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
split; [exact RS|]. split; [|split; [|split]].
- intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
apply ranges_free_intro. intros b n HI.
pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite RS; exact HI)).
destruct HI as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
- intros q1 r1 q2 r2 H1 H2 NE.
assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
{ intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
- left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
- right. exact D. }
destruct (rgr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rgr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ exact (OLD q2 r2 H2' NE2).
+ destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO).
destruct (decide (fst a = rid)) as [E|NE].
+ exists r'. rewrite E in Hra |- *. rewrite rgr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
cbn [r_base r_len r_kind r']. rewrite rgr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
rewrite LEN in A1. repeat split; try assumption; lia.
+ exists ra. rewrite rgr_lookup_old by exact NE. repeat split; assumption.
- intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
exists rb. rewrite rgr_lookup_old by exact NE. auto.
Qed.

#[using="MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rmrep_grow_region : rmrep st' m.
Proof.
pose proof MR as (WF & CX & GL & AR & GR & SH).
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
split; [exact rgr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold rmrep_ctx.
replace (ctx_head_cells st') with (ctx_head_cells st) by (unfold ctx_head_cells; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
replace (ctx_tail_cells st') with (ctx_tail_cells st).
2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6| exact C7].
- intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4).
unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
- intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8).
exists w8. rewrite rgr_conc, PW. split; assumption.
- intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
+ exfalso. apply NK. exact Hk.
+ exact (SH q rq H Hk).
Qed.

#[using="Type"] Lemma rptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End GROW.

#[using="Type"] Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
impl usegs (at_node usegs) (enode n dec) (epost P) ms ->
(forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
impl usegs (at_node usegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof.
intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec' rsp) as [a|] eqn:E.
- destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
- cbn. apply evt_done. exact I.
Qed.

End RC__1.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq7.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QnOf QdZ1 QQbX Qn9M Qv4L.Mqk.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write usegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write usegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv usegs mX |- _ =>
apply (mem_inv_store usegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rzeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
(forall o, 0 <= o < Z.of_nat k -> bytes_at usegs m (x + o) [b8 0]) -> bytes_at usegs m x (zeros k).
Proof.
intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
rewrite nth_error_repeat by exact Hi.
destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
rewrite Z.add_0_r in HB. exact HB.
Qed.

#[using="Type"] Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof.
intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
{ change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
rewrite T4064.
destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.

#[using="Type"] Lemma rbig_word_eq rid n : 0 <= n < 2^63 ->
Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof.
intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
replace (n + 4064 + 51) with (n + 4115) by lia.
assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
destruct (Z.lt_ge_cases i 12).
- rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma le4_sxv_succ c : 0 <= c -> le4 (Z_to_bv 64 (bv_unsigned (wz (sxv c)) + 1)) = le4 (wz (u32 (c + 1))).
Proof.
intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
unfold u32. rewrite (QnDM_c1.Mq0.mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[using="Type"] Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof.
intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma rbig_fail1_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom usegs)
/\ stk usegs m lo (bv_unsigned sp))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0d8c) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros FR ST LO SP48.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity| exact ST].
Qed.

#[using="Type"] Lemma rbig_fail2b_walk :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom usegs)
/\ stk usegs m lo (bv_unsigned sp))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0f58) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros FR ST LO SP48.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity| exact ST].
Qed.

#[using="Type"] Lemma rbig_fail2a_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
rw_cells usegs m RMLOCK [C4 (wz 0)] ->
evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xd0f58) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) xw ndw a2 a3 a4 a5 a6 a7
s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom usegs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz 0) a1 a2 a3 a4 a5 a6 a7
s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0e80) fc None m (seg_rom usegs)).
Proof.
intros until m. intros LK. unfold RMLOCK in *.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
step. step. step.
eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0xd0f4c)) with (Z_to_bv 64 0xd0f4c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists (a0 a1 : word) m',
ms' = MS (mkR (Z_to_bv 64 0xd0e80) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
/\ rmrep st' m'.

#[using="Type"] Lemma rbig_seq_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
(lo n : Z) (st : mstate),
rmrep st m -> 0 <= c_seq (ctx st) < 256 ->
bv_unsigned xw <> 2^64 - 1 ->
rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo -> mem_inv usegs m ->
evt usegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0d8c) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR SEQ XNE FR ST LO ILO MI.
pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6 & _) & (_ & NL & _) & _).
unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry, alloc_ceiling in *. unfold ctx_tail_cells in C6.
replace (6576296 + 912) with 6577208 in C6 by reflexivity. replace (6576296 + 848) with 6577144 in US by reflexivity.

step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.

step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.

step. rewrite ?zxb_b8 by lia. step.

assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk usegs mj lo (bv_unsigned sp + -48) -> mem_inv usegs mj ->
munch [(6576296 + 848, 6576296 + 880); (6576296 + 912, 6576296 + 913)]%Z m mj -> wmono usegs m mj ->
evt usegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 6576288)
(Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0e78) fc None mj (seg_rom usegs))).
{ intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j & _) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
replace (6576296 + 912) with 6577208 in C6j by reflexivity.
pose proof (rw_cells_store_ok_at usegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 6577208) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
raw_store_finishR (6576296 + 912) [b8 ns] FRj STj MUj WMj SOK.

step.
apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. do 3 eexists. split; [reflexivity|].
split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
-
pose proof (rw_cells_of_u8arr usegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
assert (UZ : u8arr usegs m1 6577144 (zeros 32)).
{ apply (u8arr_of_rw_cells usegs m1 6577144 32). apply (rw_cells_congr usegs m1 6577144 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
clear USC.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with MUc : munch _ m m1, WMc : wmono usegs m m1 |- _ =>
assert (MRz : rmrep stz m1);
[ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
| left; unfold RCTX; replace (6576296 + 912) with 6577208 by reflexivity;
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.

step. step.
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono usegs m ?mX, FRc : rw_cells usegs ?mX (bv_unsigned sp + -48) _, STc : stk usegs ?mX _ _, MIc : mem_inv usegs ?mX |- _ =>
eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^63 - 4097.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="MR TK G0 MSL RR GN AN SHN HC CR NR CLO"] Lemma rbig_succ_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
bv_unsigned gw = G ->
rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a0' a1' : word) m',
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1018) fc None m' (seg_rom usegs)
/\ munch [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
/\ rmrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0e80) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
change (meta_word meta0) with 0 in CH.
destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].

destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
assert (HDR : rw_cells usegs m x [C8 (wz 0); C1 (b8 0)]).
{ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
- cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
apply rzeros_bytes_at; [lia| cbn; unfold alloc_ceiling in XC; lia|].
intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
- cbn. eapply wr_at_sub; [exact XW| lia| lia]. }

pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
rewrite <- HG in CH.
unfold alloc_ceiling, RCTX, RMLOCK in *.

step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.

unfold ctx_head_cells in CX1. rewrite HC in CX1.
pose proof (rw_cells_prefix usegs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

step. step.

pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl usegs m) as WMa.
step.
assert (PWX : pw st (Some (rid, 0)) = wz x).
{ unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CHA : rw_cells usegs mX (conc st g) (meta_cells st (big_metaA rid)));
[ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
| pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
clear MUa WMa CHA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl usegs mX) as WMb end.
cbv delta [wz]. step.
set (stA := put_meta g (big_metaA rid) st) in MRA.
destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
{ eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
- unfold RCTX in R1. lia.
- unfold RMLOCK in R2. lia.
- unfold RNEED_LOCKS in R3. lia.
- unfold RPAGE_SIZE in R4. lia.
- change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
destruct (N.eq_dec q rid) as [->|NE].
+ rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
- unfold RGOT_SSP in R5. lia.
- unfold RSSP_GUARD in R6. lia. }
clear MRB0 MUb WMb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
{ eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
clear MRB1.

step. step. step. step. step. step.
rewrite (unsigned_lit (n + 4115)) by lia.
assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
step. step. step.
set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CHC : rw_cells usegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
[ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
| pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
clear MUc WMc CHC MRB.

step. rewrite (sx32_wz_sxv c) by lia. step.

lazymatch goal with H : rw_cells usegs ?mX 6576296 _ |- _ =>
pose proof (rw_cells_store_ok_at usegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 6576308) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
clear H end.
st1. rewrite le4_swrap_succ by lia.
set (stC := put_meta g (big_meta rid n) stB) in MRC.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
clear MRC.
raw_store_finishR (6576296 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.

step.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [exact MRD| exact TKB].
Qed.
End SUCC.

End RC__1.
End Mqh.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa.
Import QCwx.Mq3 QFqQ.Mq1 QdZ1 QQbX Qv4L.Mqi Qv4L.Mqb.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
(t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv usegs m1 ->
stk usegs m1 lo (bv_unsigned sp + -48) ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
(forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
0 <= c_mmap_counter (ctx st2) < 2^32 ->
slot_ok st2 g b r idx n ->
(expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 (Some (g, idx))) s' Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1018) fc None m1 (seg_rom usegs)).

Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st2 m1 -> ticks_ok st2 -> mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp) ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> errv = Z_to_bv 64 12 -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 None) s' Q
(MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom usegs)).

#[using="Type"] Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
lo <= a < sp \/ a < alloc_ceiling.
Proof.
intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold RCTX in H. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

#[using="Type"] Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs :
rmrep st m0 -> rmrep st2 m2 ->
rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells usegs m A cs ->
sp' <= A -> alloc_ceiling <= A -> rw_cells usegs m' A cs.
Proof.
intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

#[using="Type"] Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof.
intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

#[using="Type"] Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

#[using="Type"] Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
0xe4000 <= a < 0x647000 -> RCTX <= a < RCTX + 928 \/ 0x62547c <= a < 0x625480.
Proof.
intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
/\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
{ intros P. split; intros rid r Hr Ha.
- destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
- destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
-
exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

#[using="Type"] Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B :
rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

End RC__1.
End Mqi.

Module Mqj.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QWTl.Mq4 QDUx.Mqb.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QdZ1.Mq7 Qv4L.Mqj.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma testbit_false_ge a n : 0 <= a < 2^n -> 0 <= n -> forall k, n <= k -> Z.testbit a k = false.
Proof.
intros Ha Hn k Hk. destruct (Z.eq_dec a 0) as [->|NE]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|].
assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

#[using="Type"] Lemma lor_lxor_ones64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 ->
Z.lor (Z.lxor a 18446744073709551615) (Z.lxor b 18446744073709551615) = Z.lxor (Z.land a b) 18446744073709551615.
Proof.
intros Ha Hb. change 18446744073709551615 with (Z.ones 64).
apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !Z.lxor_spec, Z.land_spec.
destruct (Z.lt_ge_cases n 64) as [L|G].
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite (testbit_false_ge a 64), (testbit_false_ge b 64) by lia. reflexivity.
Qed.

#[using="Type"] Lemma usage_sub_word u w : 0 <= u < 2^64 -> 0 <= w < 2^64 ->
Z_to_bv 64 (u + Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor w 18446744073709551615))) 18446744073709551584)
= wz (u - (Z.land w 31 + 1)).
Proof.
intros Hu Hw.
assert (HX : 0 <= Z.lxor w 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
rewrite unsigned_lit by lia.
change 18446744073709551584 with (Z.lxor 31 18446744073709551615).
rewrite lor_lxor_ones64 by lia.
assert (HL : 0 <= Z.land w 31 < 32).
{ split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite zb_lxor_ones by lia. unfold wz.
rewrite <- (Z_to_bv_mod64 (u + _)), <- (Z_to_bv_mod64 (u - _)). f_equal.
replace (u + (18446744073709551615 - Z.land w 31)) with ((u - (Z.land w 31 + 1)) + 1 * 2^64) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition rfg_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc W : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a3 a4 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz W) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd08a0) fc None m' (seg_rom usegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -96)
/\ rw_cells usegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rntf_fg : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
mw_ok mr ->
(m_sizeclass mr < 48 -> 0 <= usage st (m_sizeclass mr) < 2^64) ->
rw_cells usegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rfg_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(fg_usage_st st g) g (m_sizeclass mr) (meta_word mr) fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd086c) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros mr MR MI MSL MW UR FR FRL ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (meta_word_range mr MW) as MWR.
pose proof MW as (LI & FB & SCR & ML).
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
unfold alloc_ceiling, RCTX in *.
assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
rmeta_chunk MR MSL CH. fold mr in CH.
st1. st1. st1. rewrite MW2. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
clear CH.
unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with false by (symmetry; apply Z.ltb_ge; lia).
apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split; [apply rpres_except_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR].
- unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
specialize (UR ltac:(lia)).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (6576296, 6576296 + 928)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (rmrep_usage_read st m (m_sizeclass mr) (wa (RCTX + 464 + 8 * m_sizeclass mr)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
st1. rewrite ?(unsigned_lit (m_sizeclass mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
st1.
replace (wa (6576296 + 464 + 8 * m_sizeclass mr)) with (Z_to_bv 64 (6576296 + m_sizeclass mr * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.

st1. st1. st1.
rewrite (usage_sub_word (usage st (m_sizeclass mr)) (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).

pose proof MR as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok usegs _ _ (usages st) (m_sizeclass mr) (Z_to_bv 64 (6576296 + m_sizeclass mr * 8 + 464)) USG
ltac:(rewrite usages_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage st mX (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
clear USG.
rraw_store_finish (6576296 + 464 + 8 * m_sizeclass mr) (le8 (wz (usage st (m_sizeclass mr) - (m_last_idx mr + 1)))) FR ST MU WM SOK.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CH' : rw_cells usegs mX (conc st g) (meta_cells st mr)) end.
{ pose proof (rmrep_meta_chunk _ _ _ MR2 (meta_slot_set_usage _ _ _ _ MSL)) as X.
rewrite conc_set_usage, rec_set_usage in X. fold mr in X.
replace (meta_cells (set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st) mr) with (meta_cells st mr) in X; [exact X|].
unfold meta_cells, pw. rewrite !oconc_set_usage. reflexivity. }
clear CH. unfold meta_cells in CH'.
st1. clear CH'.
apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ apply rfree_fp_ctx. unfold RCTX. lia. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

End RC__1.
End Mqj.

Module Mqk.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 Q9Ay.Mqb QDUx.Mqb.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 Qv4L.Mqf QdZ1.Mq7 Qv4L.Mqj.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rntf_seq : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc ns lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv usegs m -> meta_slot st g -> mw_ok mr ->
sc = m_sizeclass mr -> m_mem mr = Some p -> 0 <= ns < 256 ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono usegs m0 m ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (Z_to_bv 64 ns) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0900) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold alloc_ceiling, RCTX, rntf_frame in *.

st1. rewrite ?(unsigned_lit sc) by lia. st1.

pose proof MR as (_ & (_ & _ & _ & _ & _ & C6 & _) & _).
pose proof (rw_cells_store_ok_at usegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (6576296 + 912)) C6 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq st mX ns MR NS) as MR1; unfold RCTX in MR1 end.
rraw_store_finish (6576296 + 912) [b8 ns] FR ST MU WM SOK.
set (st1 := upd_ctx (set_seq ns) st) in MR1.

st1.
assert (JOIN : forall m2 (a1' : word),
rmrep (seq_st ns sc st) m2 -> mem_inv usegs m2 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (6576296, 6576296 + 928)] m0 m2 -> wmono usegs m0 m2 ->
stk usegs m2 lo (bv_unsigned sp + -96) -> rw_cells usegs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 rc_canary; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 6576296) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0918) fc None m2 (seg_rom usegs))).
{ intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); exact MSL).
rmeta_chunk MR2 MS2 CH.
assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.

st1. st1. st1. st1. clear CH.
rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
eapply evt_mono.
{ eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
first [exact MR2 | exact MI2 | exact MS2 | exact S1 | exact FR2 | exact ST2 | unfold alloc_ceiling; lia | lia | idtac].
unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; exact FMF. }
intros ms' PO. unfold rntf_ret_post in PO |- *.
destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR').
do 14 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans.
- apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [exact MU2|exact WM2|].
cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; unfold RCTX; lia].
- eapply rpres_except_mono; [exact PE|]. intros a Ha.
eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try exact Ha; try lia;
unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
split; [eapply wmono_trans; [exact WM2|exact WM']|]. split; [exact MI'|]. split; [exact ST'|exact MR']. }
if_cases K; zify_cond K.
-
assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K).
eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. exact MR1.
- assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }

st1.
pose proof MR1 as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_store_ok usegs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 (6576296 + (sc + -7) + 848)) US
ltac:(rewrite unmap_seqs_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
clear US.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish (6576296 + 848 + (sc - 7)) [b8 ns] FR ST MU WM SOK.
eapply JOIN; try eassumption.
unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [exact MR2|] end.
unfold upd_ctx. cbn. reflexivity.
Qed.

#[using="Type"] Lemma zeros32_cells : cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] = zeros 32.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma rntf_top : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv usegs m -> meta_slot st g -> mw_ok mr ->
sc = m_sizeclass mr -> m_mem mr = Some p -> m_maplen mr <> 0 ->
0 <= c_seq (ctx st) < 256 ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)] m0 m -> wmono usegs m0 m ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (record_seq sc (step_seq st)) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd08a0) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_maplen _ MW) as M12.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold alloc_ceiling, RCTX, rntf_frame in *.

st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.

pose proof (rmrep_seq_read st m (wa (RCTX + 912)) MR eq_refl) as RDS. unfold RCTX, wa in RDS.
st1. clear RDS. st1.

st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
-
st1.
replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
first [exact MR | exact MI | exact MSL | exact MW | exact HSC | exact Hmem | exact FMF | exact S1 | exact ER | exact ES | exact EG | exact MU | exact WM | exact FR | exact ST | unfold alloc_ceiling; lia].
-
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (rw_cells_of_u8arr usegs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. unfold RCTX in UB.
replace (6576296 + 848) with 6577144 in UB by reflexivity.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(6576296 + 848, 6576296 + 880)]%Z mX) as MUz; pose proof (wmono_refl usegs mX) as WMz end.
st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UA' : u8arr usegs mX (RCTX + 848) (zeros 32))
by (apply (u8arr_of_rw_cells usegs mX _ 32); unfold RCTX; eapply rw_cells_congr; [| | | exact UB]; [exact zeros32_cells| reflexivity| cbn; tauto]) end.
clear UB.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
{ eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- left. unfold stz. rewrite unmap_seqs_empty. exact UA'.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }

st1. st1.
replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by reflexivity.
replace (conc st p) with (conc stz p) by reflexivity.
change (get_meta_rec st g) with (get_meta_rec stz g).
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
first [exact MRz | assumption | exact MSL | exact MW | exact HSC | exact Hmem | exact S1 | exact ER | exact ES | exact EG | exact FR | exact ST | unfold alloc_ceiling; lia
| apply fm_facts_ctx; [reflexivity| exact FMF] ].
Qed.

End RC__1.
End Mqk.

Module Mql.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QDUx.Mqb QPjm.Mq3.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 Q98Z.Mq4 QdZ1.Mq7 Qv4L.Mqj.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0xd08cc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0644) fc None m' (seg_rom usegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -96)
/\ rw_cells usegs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="Type"] Lemma rntf_nest_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g p base1 g1 : aptr) (ghp gh1 : ghdr) (ar1 : area) (b3 lo8 hi8 off16 lo : Z),
let mr := get_meta_rec st g in
let mr1 := get_meta_rec st g1 in
let idx1 := Z.land b3 31 in
rmrep st m -> mem_inv usegs m -> meta_slot st g -> mw_ok mr -> m_maplen mr = 0 -> m_mem mr = Some p ->
(s_groups st) !! p = Some ghp ->
(forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
bytes_at usegs m (conc st p - 4) [b8 0; b8 b3; b8 lo8; b8 hi8] ->
0 <= b3 < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> off16 = lo8 + 256 * hi8 ->
base1 = aadd p (- (UNIT * off16) - UNIT) ->
(s_groups st) !! base1 = Some gh1 -> g_meta gh1 = Some g1 -> meta_slot st g1 -> m_mem mr1 = Some base1 ->
0 <= m_avail mr1 < 2^32 -> 0 <= m_freed mr1 < 2^32 -> 0 <= m_last_idx mr1 < 32 -> 0 <= m_freeable mr1 < 2 ->
0 <= m_sizeclass mr1 < 64 -> 0 <= m_maplen mr1 < 2^40 ->
(s_areas st) !! (area_of g1) = Some ar1 -> a_check ar1 = c_secret (ctx st) -> 0 <= c_secret (ctx st) < 2^64 ->
idx1 <= m_last_idx mr1 -> Z.testbit (m_avail mr1) idx1 = false -> Z.testbit (m_freed mr1) idx1 = false ->
(m_sizeclass mr1 < 48 -> size_class (m_sizeclass mr1) * idx1 <= off16 < size_class (m_sizeclass mr1) * (idx1 + 1)) ->
(48 <= m_sizeclass mr1 -> m_sizeclass mr1 = 63) ->
(m_maplen mr1 <> 0 -> off16 <= m_maplen mr1 * 256 - 1) ->
rw_cells usegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rnest_call_post sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (grp_del st g p) g p (conc st g1) idx1 fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd08a0) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_maplen _ MW) as M12.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).

destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
{ rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
pose proof MS1 as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
assert (Hao : area_of g1 = a).
{ rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [exact AAL | unfold NSLOTS in Hkk; lia]. }
assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
{ rewrite HG. apply page_off_mod; [exact RgBAL | exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
unfold alloc_ceiling, RCTX, AREA_HDR, META_SIZE, NSLOTS in *.
assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.

change (frozen (conc st p mod 16 = 0)) in P16m.
change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
clear HGm AAL RBAL RgBAL SpA BbA.
destruct GB as (GB0 & GB1 & GB2 & _). destruct G1B as (G1B0 & G1B1 & G1B2 & _).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.

st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
pose proof (rmrep_ctx_secret_read st mX MR) as RC;
pose proof (bytes_at_read usegs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
pose proof (bytes_at_read usegs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
pose proof (bytes_at_read usegs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
end.
rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
rewrite Hchk in RA. rewrite Hao, (conc_region' st a rg Hrg) in RA. unfold RCTX in RC.
change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.

st1.
eapply evt_cut.
{ eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
(m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
(m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) (c_secret (ctx st))).
all: lazymatch goal with
| |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => exact R4
| |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => exact R3
| |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => exact R2
| |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => exact RG
| |- ov_read_bytes _ _ (wa 6576296) 8 = _ => exact RC
| |- ov_read_bytes _ _ (wa RCTX) 8 = _ => exact RC
| |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => exact RA
| |- rw_cells _ _ (conc _ _) _ => exact MM
| |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
| |- _ => idtac
end.
all: first [ exact P16m | exact HAeq | exact Hidx | exact Hav | exact Hfr | exact Hsc | exact Hsc63 | exact Hml
| lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
replace (ret_pc (Z_to_bv 64 0xd08b8)) with (Z_to_bv 64 0xd08b8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

st1.
unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
st1.

clear CH MM RG RA RC R4 R2.
pose proof MR as (_ & _ & _ & _ & GR0 & _). destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rw_cells_store_ok_at usegs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
clear RWp.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) ltac:(eassumption) Hp UNK (length_le8 _)) as MR2
end.
rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
apply (rmrep_grp_del_eq st _ g p) in MR2.

st1. st1.
apply evt_done. unfold rnest_call_post. do 14 eexists.
split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
cbv delta [mkR]. unfold RCTX. reflexivity. }
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_group; [exact Hp | lia]. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
Qed.

#[using="Type"] Lemma rntf_nest_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) (st0 st : mstate) (g : aptr) (lo : Z),
rmrep st m -> mem_inv usegs m -> meta_slot st g -> fm_facts st g ->
conc st g = conc st0 g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a0 a1)
(MS (mkR (Z_to_bv 64 0xd08cc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) (Z_to_bv 64 (conc st0 g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd08cc) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in *.
st1. st1. st1.
rewrite <- Hcg.
eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
first [exact MR | assumption | exact MSL | exact FMF | exact S1 | exact FR | exact ST | unfold alloc_ceiling; lia].
Qed.

End RC__1.
End Mql.

Module Mqm.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_set_bounce : forall st m i v,
rmrep st m -> 0 <= i < 32 ->
rmrep (set_bounce i v st) (write_to_mem m (wa (RCTX + 880 + i)) [b8 v]).
Proof.
intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6 & X7) & _).
pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write usegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl usegs m)) as WM.
eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
apply (u8arr_write usegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
- right. split; [| rctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.
End RC__1.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (stk_write usegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write usegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv usegs mX |- _ =>
apply (mem_inv_store usegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.

Ltac rraw_store_finish0 A bs' MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
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

#[using="Type"] Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
conc st q = conc st g -> q = g.
Proof.
intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
- rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
- exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.
End RC__2.

Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; tauto]);
clear MUq WMq CH end.

Ltac rmchunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_regroup : forall st m m' b gh g ai (w8' : byte),
rmrep st m -> (s_groups st) !! b = Some gh ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
munch [(conc st b, conc st b + 9)]%Z m m' -> wmono usegs m m' ->
rw_cells usegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
rmrep (put_group b (Some g) ai st) m'.
Proof.
intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
pose proof (rmrep_del_group st m b MR) as MR1.
assert (MR2 : rmrep (del_group b st) m').
{ eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
pose proof (round_up_pg_ge (r_len r)).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
- unfold RCTX in R1. lia.
- unfold RMLOCK in R2. lia.
- unfold RNEED_LOCKS in R3. lia.
- unfold RPAGE_SIZE in R4. lia.
- change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
- unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
rewrite lookup_delete_ne in Hb2 by congruence.
destruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
+ rewrite E, Hr in Hr2. inversion Hr2; subst r2.
assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
+ destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
- change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
destruct (N.eq_dec q (fst b)) as [->|NE].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
- unfold RGOT_SSP in R8. lia.
- unfold RSSP_GUARD in R9. lia. }
rewrite <- put_group_del.
eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

#[using="Type"] Lemma rmrep_set_group_ai : forall st m m' b g ai0 ai (w8' : byte),
rmrep st m -> (s_groups st) !! b = Some (mkGhdr (Some g) ai0) ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
munch [(conc st b, conc st b + 9)]%Z m m' -> wmono usegs m m' ->
rw_cells usegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
rmrep (set_group_active_idx b ai st) m'.
Proof.
intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
eapply rmrep_regroup; eauto.
Qed.

#[using="Type"] Lemma rmrep_ctr_byte_read : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
ov_read_bytes usegs m (wa (RCTX + 12)) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof.
intros st m (_ & (HD & _) & _) CR.
destruct HD as [[_ HB] _]. unfold ctx_head_cells in HB. cbn [cells_bytes cbytes app] in HB.
rewrite (bytes_at_read usegs m RCTX _ 12 1 HB).
all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
change (Z.to_nat 12) with 12%nat.
unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

End RC__3.
End Mqm.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Notation RISTF := (@ISTF_g ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved rc_secret).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rimplT_steq {R} o (t1 t2 : QUZl.M R) s Q ms :
steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof.
intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|exact H]. apply eruns_steq. exact Hs.
Qed.

#[using="Type"] Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> QUZl.M R') -> QUZl.M R' -> QUZl.M R')
(k : X -> Y -> QUZl.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
rimplT o (P _ kS bS) s QS ms ->
(forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
(forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
rimplT o (P R k bail) s Q ms.
Proof.
intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
eapply rimplT_bind; [eapply rimplT_reach; exact H|].
intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
(exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
/\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

Definition ras_post2
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
(st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
/\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
/\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
/\ mrel st st1 /\ brk_link_ps st1 s'
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ as_inv2 st0 st st1 sc idx
/\ 0 <= c_mmap_counter (ctx st1) < 2^32
/\ ((idx = -1 /\ errv' = Z_to_bv 64 12)
\/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
/\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

#[using="Type"] Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof. reflexivity. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
forall (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).

#[using="Type"] Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
forall (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof.
intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot _ R' full_lay fuel st sc req k' b') k bail s
(fun r s' ms' => match r with
| Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
| None => False end)).
- apply alloc_slot_nat.
- eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
- intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
- intros s' ms' [].
Qed.

#[using="Type"] Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
forall (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
tp = Z_to_bv 64 0x625520 ->
(forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
rimplT o (k st1 mo) s' Q ms') ->
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs)).
Proof.
intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta _ R' st k' b') k bail s
(fun r s' ms' => match r with
| Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
| None => False end)).
- apply alloc_meta_nat.
- eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
- intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
- intros s' ms' [].
Qed.

End RC__1.
