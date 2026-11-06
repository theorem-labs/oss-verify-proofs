(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QZzg QTVW QbcP_c1 Qu4g QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QZzg QTVW QbcP_c1 Qu4g QN4c.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Fixpoint zrange (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zrange (lo + 1) n' end.
Lemma in_zrange : forall n lo x, In x (zrange lo n) <-> lo <= x < lo + Z.of_nat n.
Proof. induction n as [|n IH]; intros lo x; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma brute_word_eq : forall (f g : Z -> bv 64) lo hi n,
forallb (fun k => bv_eqb (f k) (g k)) (zrange lo (Z.to_nat (hi - lo + 1))) = true -> lo <= n <= hi -> f n = g n.
Proof.
intros f g lo hi n H Hn. rewrite forallb_forall in H. specialize (H n ltac:(apply in_zrange; lia)).
unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Ltac brute_eq n lo hi :=
pattern n;
lazymatch goal with |- (fun x => @?A x = @?B x) _ =>
cbv beta;
apply (brute_word_eq (fun x => A x) (fun x => B x) lo hi n); [vm_compute; reflexivity| lia]
end.

Ltac sname rd :=
get_reg rd ltac:(fun v =>
lazymatch v with
| Z_to_bv 64 ?e => tryif is_Zlit e then idtac else (let nm := fresh "cv" in set (nm := v) in |- *)
| _ => let nm := fresh "cv" in set (nm := v) in |- *
end).

Definition smear_inv (L m x : Z) : Prop :=
0 <= x /\ (forall i, L < i -> Z.testbit x i = false) /\ (forall i, 0 <= i -> L - m < i <= L -> Z.testbit x i = true).

Lemma smear_inv_step : forall L m m' x, 0 <= m -> m' = 2 * m -> smear_inv L m x -> smear_inv L m' (Z.lor x (Z.shiftr x m)).
Proof.
intros L m m' x Hm -> (Hx & Hhi & Hlo). split; [|split].
- apply Z.lor_nonneg. split; [exact Hx|]. apply Z.shiftr_nonneg. exact Hx.
- intros i Hi. destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [apply Z.testbit_neg_r; exact Hn|].
rewrite Z.lor_spec, Z.shiftr_spec by exact Hn. rewrite !Hhi by lia. reflexivity.
- intros i Hi0 Hi. rewrite Z.lor_spec, Z.shiftr_spec by exact Hi0.
destruct (Z_le_gt_dec i (L - m)) as [Hc|Hc].
+ rewrite (Hlo (i + m)) by lia. apply Bool.orb_true_r.
+ rewrite (Hlo i) by lia. reflexivity.
Qed.

Lemma smear_inv_init : forall x, 0 < x -> smear_inv (Z.log2 x) 1 x.
Proof.
intros x Hx. split; [lia|split].
- intros i Hi. apply Z.bits_above_log2; lia.
- intros i Hi0 Hi. replace i with (Z.log2 x) by lia. apply Z.bit_log2. exact Hx.
Qed.

Lemma smear_inv_ones : forall L m x, 0 <= L -> L < m -> smear_inv L m x -> x = Z.ones (L + 1).
Proof.
intros L m x HL Hm (Hx & Hhi & Hlo). apply Z.bits_inj'. intros i Hi.
destruct (Z_le_gt_dec i L) as [Hc|Hc].
- rewrite (Hlo i Hi) by lia. symmetry. apply Z.ones_spec_low. lia.
- rewrite (Hhi i) by lia. symmetry. apply Z.ones_spec_high. lia.
Qed.

Lemma smear_word_step : forall (w s o : bv 64) L m m' x,
bv_unsigned w = x -> 0 <= m -> m' = 2 * m -> smear_inv L m x ->
s = Z_to_bv 64 (Z.shiftr (bv_unsigned w) m) -> o = Z_to_bv 64 (Z.lor (bv_unsigned w) (bv_unsigned s)) ->
exists y, bv_unsigned o = y /\ smear_inv L m' y.
Proof.
intros w s o L m m' x Ew Hm Hm' SI -> ->. exists (Z.lor x (Z.shiftr x m)). split.
- rewrite inr64_unsigned_lit by (apply zr_lor; apply zr_word).
rewrite inr64_unsigned_lit by (apply zr_shiftr; [apply zr_word| exact Hm]). rewrite Ew. reflexivity.
- exact (smear_inv_step L m m' x Hm Hm' SI).
Qed.

Lemma lor_even_bit : forall a b, 0 <= b <= 1 -> Z.lor (2 * a) b = 2 * a + b.
Proof.
intros a b Hb. assert (b = 0 \/ b = 1) as [ -> | -> ] by lia.
- rewrite Z.lor_0_r. lia.
- apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z.eq_dec i 0) as [->|Hi'].
+ rewrite Z.testbit_even_0, Z.testbit_odd_0. reflexivity.
+ replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ, Z.testbit_odd_succ by lia.
rewrite (Z.bits_above_log2 1 (Z.succ (i - 1))) by (cbn; lia). apply Bool.orb_false_r.
Qed.

Lemma cid_goal : forall n : Z, 513 <= n <= 65536 ->
let cv0 := Z_to_bv 64 n in
let cv := Z_to_bv 64 (Z.shiftr (bv_unsigned cv0) 1) in
let cv1 := Z_to_bv 64 (Z.lor (bv_unsigned cv0) (bv_unsigned cv)) in
let cv2 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv1) 2) in
let cv3 := Z_to_bv 64 (Z.lor (bv_unsigned cv1) (bv_unsigned cv2)) in
let cv4 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv3) 4) in
let cv5 := Z_to_bv 64 (Z.lor (bv_unsigned cv3) (bv_unsigned cv4)) in
let cv6 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv5) 8) in
let cv7 := Z_to_bv 64 (Z.lor (bv_unsigned cv5) (bv_unsigned cv6)) in
let cv8 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv7) 16) in
let cv9 := Z_to_bv 64 (Z.lor (bv_unsigned cv7) (bv_unsigned cv8)) in
let cv10 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv9) 32) in
let cv11 := Z_to_bv 64 (Z.lor (bv_unsigned cv9) (bv_unsigned cv10)) in
let cv12 := Z_to_bv 64 (Z.lxor (bv_unsigned cv11) 18446744073709551615) in
let cv13 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv12) 1) in
let cv14 := Z_to_bv 64 (Z.land (bv_unsigned cv13) 6148914691236517205) in
let cv15 := Z_to_bv 64 (Z.sub (bv_unsigned cv12) (bv_unsigned cv14)) in
let cv16 := Z_to_bv 64 (Z.land (bv_unsigned cv15) 3689348814741910323) in
let cv17 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv15) 2) in
let cv18 := Z_to_bv 64 (Z.land (bv_unsigned cv17) 3689348814741910323) in
let cv19 := Z_to_bv 64 (Z.add (bv_unsigned cv16) (bv_unsigned cv18)) in
let cv20 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv19) 4) in
let cv21 := Z_to_bv 64 (Z.add (bv_unsigned cv19) (bv_unsigned cv20)) in
let cv22 := Z_to_bv 64 (Z.land (bv_unsigned cv21) 1085102592571150095) in
let cv23 := Z_to_bv 64 (Z.mul (bv_unsigned cv22) 72340172838076673) in
let cv24 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv23) 56) in
let cv25 := Z_to_bv 64 (bv_swrap 32 (Z.sub 62 (bv_unsigned cv24))) in
let cv26 := Z_to_bv 64 (Z.shiftl (bv_unsigned cv24) 1) in
let cv27 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv0) (Z.modulo (bv_unsigned cv25) 64)) in
let cv28 := Z_to_bv 64 (bv_swrap 32 (Z.shiftl 18446744073709551615 (Z.modulo (bv_unsigned cv25) 32))) in
let cv29 := Z_to_bv 64 (Z.lxor (bv_unsigned cv26) 126) in
let cv30 := Z_to_bv 64 (Z.land (bv_unsigned cv27) 1) in
let cv31 := Z_to_bv 64 (Z.lxor (bv_unsigned cv28) 18446744073709551615) in
let cv32 := Z_to_bv 64 (Z.land (bv_unsigned cv0) (bv_unsigned cv31)) in
let cv33 := Z_to_bv 64 (Z.lor (bv_unsigned cv29) (bv_unsigned cv30)) in
let cv34 := v_sltu (Z_to_bv 64 0) cv32 in
let cv35 := Z_to_bv 64 (Z.add (bv_unsigned cv33) (bv_unsigned cv34)) in
let cv36 := Z_to_bv 64 (Z.add (bv_unsigned cv35) (-2)) in
cv36 = Z_to_bv 64 (class_id n).
Proof.
intros n Hn cv0 cv cv1 cv2 cv3 cv4 cv5 cv6 cv7 cv8 cv9 cv10 cv11 cv12 cv13 cv14 cv15 cv16 cv17 cv18 cv19 cv20
cv21 cv22 cv23 cv24 cv25 cv26 cv27 cv28 cv29 cv30 cv31 cv32 cv33 cv34 cv35 cv36.
assert (U0 : bv_unsigned cv0 = n) by (apply inr64_unsigned_lit; unfold inr64; lia).
assert (HL : 9 <= Z.log2 n <= 16).
{ pose proof (proj1 (Z.log2_le_pow2 n 9 ltac:(lia)) ltac:(change (2 ^ 9) with 512; lia)) as HL1.
pose proof (proj1 (Z.log2_lt_pow2 n 17 ltac:(lia)) ltac:(change (2 ^ 17) with 131072; lia)) as HL2. lia. }

assert (S1 : smear_inv (Z.log2 n) 1 n) by (apply smear_inv_init; lia).
destruct (smear_word_step cv0 cv cv1 _ 1 2 n U0 ltac:(lia) eq_refl S1 eq_refl eq_refl) as (x1 & U1 & S2).
destruct (smear_word_step cv1 cv2 cv3 _ 2 4 x1 U1 ltac:(lia) eq_refl S2 eq_refl eq_refl) as (x3 & U3 & S3).
destruct (smear_word_step cv3 cv4 cv5 _ 4 8 x3 U3 ltac:(lia) eq_refl S3 eq_refl eq_refl) as (x5 & U5 & S4).
destruct (smear_word_step cv5 cv6 cv7 _ 8 16 x5 U5 ltac:(lia) eq_refl S4 eq_refl eq_refl) as (x7 & U7 & S5).
destruct (smear_word_step cv7 cv8 cv9 _ 16 32 x7 U7 ltac:(lia) eq_refl S5 eq_refl eq_refl) as (x9 & U9 & S6).
destruct (smear_word_step cv9 cv10 cv11 _ 32 64 x9 U9 ltac:(lia) eq_refl S6 eq_refl eq_refl) as (x11 & U11 & S7).
pose proof (smear_inv_ones (Z.log2 n) 64 x11 ltac:(lia) ltac:(lia) S7) as E11. rewrite E11 in U11.
clear x1 x3 x5 x7 x9 U1 U3 U5 U7 U9 S1 S2 S3 S4 S5 S6 S7 E11.

assert (OCT : bv_unsigned cv25 = Z.log2 n - 1 /\ bv_unsigned cv29 = 2 * Z.log2 n /\ bv_unsigned cv31 = Z.ones (Z.log2 n - 1)).
{ unfold cv31, cv29, cv28, cv26, cv25, cv24, cv23, cv22, cv21, cv20, cv19, cv18, cv17, cv16, cv15, cv14, cv13, cv12.
rewrite U11.
assert (Z.log2 n = 9 \/ Z.log2 n = 10 \/ Z.log2 n = 11 \/ Z.log2 n = 12 \/ Z.log2 n = 13 \/ Z.log2 n = 14
\/ Z.log2 n = 15 \/ Z.log2 n = 16) as OC by lia.
destruct OC as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; (split; [reflexivity|split; reflexivity]). }
destruct OCT as (U25 & U29 & U31).

assert (U27 : bv_unsigned cv27 = Z.shiftr n (Z.log2 n - 1)).
{ unfold cv27. rewrite U0, U25, (Z.mod_small (Z.log2 n - 1) 64) by lia.
apply inr64_unsigned_lit. apply zr_shiftr; [unfold inr64; lia| lia]. }
assert (U30 : bv_unsigned cv30 = Z.land (Z.shiftr n (Z.log2 n - 1)) 1).
{ unfold cv30. rewrite U27. apply inr64_unsigned_lit. apply zr_land_lit. lia. }
assert (U32 : bv_unsigned cv32 = Z.land n (Z.ones (Z.log2 n - 1))).
{ unfold cv32. rewrite U0, U31. apply inr64_unsigned_lit. apply zr_land_l; [unfold inr64; lia|].
rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 (Z.log2 n - 1) ltac:(lia) ltac:(lia)). lia. }
assert (U34 : bv_unsigned cv34 = if 0 <? Z.land n (Z.ones (Z.log2 n - 1)) then 1 else 0).
{ unfold cv34. rewrite v_sltu_b2z, U32, (inr64_unsigned_lit 0) by (unfold inr64; lia).
rewrite inr64_unsigned_lit by apply zr_b2z. destruct (0 <? Z.land n (Z.ones (Z.log2 n - 1))); reflexivity. }
assert (HB : 0 <= Z.land (Z.shiftr n (Z.log2 n - 1)) 1 <= 1).
{ pose proof (Z.land_ones (Z.shiftr n (Z.log2 n - 1)) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E.
change (2 ^ 1) with 2 in E. rewrite E. pose proof (Z.mod_pos_bound (Z.shiftr n (Z.log2 n - 1)) 2 ltac:(lia)). lia. }
assert (U33 : bv_unsigned cv33 = 2 * Z.log2 n + Z.land (Z.shiftr n (Z.log2 n - 1)) 1).
{ unfold cv33. rewrite U29, U30, lor_even_bit by exact HB. apply inr64_unsigned_lit. unfold inr64. lia. }
assert (HC : 0 <= (if 0 <? Z.land n (Z.ones (Z.log2 n - 1)) then 1 else 0) <= 1)
by (destruct (0 <? Z.land n (Z.ones (Z.log2 n - 1))); lia).
assert (U35 : bv_unsigned cv35 = 2 * Z.log2 n + Z.land (Z.shiftr n (Z.log2 n - 1)) 1
+ (if 0 <? Z.land n (Z.ones (Z.log2 n - 1)) then 1 else 0)).
{ unfold cv35. rewrite U33, U34. apply inr64_unsigned_lit. unfold inr64. lia. }
assert (CID : class_id n = 16 + 2 * (Z.log2 n - 9) + Z.land (Z.shiftr n (Z.log2 n - 1)) 1
+ (if 0 <? Z.land n (Z.ones (Z.log2 n - 1)) then 1 else 0)).
{ unfold class_id. replace (n <=? 512) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
apply bv_eq. unfold cv36. rewrite U35, CID.
rewrite !inr64_unsigned_lit by (unfold inr64; lia). lia.
Qed.

Lemma class_id_small : forall n, 1 <= n <= 512 -> class_id n = (n + 31) / 32.
Proof. intros n Hn. unfold class_id. replace (n <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma classid_block : forall (n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (Q : machine_state -> Prop),
1 <= n <= 65536 ->
(forall a2' a4' a5' a6' a7' t0' t1',
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2 (wz (class_id n)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43c60) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43b4c) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros Hn CONT.
step.
step.
destruct (Z.leb_spec n 512) as [SM|BG].
- ifz.
step. step.
rewrite (unsigned_lit (n + 31)), Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. rewrite <- class_id_small by lia.
step.
apply CONT.
- ifz.
set (cv0 := wz n) in |- *.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 16%Z.
stp. sname 17%Z.
stp. sname 5%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 16%Z.
stp. sname 17%Z.
stp. sname 5%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 15%Z.
stp. sname 6%Z.
stp. sname 16%Z.
stp. sname 6%Z.
stp. sname 17%Z.
stp. sname 6%Z.
stp. sname 5%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 16%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 17%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 16%Z.
stp. sname 15%Z.
stp. sname 14%Z.
stp. sname 12%Z.
stp. sname 14%Z.
stp. sname 12%Z.
stp. sname 8%Z.
assert (E36 : cv36 = wz (class_id n)).
{ revert cv36. revert cv35. revert cv34. revert cv33. revert cv32. revert cv31. revert cv30. revert cv29. revert cv28. revert cv27.
revert cv26. revert cv25. revert cv24. revert cv23. revert cv22. revert cv21. revert cv20. revert cv19. revert cv18. revert cv17.
revert cv16. revert cv15. revert cv14. revert cv13. revert cv12. revert cv11. revert cv10. revert cv9. revert cv8. revert cv7.
revert cv6. revert cv5. revert cv4. revert cv3. revert cv2. revert cv1. revert cv. revert cv0.
exact (cid_goal n ltac:(lia)). }
rewrite E36. apply CONT.
Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Fixpoint zrange (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zrange (lo + 1) n' end.
Lemma in_zrange : forall n lo x, In x (zrange lo n) <-> lo <= x < lo + Z.of_nat n.
Proof. induction n as [|n IH]; intros lo x; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma brute_word_eq : forall (f g : Z -> bv 64) lo hi n,
forallb (fun k => bv_eqb (f k) (g k)) (zrange lo (Z.to_nat (hi - lo + 1))) = true -> lo <= n <= hi -> f n = g n.
Proof.
intros f g lo hi n H Hn. rewrite forallb_forall in H. specialize (H n ltac:(apply in_zrange; lia)).
unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Ltac brute_eq n lo hi :=
pattern n;
lazymatch goal with |- (fun x => @?A x = @?B x) _ =>
cbv beta;
apply (brute_word_eq (fun x => A x) (fun x => B x) lo hi n); [vm_compute; reflexivity| lia]
end.

Ltac sname rd :=
get_reg rd ltac:(fun v =>
lazymatch v with
| Z_to_bv 64 ?e => tryif is_Zlit e then idtac else (let nm := fresh "cv" in set (nm := v) in |- *)
| _ => let nm := fresh "cv" in set (nm := v) in |- *
end).

Definition smear_inv (L m x : Z) : Prop :=
0 <= x /\ (forall i, L < i -> Z.testbit x i = false) /\ (forall i, 0 <= i -> L - m < i <= L -> Z.testbit x i = true).

Lemma smear_inv_step : forall L m m' x, 0 <= m -> m' = 2 * m -> smear_inv L m x -> smear_inv L m' (Z.lor x (Z.shiftr x m)).
Proof.
intros L m m' x Hm -> (Hx & Hhi & Hlo). split; [|split].
- apply Z.lor_nonneg. split; [exact Hx|]. apply Z.shiftr_nonneg. exact Hx.
- intros i Hi. destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [apply Z.testbit_neg_r; exact Hn|].
rewrite Z.lor_spec, Z.shiftr_spec by exact Hn. rewrite !Hhi by lia. reflexivity.
- intros i Hi0 Hi. rewrite Z.lor_spec, Z.shiftr_spec by exact Hi0.
destruct (Z_le_gt_dec i (L - m)) as [Hc|Hc].
+ rewrite (Hlo (i + m)) by lia. apply Bool.orb_true_r.
+ rewrite (Hlo i) by lia. reflexivity.
Qed.

Lemma smear_inv_init : forall x, 0 < x -> smear_inv (Z.log2 x) 1 x.
Proof.
intros x Hx. split; [lia|split].
- intros i Hi. apply Z.bits_above_log2; lia.
- intros i Hi0 Hi. replace i with (Z.log2 x) by lia. apply Z.bit_log2. exact Hx.
Qed.

Lemma smear_inv_ones : forall L m x, 0 <= L -> L < m -> smear_inv L m x -> x = Z.ones (L + 1).
Proof.
intros L m x HL Hm (Hx & Hhi & Hlo). apply Z.bits_inj'. intros i Hi.
destruct (Z_le_gt_dec i L) as [Hc|Hc].
- rewrite (Hlo i Hi) by lia. symmetry. apply Z.ones_spec_low. lia.
- rewrite (Hhi i) by lia. symmetry. apply Z.ones_spec_high. lia.
Qed.

Lemma smear_word_step : forall (w s o : bv 64) L m m' x,
bv_unsigned w = x -> 0 <= m -> m' = 2 * m -> smear_inv L m x ->
s = Z_to_bv 64 (Z.shiftr (bv_unsigned w) m) -> o = Z_to_bv 64 (Z.lor (bv_unsigned w) (bv_unsigned s)) ->
exists y, bv_unsigned o = y /\ smear_inv L m' y.
Proof.
intros w s o L m m' x Ew Hm Hm' SI -> ->. exists (Z.lor x (Z.shiftr x m)). split.
- rewrite inr64_unsigned_lit by (apply zr_lor; apply zr_word).
rewrite inr64_unsigned_lit by (apply zr_shiftr; [apply zr_word| exact Hm]). rewrite Ew. reflexivity.
- exact (smear_inv_step L m m' x Hm Hm' SI).
Qed.

Lemma lor_even_bit : forall a b, 0 <= b <= 1 -> Z.lor (2 * a) b = 2 * a + b.
Proof.
intros a b Hb. assert (b = 0 \/ b = 1) as [ -> | -> ] by lia.
- rewrite Z.lor_0_r. lia.
- apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
destruct (Z.eq_dec i 0) as [->|Hi'].
+ rewrite Z.testbit_even_0, Z.testbit_odd_0. reflexivity.
+ replace i with (Z.succ (i - 1)) by lia. rewrite Z.testbit_even_succ, Z.testbit_odd_succ by lia.
rewrite (Z.bits_above_log2 1 (Z.succ (i - 1))) by (cbn; lia). apply Bool.orb_false_r.
Qed.

Lemma cid_goal : forall n : Z, 513 <= n <= 65536 ->
let cv0 := Z_to_bv 64 n in
let cv := Z_to_bv 64 (Z.shiftr (bv_unsigned cv0) 1) in
let cv1 := Z_to_bv 64 (Z.lor (bv_unsigned cv0) (bv_unsigned cv)) in
let cv2 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv1) 2) in
let cv3 := Z_to_bv 64 (Z.lor (bv_unsigned cv1) (bv_unsigned cv2)) in
let cv4 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv3) 4) in
let cv5 := Z_to_bv 64 (Z.lor (bv_unsigned cv3) (bv_unsigned cv4)) in
let cv6 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv5) 8) in
let cv7 := Z_to_bv 64 (Z.lor (bv_unsigned cv5) (bv_unsigned cv6)) in
let cv8 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv7) 16) in
let cv9 := Z_to_bv 64 (Z.lor (bv_unsigned cv7) (bv_unsigned cv8)) in
let cv10 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv9) 32) in
let cv11 := Z_to_bv 64 (Z.lor (bv_unsigned cv9) (bv_unsigned cv10)) in
let cv12 := Z_to_bv 64 (Z.lxor (bv_unsigned cv11) 18446744073709551615) in
let cv13 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv12) 1) in
let cv14 := Z_to_bv 64 (Z.land (bv_unsigned cv13) 6148914691236517205) in
let cv15 := Z_to_bv 64 (Z.sub (bv_unsigned cv12) (bv_unsigned cv14)) in
let cv16 := Z_to_bv 64 (Z.land (bv_unsigned cv15) 3689348814741910323) in
let cv17 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv15) 2) in
let cv18 := Z_to_bv 64 (Z.land (bv_unsigned cv17) 3689348814741910323) in
let cv19 := Z_to_bv 64 (Z.add (bv_unsigned cv16) (bv_unsigned cv18)) in
let cv20 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv19) 4) in
let cv21 := Z_to_bv 64 (Z.add (bv_unsigned cv19) (bv_unsigned cv20)) in
let cv22 := Z_to_bv 64 (Z.land (bv_unsigned cv21) 1085102592571150095) in
let cv23 := Z_to_bv 64 (Z.mul (bv_unsigned cv22) 72340172838076673) in
let cv24 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv23) 56) in
let cv25 := Z_to_bv 64 (bv_swrap 32 (Z.sub 62 (bv_unsigned cv24))) in
let cv26 := Z_to_bv 64 (Z.shiftl (bv_unsigned cv24) 1) in
let cv27 := Z_to_bv 64 (Z.shiftr (bv_unsigned cv0) (Z.modulo (bv_unsigned cv25) 64)) in
let cv28 := Z_to_bv 64 (bv_swrap 32 (Z.shiftl 18446744073709551615 (Z.modulo (bv_unsigned cv25) 32))) in
let cv29 := Z_to_bv 64 (Z.lxor (bv_unsigned cv26) 126) in
let cv30 := Z_to_bv 64 (Z.land (bv_unsigned cv27) 1) in
let cv31 := Z_to_bv 64 (Z.lxor (bv_unsigned cv28) 18446744073709551615) in
let cv32 := Z_to_bv 64 (Z.land (bv_unsigned cv0) (bv_unsigned cv31)) in
let cv33 := Z_to_bv 64 (Z.lor (bv_unsigned cv29) (bv_unsigned cv30)) in
let cv34 := v_sltu (Z_to_bv 64 0) cv32 in
let cv35 := Z_to_bv 64 (Z.add (bv_unsigned cv33) (bv_unsigned cv34)) in
let cv36 := Z_to_bv 64 (Z.add (bv_unsigned cv35) (-2)) in
cv36 = Z_to_bv 64 (class_id n).
Proof.
intros n Hn cv0 cv cv1 cv2 cv3 cv4 cv5 cv6 cv7 cv8 cv9 cv10 cv11 cv12 cv13 cv14 cv15 cv16 cv17 cv18 cv19 cv20
cv21 cv22 cv23 cv24 cv25 cv26 cv27 cv28 cv29 cv30 cv31 cv32 cv33 cv34 cv35 cv36.
assert (U0 : bv_unsigned cv0 = n) by (apply inr64_unsigned_lit; unfold inr64; lia).
assert (HL : 9 <= Z.log2 n <= 16).
{ pose proof (proj1 (Z.log2_le_pow2 n 9 ltac:(lia)) ltac:(change (2 ^ 9) with 512; lia)) as HL1.
pose proof (proj1 (Z.log2_lt_pow2 n 17 ltac:(lia)) ltac:(change (2 ^ 17) with 131072; lia)) as HL2. lia. }

assert (S1 : smear_inv (Z.log2 n) 1 n) by (apply smear_inv_init; lia).
destruct (smear_word_step cv0 cv cv1 _ 1 2 n U0 ltac:(lia) eq_refl S1 eq_refl eq_refl) as (x1 & U1 & S2).
destruct (smear_word_step cv1 cv2 cv3 _ 2 4 x1 U1 ltac:(lia) eq_refl S2 eq_refl eq_refl) as (x3 & U3 & S3).
destruct (smear_word_step cv3 cv4 cv5 _ 4 8 x3 U3 ltac:(lia) eq_refl S3 eq_refl eq_refl) as (x5 & U5 & S4).
destruct (smear_word_step cv5 cv6 cv7 _ 8 16 x5 U5 ltac:(lia) eq_refl S4 eq_refl eq_refl) as (x7 & U7 & S5).
destruct (smear_word_step cv7 cv8 cv9 _ 16 32 x7 U7 ltac:(lia) eq_refl S5 eq_refl eq_refl) as (x9 & U9 & S6).
destruct (smear_word_step cv9 cv10 cv11 _ 32 64 x9 U9 ltac:(lia) eq_refl S6 eq_refl eq_refl) as (x11 & U11 & S7).
pose proof (smear_inv_ones (Z.log2 n) 64 x11 ltac:(lia) ltac:(lia) S7) as E11. rewrite E11 in U11.
clear x1 x3 x5 x7 x9 U1 U3 U5 U7 U9 S1 S2 S3 S4 S5 S6 S7 E11.

assert (OCT : bv_unsigned cv25 = Z.log2 n - 1 /\ bv_unsigned cv29 = 2 * Z.log2 n /\ bv_unsigned cv31 = Z.ones (Z.log2 n - 1)).
{ unfold cv31, cv29, cv28, cv26, cv25, cv24, cv23, cv22, cv21, cv20, cv19, cv18, cv17, cv16, cv15, cv14, cv13, cv12.
rewrite U11.
assert (Z.log2 n = 9 \/ Z.log2 n = 10 \/ Z.log2 n = 11 \/ Z.log2 n = 12 \/ Z.log2 n = 13 \/ Z.log2 n = 14
\/ Z.log2 n = 15 \/ Z.log2 n = 16) as OC by lia.
destruct OC as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; vm_compute; (split; [reflexivity|split; reflexivity]). }
destruct OCT as (U25 & U29 & U31).

assert (U27 : bv_unsigned cv27 = Z.shiftr n (Z.log2 n - 1)).
{ unfold cv27. rewrite U0, U25, (Z.mod_small (Z.log2 n - 1) 64) by lia.
apply inr64_unsigned_lit. apply zr_shiftr; [unfold inr64; lia| lia]. }
assert (U30 : bv_unsigned cv30 = Z.land (Z.shiftr n (Z.log2 n - 1)) 1).
{ unfold cv30. rewrite U27. apply inr64_unsigned_lit. apply zr_land_lit. lia. }
assert (U32 : bv_unsigned cv32 = Z.land n (Z.ones (Z.log2 n - 1))).
{ unfold cv32. rewrite U0, U31. apply inr64_unsigned_lit. apply zr_land_l; [unfold inr64; lia|].
rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 (Z.log2 n - 1) ltac:(lia) ltac:(lia)). lia. }
assert (U34 : bv_unsigned cv34 = if 0 <? Z.land n (Z.ones (Z.log2 n - 1)) then 1 else 0).
{ unfold cv34. rewrite v_sltu_b2z, U32, (inr64_unsigned_lit 0) by (unfold inr64; lia).
rewrite inr64_unsigned_lit by apply zr_b2z. destruct (0 <? Z.land n (Z.ones (Z.log2 n - 1))); reflexivity. }
assert (HB : 0 <= Z.land (Z.shiftr n (Z.log2 n - 1)) 1 <= 1).
{ pose proof (Z.land_ones (Z.shiftr n (Z.log2 n - 1)) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E.
change (2 ^ 1) with 2 in E. rewrite E. pose proof (Z.mod_pos_bound (Z.shiftr n (Z.log2 n - 1)) 2 ltac:(lia)). lia. }
assert (U33 : bv_unsigned cv33 = 2 * Z.log2 n + Z.land (Z.shiftr n (Z.log2 n - 1)) 1).
{ unfold cv33. rewrite U29, U30, lor_even_bit by exact HB. apply inr64_unsigned_lit. unfold inr64. lia. }
assert (HC : 0 <= (if 0 <? Z.land n (Z.ones (Z.log2 n - 1)) then 1 else 0) <= 1)
by (destruct (0 <? Z.land n (Z.ones (Z.log2 n - 1))); lia).
assert (U35 : bv_unsigned cv35 = 2 * Z.log2 n + Z.land (Z.shiftr n (Z.log2 n - 1)) 1
+ (if 0 <? Z.land n (Z.ones (Z.log2 n - 1)) then 1 else 0)).
{ unfold cv35. rewrite U33, U34. apply inr64_unsigned_lit. unfold inr64. lia. }
assert (CID : class_id n = 16 + 2 * (Z.log2 n - 9) + Z.land (Z.shiftr n (Z.log2 n - 1)) 1
+ (if 0 <? Z.land n (Z.ones (Z.log2 n - 1)) then 1 else 0)).
{ unfold class_id. replace (n <=? 512) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
apply bv_eq. unfold cv36. rewrite U35, CID.
rewrite !inr64_unsigned_lit by (unfold inr64; lia). lia.
Qed.

Lemma class_id_small : forall n, 1 <= n <= 512 -> class_id n = (n + 31) / 32.
Proof. intros n Hn. unfold class_id. replace (n <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma classid_block : forall (n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (Q : machine_state -> Prop),
1 <= n <= 65536 ->
(forall a2' a4' a5' a6' a7' t0' t1',
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2 (wz (class_id n)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43a34) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43920) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros Hn CONT.
step.
step.
destruct (Z.leb_spec n 512) as [SM|BG].
- ifz.
step. step.
rewrite (unsigned_lit (n + 31)), Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. rewrite <- class_id_small by lia.
step.
apply CONT.
- ifz.
set (cv0 := wz n) in |- *.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 16%Z.
stp. sname 17%Z.
stp. sname 5%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 16%Z.
stp. sname 17%Z.
stp. sname 5%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 15%Z.
stp. sname 6%Z.
stp. sname 16%Z.
stp. sname 6%Z.
stp. sname 17%Z.
stp. sname 6%Z.
stp. sname 5%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 6%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 16%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 17%Z.
stp. sname 15%Z.
stp. sname 12%Z.
stp. sname 16%Z.
stp. sname 15%Z.
stp. sname 14%Z.
stp. sname 12%Z.
stp. sname 14%Z.
stp. sname 12%Z.
stp. sname 8%Z.
assert (E36 : cv36 = wz (class_id n)).
{ revert cv36. revert cv35. revert cv34. revert cv33. revert cv32. revert cv31. revert cv30. revert cv29. revert cv28. revert cv27.
revert cv26. revert cv25. revert cv24. revert cv23. revert cv22. revert cv21. revert cv20. revert cv19. revert cv18. revert cv17.
revert cv16. revert cv15. revert cv14. revert cv13. revert cv12. revert cv11. revert cv10. revert cv9. revert cv8. revert cv7.
revert cv6. revert cv5. revert cv4. revert cv3. revert cv2. revert cv1. revert cv. revert cv0.
exact (cid_goal n ltac:(lia)). }
rewrite E36. apply CONT.
Qed.
