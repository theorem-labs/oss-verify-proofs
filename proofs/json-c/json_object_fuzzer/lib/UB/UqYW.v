(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.

Module GwI.
Definition segs := rsegs.
End GwI.

Ltac show_goal := match goal with |- ?g => idtac g end.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
end.
Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.

Ltac decb := repeat match goal with
| |- context [Z.ltb ?a ?b] => first [replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; mlia2) | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; mlia2)]
| |- context [Z.leb ?a ?b] => first [replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; mlia2) | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; mlia2)]
| |- context [Z.eqb ?a ?b] => first [replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; mlia2) | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; mlia2)]
end.

Lemma sx32_M64 : sx32 (Z_to_bv 64 18446744073709551615) = Z_to_bv 64 18446744073709551615.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.sx32_M64) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.sx32_M64)]. Qed.
Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.zx32_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.zx32_lit)]. Qed.

Lemma bv_lts_lit : ltac2:(Q6nq.tyx '(@QQRC.Mq1.bv_lts_lit) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@QQRC.Mq1.bv_lts_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.bv_lts_lit)]. Qed.
Lemma swrap32_land64_add : ltac2:(Q6nq.tyx '(@QQRC.Mq1.swrap32_land64_add) [] '([18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) Q6nq.gwt_nil))).
Proof. first [GwInst.gw_exact (@QQRC.Mq1.swrap32_land64_add) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.swrap32_land64_add)]. Qed.
Lemma swrap32_shift : forall x k k', (k' = k - 2^64)%Z -> bv_swrap 32 (x + k) = bv_swrap 32 (x + k').
Proof. first [GwInst.gw_exact (@QQRC.Mq1.swrap32_shift) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.swrap32_shift)]. Qed.
Lemma swrap32_shift_sub : forall x k k', (k' = 2^64 - k)%Z -> bv_swrap 32 (x - k) = bv_swrap 32 (x + k').
Proof. first [GwInst.gw_exact (@QQRC.Mq1.swrap32_shift_sub) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.swrap32_shift_sub)]. Qed.
Lemma swrap32_landW : forall a c, bv_swrap 32 (Z.land a 18446744073709551615 + c) = bv_swrap 32 (a + c).
Proof. first [GwInst.gw_exact (@QQRC.Mq1.swrap32_landW) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.swrap32_landW)]. Qed.
Lemma swrap32_landW_sub : forall a c, bv_swrap 32 (Z.land a 18446744073709551615 - c) = bv_swrap 32 (a - c).
Proof. first [GwInst.gw_exact (@QQRC.Mq1.swrap32_landW_sub) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.swrap32_landW_sub)]. Qed.
Lemma swrap32_swrap32_add : forall e k, bv_swrap 32 (Z.land (bv_swrap 32 e) 18446744073709551615 + k) = bv_swrap 32 (e + k).
Proof. first [GwInst.gw_exact (@QQRC.Mq1.swrap32_swrap32_add) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.swrap32_swrap32_add)]. Qed.
Lemma bv_lts_0_lit : forall e, (-2^63 <= e < 2^63)%Z -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 e) = (0 <? e)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.bv_lts_0_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.bv_lts_0_lit)]. Qed.
Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).
Lemma swrap32_land64_small : forall e, (-2^31 <= e < 2^31)%Z -> bv_swrap 32 (Z.land e 18446744073709551615) = e.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.swrap32_land64_small) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.swrap32_land64_small)]. Qed.
Ltac fixw2 := rewrite ?swrap32_landW, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
Ltac fixw :=
try match goal with |- context [bv_swrap 32 (?x + ?k)] =>
lazymatch isZcst k with true => idtac end;
first [ assert_succeeds (assert (2^63 <= k)%Z by lia);
let k' := eval vm_compute in (k - 2^64)%Z in rewrite (swrap32_shift x k k') by reflexivity
| idtac ] end;
try match goal with |- context [bv_swrap 32 (?x - ?k)] =>
lazymatch isZcst k with true => idtac end;
first [ assert_succeeds (assert (2^63 <= k)%Z by lia);
let k' := eval vm_compute in (2^64 - k)%Z in rewrite (swrap32_shift_sub x k k') by reflexivity
| idtac ] end;
try rewrite swrap32_land64_add by lia; try rewrite swrap32_land64_small by lia; try rewrite swrap32_small by lia.

Lemma f128_le_range : forall a b, (-1 <= f128_le a b <= 1)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.f128_le_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.f128_le_range)]. Qed.
Lemma fpclass_not_nan : forall y, Z.land (Z.shiftr (hi64 y) 48) 0x7fff <> 0x7fff%Z -> (m_fpclassifyl y =? 0) = false.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.fpclass_not_nan) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.fpclass_not_nan)]. Qed.
Lemma fpclass_nan : ltac2:(Q6nq.tyx '(@QQRC.Mq1.fpclass_nan) [] '([32767; 281474976710655]%Z : list Z) '(Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil)).
Proof. first [GwInst.gw_exact (@QQRC.Mq1.fpclass_nan) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.fpclass_nan)]. Qed.
Lemma land_pow2_bit : forall a n, (0 <= n)%Z -> Z.land a (2^n) = (if Z.testbit a n then 2^n else 0)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.land_pow2_bit) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.land_pow2_bit)]. Qed.
Lemma zbv_u64 : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.zbv_u64) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.zbv_u64)]. Qed.
Lemma shl48_land64 : forall v, Z.land (Z.shiftl v 48) 18446744073709551615 = Z.shiftl (Z.land v 65535) 48.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.shl48_land64) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.shl48_land64)]. Qed.
Lemma pack_hi_range : forall xhi v, (0 <= Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land v 65535) 48) < 2^64)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.pack_hi_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.pack_hi_range)]. Qed.
Lemma pack_eq : ltac2:(Q6nq.tyx '(@QQRC.Mq1.pack_eq) [] '([65535; 281474976710655; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@MASK48) Q6nq.gwt_nil)))).
Proof. first [GwInst.gw_exact (@QQRC.Mq1.pack_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.pack_eq)]. Qed.
Lemma sbb_bridge : forall xhi xlo yhi ylo, (0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z ->
let hi' := (if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi))%Z in
Z.land (Z.land (xhi - yhi) 18446744073709551615 - Z.b2z (xlo <? ylo)%Z) 18446744073709551615 = hi'
/\ Z_to_bv 64 (Z.land (xhi - yhi) 18446744073709551615 - Z.b2z (xlo <? ylo)%Z) = Z_to_bv 64 hi'
/\ (0 <= hi' < 2^64)%Z /\ u64 (xlo - ylo) = Z.land (xlo - ylo) 18446744073709551615.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.sbb_bridge) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.sbb_bridge)]. Qed.
Lemma shr63_eqb : forall h, (0 <= h < 2^64)%Z -> (Z.shiftr h 63 =? 0) = (h <? 2^63)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.shr63_eqb) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.shr63_eqb)]. Qed.
Lemma shr48_range : forall h, (0 <= h < 2^64)%Z -> (0 <= Z.shiftr h 48 < 65536)%Z.
Proof. first [GwApply.gw_by_name GwI.segs (@QQRC.Mq1.shr48_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQRC.Mq1.shr48_range)]. Qed.
Lemma land63_range : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.land x 0x7fffffffffffffff < 2^64)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.land63_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.land63_range)]. Qed.
Lemma testbit_small_high : forall x k i, (0 <= x < 2^k)%Z -> (0 <= k <= i)%Z -> Z.testbit x i = false.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.testbit_small_high) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.testbit_small_high)]. Qed.
Lemma lor_low_high : forall x y k, (0 <= x < 2^k)%Z -> (0 <= y)%Z -> (0 <= k)%Z -> Z.lor x (y * 2^k) = (x + y * 2^k)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.lor_low_high) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.lor_low_high)]. Qed.
Lemma land_highmask : forall x k, (0 <= x < 2^64)%Z -> (0 <= k < 64)%Z ->
Z.land x (2^64 - 2^k) = (x - x mod 2^k)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.land_highmask) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.land_highmask)]. Qed.
Lemma land_bit63 : forall x, (0 <= x < 2^64)%Z -> Z.land x 9223372036854775808 = (x - x mod 2^63)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.land_bit63) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.land_bit63)]. Qed.
Lemma land_m63 : forall x, Z.land x 9223372036854775807 = (x mod 2^63)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.land_m63) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.land_m63)]. Qed.
Lemma land_m48 : forall x, Z.land x 281474976710655 = (x mod 2^48)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.land_m48) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.land_m48)]. Qed.
Lemma land_m16 : forall x, Z.land x 65535 = (x mod 2^16)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq1.land_m16) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq1.land_m16)]. Qed.
