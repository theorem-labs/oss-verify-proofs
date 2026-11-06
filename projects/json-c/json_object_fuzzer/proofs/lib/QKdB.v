(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From Stdlib Require Import SpecFloat.
From Flocq.IEEE754 Require BinarySingleNaN. From Flocq.Calc Require Round.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma digits2_pos_size : forall p, digits2_pos p = Pos.size p.
Proof. induction p; cbn; congruence. Qed.

Lemma Zpos_iter_xO : forall p n, Z.pos (Pos.iter xO p n) = Z.pos p * 2 ^ Z.pos n.
Proof.
intros p n. rewrite (Pos.iter_swap_gen _ _ Zpos xO (Z.mul 2)) by reflexivity.
change (Pos.iter (Z.mul 2) (Z.pos p) n) with (Z.shiftl (Z.pos p) (Z.pos n)). apply Z.shiftl_mul_pow2. lia.
Qed.

Lemma Zpos_iter_succ : forall a n, Z.pos (Pos.iter Pos.succ a n) = Z.pos a + Z.pos n.
Proof.
intros a n. rewrite (Pos.iter_swap_gen _ _ Zpos Pos.succ Z.succ) by (intros; apply Pos2Z.inj_succ).
induction n using Pos.peano_ind; [cbn; lia|]. rewrite Pos.iter_succ, IHn, Pos2Z.inj_succ. lia.
Qed.

Lemma size_iter_xO : forall p n, Pos.size (Pos.iter xO p n) = Pos.iter Pos.succ (Pos.size p) n.
Proof. intros p n. apply (Pos.iter_swap_gen _ _ Pos.size xO Pos.succ). reflexivity. Qed.

Lemma size_log2 : forall p, Z.pos (Pos.size p) = Z.log2 (Z.pos p) + 1.
Proof. intros p. destruct p; [ | | reflexivity]; cbn [Z.log2 Pos.size]; lia. Qed.

Lemma cvt_pos : forall p, Z.pos p < 2^31 ->
exists mz ez, fp_of_int fmt_double RNE true 32 (Z.pos p) = (fp_encode fmt_double (S754_finite false mz ez), no_flags)
/\ ez = Z.log2 (Z.pos p) - 52 /\ Z.pos mz = Z.pos p * 2 ^ (- ez) /\ Z.pos (Pos.size mz) = 53.
Proof.
intros p Hp.
pose proof (Z.log2_spec (Z.pos p) ltac:(lia)) as [L1 L2].
assert (HD : 0 <= Z.log2 (Z.pos p) <= 30).
{ split; [apply Z.log2_nonneg|]. destruct (Z.le_gt_cases (Z.log2 (Z.pos p)) 30); [assumption|].
exfalso. assert (2 ^ 31 <= 2 ^ Z.log2 (Z.pos p)) by (apply Z.pow_le_mono_r; lia). lia. }
unfold fp_of_int.
replace (int_wrap 32 (Z.pos p)) with (Z.pos p) by (unfold int_wrap; rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
replace (Z.testbit (Z.pos p) (32 - 1)) with false by (symmetry; apply Z.testbit_false; [lia|]; rewrite Z.div_small by lia; reflexivity).
cbv beta iota delta [andb].
unfold round_scaled, round_exact.
rewrite digits2_pos_size. pose proof (size_log2 p) as SD. set (D := Pos.size p) in *.
replace (fexp (fp_prec fmt_double) (fp_emax fmt_double) (Z.pos D + 0)) with (Z.pos D - 53) by (unfold fexp, emin; cbn [fp_prec fp_emax fmt_double]; lia).
unfold shl_align.
replace (Z.pos D - 53 - 0) with (- Z.pos (Z.to_pos (53 - Z.pos D))) by (rewrite Z2Pos.id by lia; lia).
pose proof (Z2Pos.id (53 - Z.pos D) ltac:(lia)) as SH.
set (sh := Z.to_pos (53 - Z.pos D)) in *. change (- Z.pos sh) with (Z.neg sh).
set (mz := Pos.iter xO p sh).
assert (Dmz : Z.pos (Pos.size mz) = 53) by (subst mz; rewrite size_iter_xO, Zpos_iter_succ; lia).
assert (Vmz : Z.pos mz = Z.pos p * 2 ^ Z.pos sh) by (subst mz; apply Zpos_iter_xO).
exists mz, (Z.pos D - 53).
split; [| split; [lia| split; [rewrite Vmz; f_equal; f_equal; lia | exact Dmz]]].
unfold round_aux.
cbn iota. change (PosDef.Pos.iter xO p sh) with mz.
unfold shr_fexp at 1. cbn [Zdigits2]. rewrite digits2_pos_size, Dmz.
replace (fexp (fp_prec fmt_double) (fp_emax fmt_double) (53 + (Z.pos D - 53)) - (Z.pos D - 53)) with 0 by (unfold fexp, emin; cbn [fp_prec fp_emax fmt_double]; lia).
cbn [shr shr_record_of_loc loc_of_shr_record shr_m BinarySingleNaN.choice_mode flocq_mode Round.round_N Round.cond_incr].
unfold shr_fexp. cbn [Zdigits2]. rewrite digits2_pos_size, Dmz.
replace (fexp (fp_prec fmt_double) (fp_emax fmt_double) (53 + (Z.pos D - 53)) - (Z.pos D - 53)) with 0 by (unfold fexp, emin; cbn [fp_prec fp_emax fmt_double]; lia).
cbn [shr shr_record_of_loc loc_of_shr_record shr_m].
replace (Z.pos D - 53 <=? fp_emax fmt_double - fp_prec fmt_double) with true by (symmetry; apply Z.leb_le; cbn; lia).
cbn [andb mk_round_flags enc fst snd]. reflexivity.
Qed.

Definition encN (mz : positive) (ez : Z) : Z := (ez + 1075) * 2^52 + (Z.pos mz - 2^52).
Lemma encode_normal : forall mz ez, Z.pos (Pos.size mz) = 53 ->
fp_encode fmt_double (S754_finite false mz ez) = encN mz ez.
Proof.
intros mz ez Hs. unfold fp_encode. rewrite Hs. cbn [fp_prec fmt_double Z.ltb Z.compare Pos.compare Pos.compare_cont].
unfold encN, fp_emin, fp_mw, fp_ew. cbn [fp_prec fp_emax fmt_double]. rewrite !Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma decode_normal : forall mz ez, Z.pos (Pos.size mz) = 53 -> -1022 <= ez + 52 <= 1023 ->
fp_decode fmt_double (encN mz ez) = S754_finite false mz ez /\ 0 <= encN mz ez < 2^63.
Proof.
intros mz ez Hs He.
pose proof (Pos.size_gt mz) as G. pose proof (Pos.size_le mz) as L.
apply Pos2Z.pos_lt_pos in G. apply Pos2Z.pos_le_pos in L. rewrite Pos2Z.inj_pow, Hs in G, L. rewrite Pos2Z.inj_xO in L.
assert (R : 0 <= encN mz ez < 2^63) by (unfold encN; lia).
split; [|exact R].
unfold fp_decode, fp_sign_bit, fp_exp_field, fp_man_field.
change (fp_mw fmt_double) with 52. change (fp_ew fmt_double) with 11. change (fp_emin fmt_double) with (-1074). change (52 + 11) with 63.
replace (Z.testbit (encN mz ez) 63) with false by (symmetry; apply Z.testbit_false; [lia|]; rewrite Z.div_small by lia; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. rewrite !Z.land_ones by lia.
replace (encN mz ez / 2 ^ 52) with (ez + 1075) by (unfold encN; rewrite Z.div_add_l by lia; rewrite Z.div_small by lia; lia).
rewrite (Z.mod_small (ez + 1075)) by lia.
replace (encN mz ez mod 2 ^ 52) with (Z.pos mz - 2^52) by (unfold encN; rewrite Z.add_comm, Z.mod_add by lia; rewrite Z.mod_small by lia; lia).
rewrite (proj2 (Z.eqb_neq (ez + 1075) 0)) by lia.
change (Z.ones 11) with 2047. rewrite (proj2 (Z.eqb_neq (ez + 1075) 2047)) by lia.
change (Z.shiftl 1 52) with (2^52).
replace (2^52 + (Z.pos mz - 2 ^ 52)) with (Z.pos mz) by lia. cbn iota. f_equal. lia.
Qed.

Definition lf_facts_b (S : Z) : bool :=
match fp_decode fmt_double (bv_unsigned (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 S)) (Z_to_bv 64 K066))) with
| S754_finite false M E =>
((lf_thr S - 1) * 2 ^ (- E) <? Z.pos M) && (Z.pos M <=? lf_thr S * 2 ^ (- E)) &&
(2 ^ (52 + E) <=? lf_thr S) && (lf_thr S <=? 2 ^ (53 + E)) && Bool.eqb (lf_test RNE S 0) (lf_thr S <=? 0)
| _ => false
end.

Theorem lf_test_spec_proof : lf_test_spec.
Proof.
intros S c HS Hc.
pose proof (lf_thr_lt S HS) as TL. pose proof (lf_size_range S HS) as SR.
assert (C : forallb lf_facts_b lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S HS). unfold lf_facts_b in C.
unfold lf_test in C |- *. set (y := fmul_d _ _ _) in C |- *.
destruct (fp_decode fmt_double (bv_unsigned y)) as [sy|sy| |sy M E] eqn:DY; try discriminate C.
destruct sy; [discriminate C|].
apply andb_prop in C as [C T0]. apply andb_prop in C as [C T4]. apply andb_prop in C as [C T3]. apply andb_prop in C as [T1 T2].
apply Z.ltb_lt in T1. apply Z.leb_le in T2. apply Z.leb_le in T3. apply Z.leb_le in T4. apply Bool.eqb_prop in T0.
assert (HE : E < -21).
{ destruct (Z.lt_ge_cases E (-21)) as [|GE]; [lia|]. assert (2 ^ 31 <= 2 ^ (52 + E)) by (apply Z.pow_le_mono_r; lia). lia. }
assert (KE : 0 < 2 ^ (- E)) by (apply Z.pow_pos_nonneg; lia).
destruct c as [|p|p]; [exact T0| |lia].
destruct (cvt_pos p ltac:(lia)) as (mz & ez & CV & Eez & Vmz & Smz).
pose proof (Z.log2_spec (Z.pos p) ltac:(lia)) as [L1 L2]. pose proof (Z.log2_nonneg (Z.pos p)) as L0.
assert (Hez : -1022 <= ez + 52 <= 1023).
{ split; [lia|]. destruct (Z.le_gt_cases (Z.log2 (Z.pos p)) 30); [lia|]. assert (2^31 <= 2^Z.log2 (Z.pos p)) by (apply Z.pow_le_mono_r; lia). lia. }
destruct (decode_normal mz ez Smz Hez) as [DC RC].
unfold fle_d, fcvt_d_w. rewrite (unsigned_lit (Z.pos p)) by lia. rewrite CV. cbn [fst]. rewrite (encode_normal mz ez Smz). rewrite (unsigned_lit (encN mz ez)) by lia.
unfold fp_le, fp_compare. rewrite DY, DC. cbn [fst SFcompare].
destruct (Z.lt_total E ez) as [LT|[EQ|GT]].
- rewrite (proj2 (Z.compare_lt_iff _ _) LT). cbn. symmetry. apply Z.leb_le.
etransitivity; [exact T4|]. etransitivity; [|exact L1]. apply Z.pow_le_mono_r; lia.
- rewrite (proj2 (Z.compare_eq_iff _ _) EQ).
lazymatch goal with |- ?l = _ => change l with (Z.pos M <=? Z.pos mz) end.
rewrite Vmz. replace (- ez) with (- E) by lia.
destruct (Z.leb_spec (lf_thr S) (Z.pos p)) as [TP|TP].
+ apply Z.leb_le. etransitivity; [exact T2|]. apply Z.mul_le_mono_nonneg_r; lia.
+ apply Z.leb_gt. assert (Z.pos p * 2 ^ (- E) <= (lf_thr S - 1) * 2 ^ (- E)) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
- rewrite (proj2 (Z.compare_gt_iff _ _) GT). cbn. symmetry. apply Z.leb_gt.
eapply Z.lt_le_trans; [exact L2|]. etransitivity; [|exact T3]. apply Z.pow_le_mono_r; lia.
Qed.
