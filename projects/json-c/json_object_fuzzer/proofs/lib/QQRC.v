(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg QZAi QqdR QnDM_c1 QQLG Q91D Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QqdR.
Import QnDM_c1.
Import QQLG.Mq7.
Import Q91D.Mq2.
Import Qy8Z.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac zstep0 := zs.

Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

Lemma shl52_land64 : forall f, (0 <= f)%Z -> Z.land (Z.shiftl f 52) 18446744073709551615 = (4503599627370496 * (f mod 4096))%Z.
Proof.
intros f Hf. rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^64)%Z with (4503599627370496 * 4096)%Z.
change (2^52)%Z with 4503599627370496%Z. rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. reflexivity.
Qed.
Lemma land_bit11 : forall f, Z.land f 2048 = (2048 * ((f / 2048) mod 2))%Z.
Proof. intros. change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia. reflexivity. Qed.
Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. intros. change 1%Z with (2^1 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma signbitl_range : forall x, (0 <= signbitl x <= 1)%Z.
Proof.
intros. unfold signbitl. pose proof (hi64_range x). rewrite Z.shiftr_div_pow2 by lia.
split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma fpclassifyl_range : forall x, (0 <= fpclassifyl x <= 4)%Z.
Proof. intros. unfold fpclassifyl. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : forall (F : bvmap 5 word) (v : word) (k : reg),
bv_unsigned k <> 10%Z -> reg_get (bvmap_set 10 v F) k = reg_get F k.
Proof.
intros F v k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq.
change (bv_unsigned (10 : reg)) with 10%Z. lia.
Qed.

Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
split. { apply Z.lor_nonneg. lia. }
pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
rewrite Z.shiftl_mul_pow2 in * by lia.
replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
nia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
pose proof (bytes_le_to_Z_range bs) as HR.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb_spec0 i 8).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. apply andb_false_r. }
rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
- rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le4, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u32arr_of_u8arr : forall segs_ m A bs k,
u8arr segs_ m A bs -> length bs = (4 * k)%nat ->
exists ws, length ws = k /\ u32arr segs_ m A ws.
Proof.
intros segs_ m A bs k [Hb Hw] HL.
assert (G : forall k bs, length bs = (4 * k)%nat -> exists ws, length ws = k /\ u32s ws = bs).
{ clear. induction k as [|k IH]; intros bs HL.
- exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
- destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
cbn [u32s]. rewrite Hu, le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
- rewrite Hu. exact Hb.
- rewrite Hlen. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma u8arr_of_u32arr : forall segs_ m A ws, u32arr segs_ m A ws -> u8arr segs_ m A (u32s ws).
Proof. intros segs_ m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed.

Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).
Definition wval (ws : list word) (i : Z) : Z := (bv_unsigned (wnth ws i) mod 4294967296)%Z.

Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. intros ws i Hi Hl. unfold wnth. apply nth_error_nth'. exact Hl. Qed.

Lemma wval_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat ->
wval (upd ws (Z.to_nat i) v) i = (bv_unsigned v mod 4294967296)%Z.
Proof.
intros ws i v Hi Hl. unfold wval, wnth.
pose proof (nth_error_upd_same ws (Z.to_nat i) v Hl) as E.
apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
Qed.
Lemma wval_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
wval (upd ws (Z.to_nat i) v) j = wval ws j.
Proof.
intros ws i j v Hi Hj Hij. unfold wval, wnth.
destruct (Nat.lt_ge_cases (Z.to_nat j) (length ws)) as [Hl|Hl].
- pose proof (nth_error_upd_other ws (Z.to_nat i) (Z.to_nat j) v ltac:(lia)) as E.
rewrite (nth_error_nth' ws (Z_to_bv 64 0) Hl) in E.
apply nth_error_nth with (d := Z_to_bv 64 0) in E. rewrite E. reflexivity.
- rewrite !nth_overflow by (rewrite ?upd_length; lia). reflexivity.
Qed.
Lemma wval_range : forall ws i, (0 <= wval ws i < 4294967296)%Z.
Proof. intros. unfold wval. apply Z.mod_pos_bound. lia. Qed.

Lemma div1e9_magic : forall x, (0 <= x < 2^64)%Z ->
Z.shiftr (Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64) 11 = (x / 1000000000)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
change (2^64 * 2^11)%Z with (2^75)%Z. change 1000000000%Z with (512 * 1953125)%Z. rewrite <- Z.div_div by lia.
change (2^9)%Z with 512%Z.
set (y := (x / 512)%Z). assert (Hy : (0 <= y < 2^55)%Z) by (subst y; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clearbody y. clear x Hx.
Z.div_mod_to_equations. nia.
Qed.

Lemma sx32_zero : forall w : word, bv_unsigned (sx32 w) = 0%Z <-> (bv_unsigned w mod 4294967296 = 0)%Z.
Proof.
intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
unfold bv_modulus in R. change (2^64)%Z with 18446744073709551616%Z in *. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
split; intros H; Z.div_mod_to_equations; lia.
Qed.
Lemma sx32_nonzero : forall w : word, bv_unsigned (sx32 w) <> 0%Z <-> (bv_unsigned w mod 4294967296 <> 0)%Z.
Proof. intros w. rewrite sx32_zero. tauto. Qed.

Lemma mulhu_M_range : forall x, (0 <= x < 2^62)%Z ->
(0 <= Z.shiftr (Z.shiftr x 9 * 19342813113834067) 64 < 18446744073709551616)%Z.
Proof.
intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
split. { apply Z.div_pos; [|lia]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. }
apply Z.div_lt_upper_bound; [lia|].
assert (x / 2^9 < 2^53)%Z by (apply Z.div_lt_upper_bound; lia).
assert (0 <= x / 2^9)%Z by (apply Z.div_pos; lia). nia.
Qed.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B QdBa QfYR QfcC Ql2m QDUx Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m.
Import QnDM_c1 QDUx Q9Ay.
Import Qy8Z.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.

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
Proof. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit by lia. vm_compute. reflexivity. Qed.
Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma bv_lts_lit : forall a e, (-2^63 <= a < 2^63)%Z -> (-2^63 <= e < 2^63)%Z -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 e) = (a <? e)%Z.
Proof. intros a e Ha He. unfold bv_lts. rewrite !signed_of_Z by lia. reflexivity. Qed.
Lemma swrap32_land64_add : forall e k, (-2^31 <= e + k < 2^31)%Z -> (-2^31 <= k < 2^31)%Z ->
bv_swrap 32 (Z.land e 18446744073709551615 + k) = (e + k)%Z.
Proof. intros e k H1 H2. rewrite land_W64, swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_shift : forall x k k', (k' = k - 2^64)%Z -> bv_swrap 32 (x + k) = bv_swrap 32 (x + k').
Proof. intros x k k' ->. rewrite !swrap32_eq. f_equal. replace (x + (k - 2^64) + 2147483648)%Z with (x + k + 2147483648 + (- 4294967296) * 4294967296)%Z by lia. rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma swrap32_shift_sub : forall x k k', (k' = 2^64 - k)%Z -> bv_swrap 32 (x - k) = bv_swrap 32 (x + k').
Proof. intros x k k' ->. rewrite !swrap32_eq. f_equal. replace (x + (2^64 - k) + 2147483648)%Z with (x - k + 2147483648 + 4294967296 * 4294967296)%Z by lia. rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma swrap32_landW : forall a c, bv_swrap 32 (Z.land a 18446744073709551615 + c) = bv_swrap 32 (a + c).
Proof.
intros a c. rewrite land_W64, !swrap32_eq. f_equal.
rewrite (Z.mod_eq a (2^64)) by lia.
replace (a - 2 ^ 64 * (a / 2 ^ 64) + c + 2147483648)%Z with ((a + c + 2147483648) + (- (a / 2 ^ 64) * 4294967296) * 4294967296)%Z by lia.
apply Z.mod_add. lia.
Qed.
Lemma swrap32_landW_sub : forall a c, bv_swrap 32 (Z.land a 18446744073709551615 - c) = bv_swrap 32 (a - c).
Proof. intros a c. rewrite <- !Z.add_opp_r. apply swrap32_landW. Qed.
Lemma swrap32_swrap32_add : forall e k, bv_swrap 32 (Z.land (bv_swrap 32 e) 18446744073709551615 + k) = bv_swrap 32 (e + k).
Proof.
intros e k. rewrite swrap32_landW. rewrite !swrap32_eq.
Z.div_mod_to_equations. lia.
Qed.
Lemma bv_lts_0_lit : forall e, (-2^63 <= e < 2^63)%Z -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 e) = (0 <? e)%Z.
Proof. intros e He. unfold bv_lts. rewrite !signed_of_Z by lia. reflexivity. Qed.
Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).
Lemma swrap32_land64_small : forall e, (-2^31 <= e < 2^31)%Z -> bv_swrap 32 (Z.land e 18446744073709551615) = e.
Proof. intros e He. rewrite land_W64, swrap32_eq. Z.div_mod_to_equations; lia. Qed.
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
Proof.
intros a b. unfold f128_le.
repeat (lazymatch goal with |- context [if ?c then _ else _] => destruct c | _ => fail end; try (cbn; lia)).
unfold nez64, b2z. destruct (negb _); cbn; lia.
Qed.
Lemma fpclass_not_nan : forall y, Z.land (Z.shiftr (hi64 y) 48) 0x7fff <> 0x7fff%Z -> (m_fpclassifyl y =? 0) = false.
Proof.
intros y H. unfold m_fpclassifyl.
destruct (Z.land (Z.shiftr (hi64 y) 48) 0x7fff =? 0); [destruct (nz _); reflexivity|].
replace (Z.land (Z.shiftr (hi64 y) 48) 32767 =? 32767) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity.
Qed.
Lemma fpclass_nan : forall y, Z.land (Z.shiftr (hi64 y) 48) 0x7fff = 0x7fff%Z ->
(m_fpclassifyl y =? 0) = nz (Z.lor (lo64 y) (Z.land (hi64 y) 0x0000ffffffffffff)).
Proof.
intros y H. unfold m_fpclassifyl. rewrite H. cbn [Z.eqb]. destruct (nz _); reflexivity.
Qed.
Lemma land_pow2_bit : forall a n, (0 <= n)%Z -> Z.land a (2^n) = (if Z.testbit a n then 2^n else 0)%Z.
Proof.
intros a n Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec n i).
- subst i. destruct (Z.testbit a n); [rewrite Z.pow2_bits_true by lia | rewrite Z.bits_0]; reflexivity.
- rewrite Bool.andb_false_r. destruct (Z.testbit a n); [rewrite Z.pow2_bits_false by lia | rewrite Z.bits_0]; reflexivity.
Qed.
Lemma zbv_u64 : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v.
Proof. intros. apply Z_to_bv_eqm. unfold u64. apply Z.mod_mod. lia. Qed.
Lemma shl48_land64 : forall v, Z.land (Z.shiftl v 48) 18446744073709551615 = Z.shiftl (Z.land v 65535) 48.
Proof.
intros v. change 18446744073709551615%Z with (Z.ones 64). change 65535%Z with (Z.ones 16).
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, !Z.shiftl_spec, Z.land_spec by lia.
destruct (Z.lt_ge_cases (i - 48) 0) as [Hn|Hn].
- rewrite !(Z.testbit_neg_r _ (i - 48)) by lia. reflexivity.
- rewrite !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb_spec0 i 64); destruct (Z.ltb_spec0 (i - 48) 16); try lia; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
Qed.
Lemma pack_hi_range : forall xhi v, (0 <= Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land v 65535) 48) < 2^64)%Z.
Proof.
intros xhi v. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2.
- pose proof (land48_range xhi). change 0x0000ffffffffffff%Z with 281474976710655%Z in H. lia.
- rewrite Z.shiftl_mul_pow2 by lia.
assert (0 <= Z.land v 65535 < 2^16)%Z.
{ split; [apply Z.land_nonneg; right; lia|].
apply QsjA.Z_bounded_by_bits; [lia | apply Z.land_nonneg; right; lia |].
intros k Hk. rewrite Z.land_spec. replace 65535%Z with (Z.ones 16) by reflexivity.
rewrite Z.testbit_ones_nonneg by lia. destruct (Z.ltb_spec0 k 16); [lia|]. apply Bool.andb_false_r. }
change (2^64)%Z with (2^16 * 2^48)%Z. nia.
Qed.
Lemma pack_eq : forall xhi xlo v, (0 <= xlo < 2^64)%Z ->
Z_to_bv 64 (Z.lor (Z.land (Z.shiftl v 48) 18446744073709551615) (Z.land xhi 281474976710655))
= Z_to_bv 64 (hi64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land v 65535) 48)) xlo))
/\ Z_to_bv 64 xlo = Z_to_bv 64 (lo64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land v 65535) 48)) xlo)).
Proof.
intros xhi xlo v Hxlo. pose proof (pack_hi_range xhi v).
rewrite hi64_mk128, lo64_mk128 by lia. split; [|reflexivity].
rewrite shl48_land64, Z.lor_comm. reflexivity.
Qed.
Lemma sbb_bridge : forall xhi xlo yhi ylo, (0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z ->
let hi' := (if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi))%Z in
Z.land (Z.land (xhi - yhi) 18446744073709551615 - Z.b2z (xlo <? ylo)%Z) 18446744073709551615 = hi'
/\ Z_to_bv 64 (Z.land (xhi - yhi) 18446744073709551615 - Z.b2z (xlo <? ylo)%Z) = Z_to_bv 64 hi'
/\ (0 <= hi' < 2^64)%Z /\ u64 (xlo - ylo) = Z.land (xlo - ylo) 18446744073709551615.
Proof.
intros xhi xlo yhi ylo Rxh Rxl Ryh Ryl. cbv zeta. rewrite !land_W64. unfold u64.
destruct (Z.ltb_spec0 xlo ylo); cbn [Z.b2z].
- split; [reflexivity|]. split; [apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; reflexivity|].
split; [apply Z.mod_pos_bound; lia | reflexivity].
- rewrite Z.sub_0_r, Z.mod_mod by lia. split; [reflexivity|]. split; [reflexivity|].
split; [apply Z.mod_pos_bound; lia | reflexivity].
Qed.
Lemma shr63_eqb : forall h, (0 <= h < 2^64)%Z -> (Z.shiftr h 63 =? 0) = (h <? 2^63)%Z.
Proof.
intros h Hh. rewrite Z.shiftr_div_pow2 by lia.
destruct (Z.ltb_spec0 h (2^63)).
- rewrite Z.div_small by lia. reflexivity.
- apply Z.eqb_neq. intros E. assert (h / 2^63 >= 1)%Z by (apply Z.le_ge, Z.div_le_lower_bound; lia). lia.
Qed.
Lemma land63_range : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.land x 0x7fffffffffffffff < 2^64)%Z.
Proof. intros x Hx. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; lia. Qed.
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
Lemma land_m16 : forall x, Z.land x 65535 = (x mod 2^16)%Z.
Proof. intros. change 65535%Z with (2^16 - 1)%Z. apply zb_land_mask. lia. Qed.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

#[using="Type"] Lemma shr48_range : forall h, (0 <= h < 2^64)%Z -> (0 <= Z.shiftr h 48 < 65536)%Z.
Proof. intros h Hh. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

End G.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8 QZAa Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QdBa QfYR.
Import QnDM_c1 QDUx Q9Ay.
Import Q91D.
Import QCa8.
Import QQLG.Mq1.
Import Qy8Z.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition fmodlblk_code (w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 : Z) : list Z :=
[0xe00505d3; 0x0175d51b; 0x02959613; 0x0ff57693; 0x02965613; 0x02068a63; 0x0ff00513; 0x0ea69e63; 0x00000513; 0x01961613; 0x000086b7; 0xfff68693; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x00000513; 0x0e060c63; 0x00165693; 0x00d666b3; 0x0026d713; 0x00e6e6b3; 0x0046d713; 0x00e6e6b3; 0x02969713; 0x03175793; 0x00f6e6b3; 0x555557b7; 0x5557879b; 0x03975713; 0x00e6e6b3; 0xfff6c693; 0x0016d713; 0x00f77733; 0x333337b7; 0x3337879b; 0x40e686b3; 0x00f6f733; 0x0026d693; 0x00f6f6b3; 0x00d706b3; 0x0046d713; 0x00e686b3; 0x0f0f1737; 0xf0f70713; 0x00e6f6b3; 0x01010737; 0x10170713; 0x02e686b3; 0x00004737; 0xf8070713; 0x0186d69b; 0x40d70733; 0x01168693; 0x00d61633; 0x0006a693; 0xfff68693; 0x00c6f633; 0x00100793; 0x00970693; 0x03079793; 0x00f64633; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x00000513; 0x00004737; 0xf8070713; 0x00e686b3; 0x01961613; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x01f5d593; 0x03f59593; 0x03001693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x03f6d693; 0x00159613; 0x01059593; 0x00f69693; 0x03165613; 0x00c6e633; 0x03061613; 0x0105d593; 0x00b665b3; 0x00008067; 0xfb010113; 0x04113423; 0x04813023; 0x02913c23; 0x03213823; 0x03313423; 0x03413023; 0x01513c23; 0x01613823; 0x01713423; 0x01813023; 0x00068993; 0x00060913; 0x00058413; 0x00050493; 0x00000513; w_113; 0x00050613; 0x00058693; 0x00090513; 0x00098593; w_118; 0x04051a63; 0x00048513; 0x00040593; 0x00090613; 0x00098693; w_124; 0x00050613; 0x00058693; w_127; 0x04813083; 0x04013403; 0x03813483; 0x03013903; 0x02813983; 0x02013a03; 0x01813a83; 0x01013b03; 0x00813b83; 0x00013c03; 0x05010113; 0x00008067; 0x00090513; 0x00098593; w_142; 0xfa0502e3; 0x03045b13; 0x00008537; 0x031b1593; 0x0315db93; 0xfff5051b; 0xf8ab86e3; 0xfff00513; 0x00155513; 0x00a47ab3; 0x00a9fa33; 0x00048513; 0x000a8593; 0x00090613; 0x000a0693; w_158; 0x02a04063; 0x00048513; 0x000a8593; 0x00090613; 0x000a0693; w_164; 0x10050863; 0x17c0006f; 0x00199993; 0x0319dc13; 0x0a0b8263; 0x00048993; 0x020c1a63; 0x7b800537; 0xf0050553; 0xd49ff0ef; 0x00050613; 0x00058693; 0x00090513; 0x000a0593; w_179; 0x00050913; 0x00058a13; 0x0305d513; 0xf8850c13; 0xfff00513; 0x01055513; 0x00aaf5b3; 0x00150613; 0x00aa7533; 0x00c5e5b3; 0x00c56533; 0x037c4063; 0x0840006f; 0x03f9d613; 0x00159593; 0x00c5e5b3; 0xfffb8b9b; 0x00199993; 0x077c5463; 0x40a58633; 0x0129b6b3; 0x40d60633; 0xfc064ee3; 0x412989b3; 0x013665b3; 0x06058663; 0x03f9d593; 0x00161613; 0x00b665b3; 0xfcdff06f; 0x7b800537; 0xf0050553; 0xcb1ff0ef; 0x00050613; 0x00058693; 0x00048513; 0x000a8593; w_217; 0x00050993; 0x00058a93; 0x0305d513; 0xf8850b93; 0xf60c14e3; 0xf35ff06f; 0x000c0b93; 0x40a58533; 0x0129b633; 0x40c50533; 0x02054463; 0x412989b3; 0x013565b3; 0x02059063; 0x00000513; w_233; 0x00048613; 0x00040693; w_236; 0xe4dff06f; 0x00058513; 0x03055613; 0x000085b7; 0x02061063; 0x03f9d613; 0x00151693; 0x00199993; 0x00c6e533; 0x0306d693; 0xfffb8b9b; 0xfe0684e3; 0x00bb75b3; 0xfff00693; 0x00010737; 0x0106d613; 0xfff70713; 0x03705463; 0x00ebf733; 0x00d9f4b3; 0x00b765b3; 0x03059593; 0x00c57533; 0x00b56433; 0x00048513; 0x00040593; 0xde5ff06f; 0x078b8793; 0x00d9f433; 0x00e7f733; 0x00b765b3; 0x03059593; 0x00c57533; 0x00b564b3; 0x03800537; 0xf0050553; 0xbbdff0ef; 0x00050613; 0x00058693; 0x00040513; 0x00048593; w_278; 0xda5ff06f; 0x00159593; 0x0015d593; 0x00008067; 0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x01213023; 0x00060413; 0x00004637; 0x04c44a63; 0x03fff4b7; 0x02549493; 0x00000613; 0x00048693; w_295; 0x00008637; 0xfff6061b; 0x08c46863; 0x00000613; 0x00048693; w_301; 0x00050913; 0x0000c637; 0xffd6061b; 0x00058493; 0x00c46463; 0x00060413; 0xffff8537; 0x00250513; 0x0900006f; 0xffffc637; 0x0016061b; 0x06864463; 0x03900493; 0x03149493; 0x00000613; 0x00048693; w_318; 0xffff8637; 0x0746061b; 0x04866a63; 0x00000613; 0x00048693; w_324; 0x00050913; 0xffff4637; 0x0e86061b; 0x00058493; 0x00866463; 0x00060413; 0x00008537; 0xf1a50513; 0x0340006f; 0x00058493; 0x00050913; 0xffffc537; 0x00150513; 0x0200006f; 0x00058493; 0x00050913; 0x0180006f; 0x00058493; 0x00050913; 0x00004537; 0xf8d50513; 0x00a40433; w_347; w_348; w_349; 0x00050613; 0x03041413; 0x01059593; 0x0105d593; 0x00b465b3; 0x03fff537; 0x02451513; 0x00a586b3; 0x00090513; 0x00048593; w_360; 0x01813083; 0x01013403; 0x00813483; 0x00013903; 0x02010113; 0x00008067]%Z.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_4 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_5 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_6 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_7 := zsimp_fast.

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

Lemma land63_range : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.land x 0x7fffffffffffffff < 2^64)%Z.
Proof. intros x Hx. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; lia. Qed.

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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 : Z).
Variables (hi_347 : bv 20).
Variables (lo_348 : bv 12).
Variables (joff_295 joff_301 joff_318 joff_324 joff_349 joff_360 : bv 21).
Variables (G_10768 : Z).
Variables (e_extenddftf2 e_multf3 e_divtf3 : Z).
Hypothesis CODE : code_at segs base (fmodlblk_code w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1468.
Hypothesis D_295 : decode_any (Z_to_bv 32 w_295) = Some (Jal 1 joff_295, 4%Z).
Hypothesis E_295 : is_ecall (Z_to_bv 32 w_295) = false.
Hypothesis D_301 : decode_any (Z_to_bv 32 w_301) = Some (Jal 1 joff_301, 4%Z).
Hypothesis E_301 : is_ecall (Z_to_bv 32 w_301) = false.
Hypothesis D_318 : decode_any (Z_to_bv 32 w_318) = Some (Jal 1 joff_318, 4%Z).
Hypothesis E_318 : is_ecall (Z_to_bv 32 w_318) = false.
Hypothesis D_324 : decode_any (Z_to_bv 32 w_324) = Some (Jal 1 joff_324, 4%Z).
Hypothesis E_324 : is_ecall (Z_to_bv 32 w_324) = false.
Hypothesis D_347 : decode_any (Z_to_bv 32 w_347) = Some (Auipc 10 hi_347, 4%Z).
Hypothesis E_347 : is_ecall (Z_to_bv 32 w_347) = false.
Hypothesis D_348 : decode_any (Z_to_bv 32 w_348) = Some (FLoad FMT_D 10 10 lo_348, 4%Z).
Hypothesis E_348 : is_ecall (Z_to_bv 32 w_348) = false.
Hypothesis D_349 : decode_any (Z_to_bv 32 w_349) = Some (Jal 1 joff_349, 4%Z).
Hypothesis E_349 : is_ecall (Z_to_bv 32 w_349) = false.
Hypothesis D_360 : decode_any (Z_to_bv 32 w_360) = Some (Jal 1 joff_360, 4%Z).
Hypothesis E_360 : is_ecall (Z_to_bv 32 w_360) = false.
Hypothesis ANCH_348 : gw_anch (Z.shiftl (bv_signed hi_347) 12 + (base + 1388) + bv_signed lo_348)%Z G_10768.
Hypothesis LINK_295 : gw_anch (base + 1180 + bv_signed joff_295)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_301 : gw_anch (base + 1204 + bv_signed joff_301)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_318 : gw_anch (base + 1272 + bv_signed joff_318)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_324 : gw_anch (base + 1296 + bv_signed joff_324)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_349 : gw_anch (base + 1396 + bv_signed joff_349)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_360 : gw_anch (base + 1440 + bv_signed joff_360)%Z (e_multf3 + 0)%Z.
Hypothesis RNG_G_10768 : gw_br G_10768 8.
Hypothesis ROM_G_10768 : ro_bytes segs G_10768 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 240; Z_to_bv 8 63].

Local Definition gw_tbl_0 := tt.

Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post gw_tbl_0).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post gw_tbl_1).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post gw_tbl_2).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post gw_tbl_3).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post gw_tbl_4).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post gw_tbl_5).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_6).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post gw_tbl_7).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_8).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post gw_tbl_9).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post gw_tbl_10).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post gw_tbl_11).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post gw_tbl_12).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post gw_tbl_13).
Definition call2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@Qy8Z.Mq0.call2_post segs) call2_post gw_tbl_14).
Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis multf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QCa8.multf3_spec segs e_multf3) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Definition extenddftf2_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.extenddftf2_callv) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.extenddftf2_callv)).
Definition multf3_callq : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.multf3_callq) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.multf3_callq)).

#[using="G_10768 e_extenddftf2 e_multf3 e_divtf3 CODE BASE4 BASER D_295 E_295 D_301 E_301 D_318 E_318 D_324 E_324 D_347 E_347 D_348 E_348 D_349 E_349 D_360 E_360 ANCH_348 LINK_295 LINK_301 LINK_318 LINK_324 LINK_349 LINK_360 RNG_G_10768 ROM_G_10768 extenddftf2_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Definition SCALBNL : Z := (base + 0x46c).
Definition COPYSIGNL : Z := (base + 0x15c).
Definition FABSL : Z := (base + 0x460).

Definition leafq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs)
/\ munch [] m m /\ wmono segs m m /\ mem_inv segs m.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE"] Lemma fabsl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv segs m ->
evt segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FABSL) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs.
intros until X. intros MI. unfold FABSL.
pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH. pose proof (land63_range (hi64 X) ltac:(lia)) as R63.
zs. zs. zs.
apply evt_done. unfold leafq_post. repeat (lazymatch goal with |- ex _ => eexists end).
unfold m_fabsl. rewrite lo64_mk128, hi64_mk128 by lia.
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE"] Lemma copysignl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
mem_inv segs m ->
evt segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom segs)).
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 CODE segs.
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

Definition scalbnl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 D_ONE F) (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 112, q)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - 112) q.

Definition scalbnl_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n : Z),
stk segs m (q - 112) q -> (4096 <= q - 112)%Z -> (q < 2^63)%Z ->
(-2^31 <= n < 2^31)%Z ->
mem_inv segs m ->
evt segs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_scalbnl X n) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCALBNL) fc None m (seg_rom segs)).

#[using="w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 hi_347 lo_348 joff_295 joff_301 joff_318 joff_324 joff_349 joff_360 G_10768 e_extenddftf2 e_multf3 CODE BASE4 BASER D_295 E_295 D_301 E_301 D_318 E_318 D_324 E_324 D_347 E_347 D_348 E_348 D_349 E_349 D_360 E_360 ANCH_348 LINK_295 LINK_301 LINK_318 LINK_324 LINK_349 LINK_360 RNG_G_10768 ROM_G_10768 extenddftf2_spec multf3_spec"] Lemma scalbnl_spec : scalbnl_stmt.
Proof. clear - w_113 w_118 w_124 w_127 w_142 w_158 w_164 w_179 w_217 w_233 w_236 w_278 w_295 w_301 w_318 w_324 w_347 w_348 w_349 w_360 hi_347 lo_348 joff_295 joff_301 joff_318 joff_324 joff_349 joff_360 G_10768 e_extenddftf2 e_multf3 CODE BASE4 BASER D_295 E_295 D_301 E_301 D_318 E_318 D_324 E_324 D_347 E_347 D_348 E_348 D_349 E_349 D_360 E_360 ANCH_348 LINK_295 LINK_301 LINK_318 LINK_324 LINK_349 LINK_360 RNG_G_10768 ROM_G_10768 extenddftf2_spec multf3_spec.
unfold scalbnl_stmt. intros until n. intros ST Q0 Q1 Hn MI.
pose proof (munch_refl [(q - 112, q)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH.
rewrite m_scalbnl_eq. unfold SCALBNL.
zs. carve_frame 32%nat ST.
zs. zs. zs. zs. zs. zs.

assert (FIN : forall mf (x1 x10 x11 x12 x13 x14 x15 x16 x17 x5 x6 x7 x28 x29 x30 x31 : word) x' n',
mem_inv segs mf -> munch [(q - 112, q)]%Z m mf -> wmono segs m mf ->
stk segs mf (q - 112) (q + -32) ->
rw_cells segs mf (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
(-2^20 <= n' < 2^20)%Z ->
fst (scal_reduce X n) = x' -> snd (scal_reduce X n) = n' ->
evt segs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_mul (fst (scal_reduce X n)) (scal_u (snd (scal_reduce X n)))) m)
(MS (mkR x1 (Z_to_bv 64 (q + -32)) gp tp x5 x6 x7 (Z_to_bv 64 n') (Z_to_bv 64 (hi64 x')) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 x')) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x56c)) fc None mf (seg_rom segs))).
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

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache Qy5Y QVbl G.T_rfj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import Qy8Z.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope bv_scope.

Definition shgetc_code (w_71 w_72 w_98 : Z) : list Z :=
[0x00853683; 0x01053603; 0x05853703; 0x00b037b3; 0x40d60833; 0x0105a833; 0x0107f7b3; 0x40d70733; 0x0cb53023; 0x0ce53423; 0x00078463; 0x00b68633; 0x0ac53c23; 0x00008067; 0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00050413; 0x00853583; 0x05853503; 0x0c043603; 0x0c843483; 0x40a586b3; 0x009684b3; 0x00060463; 0x06c4d663; 0x00040513; 0x090000ef; 0x04054c63; 0x0c043683; 0x00843583; 0x01043603; 0x00148493; 0x00068a63; 0x40b60733; 0x409686b3; 0x00e6d463; 0x00d58633; 0x05843683; 0x40b68733; 0x00e48733; 0x0ac43c23; 0x0ce43423; 0x00b6e463; 0xfea58fa3; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067; 0x05843503; 0x00843583; 0x40b50533; 0x00a484b3; 0xfff00513; 0x0ab43c23; 0x0ca43023; 0x0c943423; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067; 0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x00050493; w_71; w_72; 0x00093503; 0x00a13823; 0x00048513; 0x05c000ef; 0xfff00413; 0x02051263; 0x0404b683; 0x00f10593; 0x00100613; 0x00100993; 0x00048513; 0x000680e7; 0x01351463; 0x00f14403; 0x00093503; 0x01013583; 0x02b51263; 0x00040513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x04010113; 0x00008067; w_98; 0xff010113; 0x00113423; 0x00813023; 0x00050413; 0x08852503; 0x02843583; 0x03843603; 0xfff50693; 0x00a6e533; 0x08a42423; 0x00c58c63; 0x04843683; 0x00040513; 0x00000593; 0x00000613; 0x000680e7; 0x00046503; 0x00457593; 0x02043023; 0x02043423; 0x02043c23; 0x02059263; 0x05843583; 0x06043603; 0x03b51513; 0x00c585b3; 0x00b43423; 0x00b43823; 0x43f55513; 0x0100006f; 0x02056513; 0x00a42023; 0xfff00513; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

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

Definition zero4 : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition w0 : word := Z_to_bv 64 0.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_71 w_72 w_98 : Z).
Variables (got_ssp STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (shgetc_code w_71 w_72 w_98).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 544.

Local Definition gw_tbl_0 := tt.

#[using="got_ssp STRING_READ ssp_guard CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Definition SHLIM : Z := (base + 0x0).
Definition SHGETC : Z := (base + 0x38).
Definition UFLOW : Z := (base + 0x100).
Definition TOREAD : Z := (base + 0x18c).

Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells segs m ssp_guard [C8 canary].

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
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(Fp, Fp + 232)%Z] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' Fp (rf_cells T p w (sh_lim0 f) J).

Definition shlim_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (txt : list Z) (f : shfile) (J : rfj) (she shl shc : word),
rw_cells segs m Fp (rf_cells_raw T p w f J she shl shc) ->
sh_ok T txt f -> length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat ->
(0 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= p <= zlength txt)%Z ->
mem_inv segs m ->
evt segs (shlim_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p w f J m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHLIM) fc None m (seg_rom segs)).

#[using="w_71 w_72 w_98 CODE"] Lemma shlim_spec : shlim_stmt.
Proof. clear - w_71 w_72 w_98 CODE.
unfold shlim_stmt. intros until shc. intros FC OK L0 L1 T0 T1 Hp MI.
pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
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

Definition ss_cells (T rpos rend : Z) (mode : word) (cookie shend : Z) (shl shc : word) : list cell :=
[C4 w0; CB 4 zero4; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend);
C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C8 (Z_to_bv 64 STRING_READ); C8 w0; C8 w0;
C8 (Z_to_bv 64 T); C8 w0; C8 w0; C8 w0; C4 w0; C4 w0; C8 w0;
C4 mode; C4 (Z_to_bv 64 M64); C4 w0; CB 4 zero4;
C8 (Z_to_bv 64 cookie); C8 w0; C8 w0; C8 w0;
C8 (Z_to_bv 64 shend); C8 shl; C8 shc;
C8 w0; C8 w0; C8 w0].

#[using="Type"] Lemma rf_cells_ss : forall T p w f, sh_stdio f = true ->
rf_cells T p w f ssJ = ss_cells T (T + sh_rpos f) (rf_rend T p w f) (Z_to_bv 64 M64) (rf_rend T p w f) (rf_rend T p w f)
(Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. intros T p w f ST. unfold rf_cells, ss_cells. rewrite ST. reflexivity. Qed.

Definition toread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T cookie shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 16, q); (Fp, Fp + 232)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - 16) (q)
/\ rw_cells segs m' Fp (ss_cells T T T (Z_to_bv 64 M64) cookie shend shl shc).

Definition toread_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T rpos rend cookie shend : Z) (mode shl shc : word),
rw_cells segs m Fp (ss_cells T rpos rend mode cookie shend shl shc) ->
(mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
(0 <= T /\ T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= cookie < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
stk segs m (q - 16) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv segs m ->
evt segs (toread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T cookie shend shl shc m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TOREAD) fc None m (seg_rom segs)).

#[using="w_71 w_72 w_98 CODE"] Lemma toread_spec : toread_stmt.
Proof. clear - w_71 w_72 w_98 CODE.
unfold toread_stmt. intros until shc. intros FC Hmode RT Rrp Rre Rck Rsh ST SPLO SPF SPF2 Q0 Q1 MI.
pose proof (munch_refl [(q - 16, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
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

End G.
End Mq3.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Qfw3_c1 QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QUZl Q7S0 QGeV QLsg QkQT QWTl QM7w Q8QT QkTt Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QWTl.Mq0 QM7w.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QkTt.Mq5.
Import Qy8Z.Mq1.
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
Variables (ralloc_meta_entry ralloc_slot_entry : Z).
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
Hypothesis AL_ralloc_meta_entry : gw_al ralloc_meta_entry 4.
Hypothesis AL_ralloc_slot_entry : gw_al ralloc_slot_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_0))).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_1)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2)))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3)))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4)))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5)))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_6)))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_7)))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_8)))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9)))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10)))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11)))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_12))).
Definition ram_post : ltac:(gw_rebind_ty (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) gw_tbl_13).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_14)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_15 := (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_14)).
Definition ralloc_meta_stmt : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) gw_tbl_15).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_16)).
Definition ras_post : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) gw_tbl_17).
Definition ralloc_slot_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) gw_tbl_18).

Definition rimplT_ret : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_ret) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_ret)).
#[global] Arguments rimplT_ret {R}%_type_scope o r s Q%_function_scope ms _.
Definition rimplM_membed_steq : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplM_membed_steq) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplM_membed_steq)).
#[global] Arguments rimplM_membed_steq {R}%_type_scope t1 t2 s Q%_function_scope ms _ _.
Definition rimplT_bind : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_bind) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_bind)).
#[global] Arguments rimplT_bind {R}%_type_scope {S}%_type_scope o t f%_function_scope s Q1%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rimplT_reach : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_reach) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_reach)).
#[global] Arguments rimplT_reach {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ralloc_meta_entry ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_ralloc_meta_entry AL_ralloc_slot_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Import Q6q3.
Section RC__1.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved"] Lemma rimplT_steq {R} o (t1 t2 : QUZl.M R) s Q ms :
steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved R o t1 t2 s Q ms.
intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|gw_exact H]. apply eruns_steq. gw_exact Hs.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved"] Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> QUZl.M R') -> QUZl.M R' -> QUZl.M R')
(k : X -> Y -> QUZl.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
rimplT o (P _ kS bS) s QS ms ->
(forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
(forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
rimplT o (P R k bail) s Q ms.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved X Y R o P k bail s QS Q ms.
intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; gw_exact NAT|].
eapply rimplT_bind; [eapply rimplT_reach; gw_exact H|].
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
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
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
Proof. clear - segs. reflexivity. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
forall (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells segs m (errno_addr tp) [C4 errv] -> mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom segs)).

#[using="Type"] Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof. clear - RATP. gw_expose_fam RATP. intros H. gw_exact H. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved"] Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
forall (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells segs m (errno_addr tp) [C4 errv] -> mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved segs RATP ralloc_slot_entry fuel. gw_expose_fam RATP.
intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot _ R' full_lay fuel st sc req k' b') k bail s
(fun r s' ms' => match r with
| Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
| None => False end)).
- apply alloc_slot_nat.
- eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. gw_exact HP.
- intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
- intros s' ms' [].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved"] Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
forall (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] -> mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
(forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
rimplT o (k st1 mo) s' Q ms') ->
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved segs RATP ralloc_meta_entry am_pre. gw_expose_fam RATP.
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

End G.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq9.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Definition alloc_meta_code (w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; w_7; w_8; 0x00093503; w_10; 0x00a13423; w_12; 0x0109a503; w_14; w_15; 0x06051263; 0x00000493; 0x41c655b7; 0x00010613; 0x00843503; 0xe6d5859b; 0x02b605b3; 0x00b13023; 0x01900a13; 0x0200006f; 0x00863583; 0x00858593; 0x00010513; 0x00800613; w_30; 0x00843503; 0x01048493; 0x00950633; 0x00063583; 0xfd458ee3; 0xfe0598e3; 0x00013503; 0x00100593; 0x00a9b423; 0x00b9a823; 0x03043403; 0x00001537; 0x00856463; 0x00001437; 0x0189b503; 0x02050a63; 0x00853583; 0x04a58063; 0x00053603; 0x00b63423; 0x00053583; 0x00853603; 0x00b63023; 0x0189b583; 0x18a59c63; 0x00853583; 0x00b9bc23; 0x18c0006f; 0x0289b583; 0x00058c63; 0x0209b503; 0xfff58593; 0x16c0006f; 0x0009bc23; 0x1700006f; 0x0309b503; 0x0a051063; 0x3a09b483; 0xfff00593; 0x08b48a63; 0x00048e63; 0x008484b3; 0x0d600893; 0x00048513; 0x00000073; 0x04950e63; 0x06c0006f; 0x00000513; 0x0d600893; 0xfff40593; 0x00000073; 0x40a00633; 0x00c5f5b3; 0x00141493; 0x00a58533; 0x3aa9b023; 0x009504b3; 0x0d600893; 0x00048513; 0x00000073; 0x02951a63; 0x3a09b503; 0x03200693; 0xfff00713; 0x00040593; 0x00000613; 0x00000793; w_98; 0x3a99b023; 0x408484b3; 0x00c45413; 0x0289b823; 0x07c0006f; 0x0309b503; 0xfff00593; 0x3ab9b023; 0x00050663; 0x0509b483; 0x0580006f; 0x0389b503; 0x00200593; 0x00a594b3; 0x028485b3; 0x02200693; 0xfff00713; 0xfff00a13; 0x00000513; 0x00000613; 0x00000793; w_120; 0x0f450463; 0xfff48493; 0x0389b583; 0x00c45613; 0x02c48633; 0x008504b3; 0x00158593; 0x02c9b823; 0x02b9bc23; 0x0499b823; 0xfff40513; 0x00957533; 0x08050a63; 0x0309b583; 0x00001637; 0x0489b503; 0x00c48633; 0xfff58593; 0x02b9b823; 0x04c9b823; 0x00050663; 0x00953423; 0x0080006f; 0x0499b023; 0x0089b503; 0x0499b423; 0x00a4b023; 0x0489b503; 0x06500593; 0x00b52823; 0x0489b503; 0x01850513; 0x06400593; 0x02850613; 0x02c9b023; 0x02b9b423; 0x00053423; 0x00053023; 0x00093583; 0x00813603; 0x04c59863; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x04010113; 0x00008067; 0x00300613; 0x00048513; 0x00040593; w_173; 0xf60500e3; w_175; 0x00052503; 0x02600593; 0xf4b508e3; 0x00000513; 0xfadff06f; w_181]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 : Z).
Variables (hi_7 hi_10 hi_14 : bv 20).
Variables (lo_8 lo_12 lo_15 : bv 12).
Variables (joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 : bv 21).
Variables (e_197bc e_24f80 : Z).
Hypothesis CODE : code_at segs base (alloc_meta_code w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 728.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmprotect_entry := (rvm_wait_entry + 240)%Z.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 10 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 10 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 11 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (OpImm ALU_ADD 19 11 lo_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 11 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (OpImm ALU_ADD 8 11 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_98 : decode_any (Z_to_bv 32 w_98) = Some (Jal 1 joff_98, 4%Z).
Hypothesis E_98 : is_ecall (Z_to_bv 32 w_98) = false.
Hypothesis D_120 : decode_any (Z_to_bv 32 w_120) = Some (Jal 1 joff_120, 4%Z).
Hypothesis E_120 : is_ecall (Z_to_bv 32 w_120) = false.
Hypothesis D_173 : decode_any (Z_to_bv 32 w_173) = Some (Jal 1 joff_173, 4%Z).
Hypothesis E_173 : is_ecall (Z_to_bv 32 w_173) = false.
Hypothesis D_175 : decode_any (Z_to_bv 32 w_175) = Some (Jal 1 joff_175, 4%Z).
Hypothesis E_175 : is_ecall (Z_to_bv 32 w_175) = false.
Hypothesis D_181 : decode_any (Z_to_bv 32 w_181) = Some (Jal 1 joff_181, 4%Z).
Hypothesis E_181 : is_ecall (Z_to_bv 32 w_181) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z RGOT_SSP.
Hypothesis ANCH_12 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_12)%Z (RATP + 131960).
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z (RATP + 131728).
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z (e_24f80 + 0)%Z.
Hypothesis LINK_98 : gw_anch (base + 392 + bv_signed joff_98)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_120 : gw_anch (base + 480 + bv_signed joff_120)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_173 : gw_anch (base + 692 + bv_signed joff_173)%Z (rmprotect_entry + 0)%Z.
Hypothesis LINK_175 : gw_anch (base + 700 + bv_signed joff_175)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_181 : gw_anch (base + 724 + bv_signed joff_181)%Z (e_197bc + 0)%Z.
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

Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) gw_tbl_0))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_1))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_11).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUq WMq CH end.
Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
#[using="RGOT_SSP rerrno_loc_entry e_197bc rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmprotect_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition ram_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ (RATP + 131968) <= a < (RATP + 132896)
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

#[using="RNG_RATP"] Lemma ram_fp_alloc_fp st lo sp a : ram_fp st lo sp a -> ralloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. clear - RNG_RATP st lo sp a RATP. gw_expose_fam RATP. unfold ram_fp, ralloc_fp. tauto. Qed.
#[using="Type"] Lemma ram_fp_stack st lo sp a : lo <= a < sp -> ram_fp st lo sp a.
Proof. clear - st lo sp a RATP. gw_expose_fam RATP. intros; left; assumption. Qed.
#[using="Type"] Lemma ram_fp_ctx st lo sp a : (RATP + 131968) <= a < (RATP + 132896) -> ram_fp st lo sp a.
Proof. clear - RATP st lo sp a. gw_expose_fam RATP. intros; right; left; assumption. Qed.
#[using="Type"] Lemma ram_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> ram_fp st lo sp a.
Proof. clear - st lo sp a rid r RATP. gw_expose_fam RATP. intros; right; right. exists rid, r. auto. Qed.
#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_fp_not_errno st lo sp a : ram_fp st lo sp a -> rregions_wf st -> alloc_ceiling <= lo ->
~ (errno_addr (Z_to_bv 64 RATP) <= a < errno_addr (Z_to_bv 64 RATP) + 4).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry RATP st lo sp a. gw_expose_fam RATP.
intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; (gw_expose_fam RATP; unfold alloc_ceiling in *); rewrite ?unsigned_lit by lia; try lia.
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (_ & _ & D23 & D2).
pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
Qed.
#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
conc st q <= a < conc st q + 40 -> ram_fp st lo sp a.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry RATP. gw_expose_fam RATP.
intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply ram_fp_region; [gw_exact Hra | gw_exact NK | lia].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_fp_area : forall st m lo sp ak ar a, rmrep st m -> (s_areas st) !! ak = Some ar ->
conc st ak <= a < conc st ak + 4096 -> ram_fp st lo sp a.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry RATP. gw_expose_fam RATP.
intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st ak ar ra WF Har Hra).
eapply ram_fp_region; [gw_exact Hra | gw_exact NK | lia].
Qed.
#[using="RNG_RATP"] Lemma ram_fp_same st st' lo sp a : s_regions st' = s_regions st -> ram_fp st' lo sp a <-> ram_fp st lo sp a.
Proof. clear - RNG_RATP st st' lo sp a RATP. gw_expose_fam RATP. intros ER. unfold ram_fp. rewrite ER. tauto. Qed.

Definition ram_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ rpres_except (ram_fp stF lo (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

Definition ram_frame (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 junk; C8 rc_canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_tail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv segs m -> meta_slot st q ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt segs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (upd_meta q clr_links st) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x274)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until q. intros MR MI MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
rmeta_chunk MR MSq CH.
(gw_expose_fam RATP; unfold alloc_ceiling, ram_frame in *).
rmeta_open (conc st q) MUq WMq.

st1. st1.
rmeta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
rewrite <- upd_meta_put in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl segs mX) as WMs end.

st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta q clr_links st) mX)
by (eapply rmrep_transport_high; [gw_exact MR2 | gw_exact MUs | gw_exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|gw_exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply ram_fp_stack. lia.
- intros x Hx. eapply ram_fp_meta; [gw_exact MR | gw_exact MSq | lia]. }
apply evt_done. unfold ram_ret_post. do 15 eexists.
split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. gw_exact MR3.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_b0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo cnt : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv segs m -> meta_slot st q -> 0 <= cnt < 2^64 ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt segs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (am_took st q cnt) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) (Z_to_bv 64 cnt) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x268)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until q. intros MR MI MSq HC FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); ((RATP + 131968), (RATP + 132896))]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1.
(gw_expose_fam RATP; unfold alloc_ceiling in *).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 131992), (RATP + 132008))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
gw_expose_fam RATP.

st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
rewrite (conc_aadd st q META_SIZE) by (destruct MSq as (a & ar & k & Ha & Hk & ->); cbn; pose proof MR as (WF' & _);
destruct (rarea_conc st a ar WF' Ha) as (ra & Hra & _); rewrite Hra; eauto).
unfold META_SIZE, wz. gw_exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia. }
clear MUc WMc C1.
change (conc st q) with (conc st1 q).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
[gw_exact MR1 | assumption | gw_exact MSq | gw_exact FR | gw_exact ST | unfold alloc_ceiling; lia | lia]. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|gw_exact WM|].
- eapply rpres_except_trans; [gw_exact MU|]. eapply rpres_except_mono; [gw_exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st st1 lo _ a eq_refl)). gw_exact Ha.
- cbn [ivs_covered]. split; [|split; [|exact I]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. gw_expose_fam RATP. lia. }
split; [eapply wmono_trans; [gw_exact WM| gw_exact WM']|]. split; [gw_exact MI'|]. split; [gw_exact ST'|]. gw_exact MR'.
Qed.

End RC__1.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1.

Import QWTl.Mq5.
Import Q2qa.Mq1 QytA Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq1 QDUx.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import Qy8Z.Mqa.
Import Qy8Z.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
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

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qy8Z.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qy8Z.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qy8Z.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qy8Z.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qy8Z.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qy8Z.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qy8Z.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qy8Z.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))))).

Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimpl_vis_unfold : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimpl_vis_unfold) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimpl_vis_unfold)).
#[global] Arguments rimpl_vis_unfold {R}%_type_scope n k%_function_scope Q%_function_scope ms.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rbytes_at_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rbytes_at_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rbytes_at_agree)).
Definition rwr_at_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rwr_at_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rwr_at_agree)).
Definition rrw_cells_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rrw_cells_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rrw_cells_agree)).
Definition ru64arr_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.ru64arr_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.ru64arr_agree)).
Definition ru8arr_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.ru8arr_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.ru8arr_agree)).

Notation RMallocKit_A2__rbytes_at_agree := rbytes_at_agree (only parsing).
Notation RMallocKit_A2__rrw_cells_agree := rrw_cells_agree (only parsing).
Notation RMallocKit_A2__ru64arr_agree := ru64arr_agree (only parsing).
Notation RMallocKit_A2__ru8arr_agree := ru8arr_agree (only parsing).
Notation RMallocKit_A2__rwr_at_agree := rwr_at_agree (only parsing).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma rmrep_agree_but_ctx : forall st st' m m',
rmrep st m ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
QWTl.Mq5.agree_on m m' (RATP + 131960) 4 -> QWTl.Mq5.agree_on m m' (RATP + 131728) 0x68 -> QWTl.Mq5.agree_on m m' RGOT_SSP 8 -> QWTl.Mq5.agree_on m m' (RATP + 131696) 8 ->
(forall a ar, (s_areas st) !! a = Some ar -> QWTl.Mq5.agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> QWTl.Mq5.agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> QWTl.Mq5.agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
rmrep_ctx st' m' ->
rmrep st' m'.
Proof. clear - RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st st' m m' (WF & CX & GL & AR & GR & SH) ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGA AGG AGR CX'.
assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [gw_exact CX'|split; [|split; [|split]]]].
- destruct WF as (RS & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG, ERs. split; [gw_exact RS|]. split; [gw_exact WR|]. split; [gw_exact DJ|]. split; [gw_exact WA| gw_exact WG].
- destruct GL as (G1 & G2 & G3 & G4 & G5). (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold rmrep_globals in *).
split; [|split; [|split; [|split]]].
+ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact G1|]. eapply QWTl.Mq5.agree_on_sub; [gw_exact AGL| lia| cbn; lia].
+ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact G2|]. eapply QWTl.Mq5.agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact G3|]. eapply QWTl.Mq5.agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact G4|]. eapply QWTl.Mq5.agree_on_sub; [gw_exact AGS1| lia| cbn; lia].
+ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact G5|]. eapply QWTl.Mq5.agree_on_sub; [gw_exact AGS2| lia| cbn; lia].
- intros a ar Ha. rewrite EA in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
unfold rarea_rep. rewrite !Hconc.
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
rewrite PW. split; [|split].
+ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact A1|]. eapply QWTl.Mq5.agree_on_sub; [gw_exact AG| lia| cbn; lia].
+ intros k Hk. rewrite MC, GM. eapply RMallocKit_A2__rrw_cells_agree; [apply A3; gw_exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply QWTl.Mq5.agree_on_sub; [gw_exact AG| lia| lia].
+ eapply RMallocKit_A2__rrw_cells_agree; [gw_exact A4|]. eapply QWTl.Mq5.agree_on_sub; [gw_exact AG| lia| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|gw_exact Hw8].
rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
eapply RMallocKit_A2__rrw_cells_agree; [gw_exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
+ eapply RMallocKit_A2__rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
eapply RMallocKit_A2__rbytes_at_agree; [gw_exact Bt|]. cbn. eapply QWTl.Mq5.agree_on_sub; [gw_exact AG| lia| lia].
Qed.

#[using="Type"] Lemma rmrep_ctx_mid_agree : forall st st' m m',
rmrep st m -> ctx st' = ctx st \/ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
/\ (forall i, unmap_seq st' i = unmap_seq st i) /\ (forall i, bounces st' i = bounces st i) ->
s_regions st' = s_regions st ->
QWTl.Mq5.agree_on m m' ((RATP + 132048)) 832 ->
u64arr segs m' ((RATP + 132048)) (actives st') /\ u64arr segs m' ((RATP + 132432)) (usages st')
/\ u8arr segs m' ((RATP + 132816)) (unmap_seqs st') /\ u8arr segs m' ((RATP + 132848)) (bouncess st').
Proof. clear - segs RATP. gw_expose_fam RATP.
intros st st' m m' (WF & (C1 & C2 & C3 & C4 & C5 & C6) & _) HX ER AG.
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
gw_expose_fam RATP.
split; [|split; [|split]].
- eapply RMallocKit_A2__ru64arr_agree; [gw_exact C2|]. rewrite L1. eapply QWTl.Mq5.agree_on_sub; [gw_exact AG| lia| cbn; lia].
- eapply RMallocKit_A2__ru64arr_agree; [gw_exact C3|]. rewrite L2. eapply QWTl.Mq5.agree_on_sub; [gw_exact AG| lia| cbn; lia].
- eapply RMallocKit_A2__ru8arr_agree; [gw_exact C4|]. rewrite L3. eapply QWTl.Mq5.agree_on_sub; [gw_exact AG| lia| cbn; lia].
- eapply RMallocKit_A2__ru8arr_agree; [gw_exact C5|]. rewrite L4. eapply QWTl.Mq5.agree_on_sub; [gw_exact AG| lia| cbn; lia].
Qed.

#[using="segs RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved"] Lemma rarea_in_live : forall st a ar r x, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof. clear - segs RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved.
intros st a ar r x WF Ha Hr Hx. destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.

#[using="Type"] Lemma rgroup_in_live : forall st b gh r x, rregions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof. clear - segs.
intros st b gh r x WF Hb Hr Hx. destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved"] Lemma rimage_clear_of_ranges_free st lo n x : s_reserved st = ref_reserved -> ranges_free (live_ranges st) lo n = true ->
0x10000 <= x < RIMG_HI -> ~ (lo <= x < lo + n).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RIMG_HI ref_reserved st lo n x. gw_expose_win.
intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF. rewrite ?LAY_ref_reserved in RF.
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
Proof. clear - Hr st m rid r off MR NK LEN OFF OAL RF CEIL RPOS UNIQ r' st'. try gw_hide st'; first [clear r' | gw_hide r' | idtac]; first [clear UNIQ | gw_hide UNIQ | idtac]; first [clear RPOS | gw_hide RPOS | idtac]; first [clear CEIL | gw_hide CEIL | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear OAL | gw_hide OAL | idtac]; first [clear OFF | gw_hide OFF | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear NK | gw_hide NK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="Type"] Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. clear - st m rid r off MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ r' st'. first [clear st' | gw_hide st' | idtac]; first [clear r' | gw_hide r' | idtac]; first [clear UNIQ | gw_hide UNIQ | idtac]; first [clear RPOS | gw_hide RPOS | idtac]; first [clear CEIL | gw_hide CEIL | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear OAL | gw_hide OAL | idtac]; first [clear OFF | gw_hide OFF | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear NK | gw_hide NK | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rgr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof. clear - q rq st m rid r off MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ r' st'. first [clear st' | gw_hide st' | idtac]; first [clear r' | gw_hide r' | idtac]; first [clear UNIQ | gw_hide UNIQ | idtac]; first [clear RPOS | gw_hide RPOS | idtac]; first [clear CEIL | gw_hide CEIL | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear OAL | gw_hide OAL | idtac]; first [clear OFF | gw_hide OFF | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear NK | gw_hide NK | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; try gw_hide rid; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
- rewrite lookup_insert_eq in H. left. split; congruence.
- rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
#[using="Type"] Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. clear - q st m rid r off MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ r' st'. first [clear st' | gw_hide st' | idtac]; first [clear r' | gw_hide r' | idtac]; first [clear UNIQ | gw_hide UNIQ | idtac]; first [clear RPOS | gw_hide RPOS | idtac]; first [clear CEIL | gw_hide CEIL | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear OAL | gw_hide OAL | idtac]; first [clear OFF | gw_hide OFF | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear NK | gw_hide NK | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. clear - st m rid r off MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ r' st'. first [clear st' | gw_hide st' | idtac]; first [clear r' | gw_hide r' | idtac]; first [clear UNIQ | gw_hide UNIQ | idtac]; first [clear RPOS | gw_hide RPOS | idtac]; first [clear CEIL | gw_hide CEIL | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear OAL | gw_hide OAL | idtac]; first [clear OFF | gw_hide OFF | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear NK | gw_hide NK | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
#[using="Hr"] Lemma rgr_conc q : conc st' q = conc st q.
Proof. clear - Hr q st m rid r off MR NK LEN OFF OAL RF CEIL RPOS UNIQ r' st'. first [clear st' | gw_hide st' | idtac]; first [clear r' | gw_hide r' | idtac]; first [clear UNIQ | gw_hide UNIQ | idtac]; first [clear RPOS | gw_hide RPOS | idtac]; first [clear CEIL | gw_hide CEIL | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear OAL | gw_hide OAL | idtac]; first [clear OFF | gw_hide OFF | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear NK | gw_hide NK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; try gw_hide rid; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
- rewrite E, rgr_lookup_new, Hr. reflexivity.
- rewrite rgr_lookup_old by gw_exact NE. reflexivity.
Qed.
#[using="RC__ OFF OAL"] Lemma rgr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. clear - RC__ OFF OAL st m rid r off MR Hr NK LEN RF CEIL RPOS UNIQ r' st'. first [clear st' | gw_hide st' | idtac]; first [clear r' | gw_hide r' | idtac]; first [clear UNIQ | gw_hide UNIQ | idtac]; first [clear RPOS | gw_hide RPOS | idtac]; first [clear CEIL | gw_hide CEIL | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear NK | gw_hide NK | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. rewrite !round_up_pg_aligned; [lia| gw_exact OAL|]. Z.div_mod_to_equations. lia. Qed.

#[using="segs RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO LAY_ref_reserved m MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rgr_regions_wf : rregions_wf st'.
Proof. clear - segs RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO LAY_ref_reserved m MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ st rid r off r' st'. first [clear st' | gw_hide st' | idtac]; try gw_hide r'; try gw_hide off; try gw_hide r; try gw_hide rid; try gw_hide st.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; gw_exact OAL).
split; [gw_exact RS|]. split; [|split; [|split]].
- intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [gw_exact RB0|]. split; [gw_exact RBAL|]. split; [lia|]. split; [lia|].
apply ranges_free_intro. intros b n HI.
pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite RS; gw_exact HI)).
rewrite LAY_ref_reserved in HI. gw_expose_win. destruct HI as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
- intros q1 r1 q2 r2 H1 H2 NE.
assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
{ intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
- left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
- right. gw_exact D. }
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
+ exists ra. rewrite rgr_lookup_old by gw_exact NE. repeat split; assumption.
- intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
exists rb. rewrite rgr_lookup_old by gw_exact NE. auto.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO LAY_ref_reserved MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rmrep_grow_region : rmrep st' m.
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO LAY_ref_reserved MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ st m rid r off r' st'. try gw_hide st'; first [clear r' | gw_hide r' | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m | gw_hide m | idtac]; try gw_hide st.
pose proof MR as (WF & CX & GL & AR & GR & SH).
assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
split; [gw_exact rgr_regions_wf|]. split; [|split; [gw_exact GL|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
replace (ctx_head_cells st') with (ctx_head_cells st) by (unfold ctx_head_cells; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
replace (ctx_tail_cells st') with (ctx_tail_cells st).
2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
split; [gw_exact C1|]. split; [gw_exact C2|]. split; [gw_exact C3|]. split; [gw_exact C4|]. split; [gw_exact C5| gw_exact C6].
- intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4).
unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
split; [gw_exact A1|]. split; [| gw_exact A4]. intros k Hk. rewrite MC. apply A3. gw_exact Hk.
- intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8).
exists w8. rewrite rgr_conc, PW. split; assumption.
- intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
+ exfalso. apply NK. gw_exact Hk.
+ exact (SH q rq H Hk).
Qed.

#[using="Type"] Lemma rptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. clear - P st m rid r off MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ r' st'. first [clear st' | gw_hide st' | idtac]; first [clear r' | gw_hide r' | idtac]; first [clear UNIQ | gw_hide UNIQ | idtac]; first [clear RPOS | gw_hide RPOS | idtac]; first [clear CEIL | gw_hide CEIL | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear OAL | gw_hide OAL | idtac]; first [clear OFF | gw_hide OFF | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear NK | gw_hide NK | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear off | gw_hide off | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros H. gw_exact H. Qed.
End GROW.

#[using="Type"] Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
impl segs (at_node segs) (enode n dec) (epost P) ms ->
(forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
impl segs (at_node segs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof. clear - segs A n dec dec' G P ms.
intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
eapply evt_mono; [gw_exact H|]. intros ms1 [Hat Hk]. split; [gw_exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec' rsp) as [a|] eqn:E.
- destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [gw_exact Hk|]. intros ms' HP; cbn in *. auto.
- cbn. apply evt_done. exact I.
Qed.

End RC__1.

End G.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq7.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import Q8QT.Mq2.
Import QDXD.Mq1.
Import QkTt.Mq5.
Import QCa8.Mq3.
Import Qy8Z.Mqa.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Definition malloc_code (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z) : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x01413023; 0xffffe5b7; 0xfff5859b; 0x0015d593; 0x02b56a63; w_11; 0x00c00593; 0x00b52023; 0x00000513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03; 0x03010113; 0x00008067; 0x00050413; 0x00020537; 0xfec5051b; w_26; w_27; 0x06a46663; 0x01440993; 0x00300613; 0x02200693; 0xfff00713; 0xfff00913; 0x00000513; 0x00098593; 0x00000793; w_37; 0xfb2500e3; 0x00050a13; w_40; w_41; 0x00050863; w_43; w_44; w_45; 0x3984c503; 0x0ff00593; 0x0cb51063; 0x3404bc23; 0x3604b023; 0x3604b423; 0x3604b823; 0x00100513; 0x0ac0006f; 0x00340513; 0x09d00593; w_57; 0x00455a13; w_59; 0x10b46263; 0x001a0513; 0x077cb5b7; 0x0025561b; 0x00a66633; 0x0015551b; 0x53158593; 0x00a66633; 0x0026561b; 0x00a66533; 0x00455613; 0x00a66533; 0x00855613; 0x00a66533; 0x02151613; 0x03165613; 0x00a66533; 0x00150613; 0xfff54513; 0x00a67533; 0x02b50533; 0x01b5551b; 0x00a98533; 0x00054503; 0x07900593; w_85; 0x00251513; 0x07c54513; 0x40a585b3; 0x00159693; w_90; 0x00d586b3; 0x0006d603; 0x06ca6063; 0x07a00613; 0x05c0006f; 0x00150513; 0x38a48c23; 0xba1ff0ef; 0x0c050063; 0x00050913; 0x00000993; 0x01453823; 0x00aa3023; 0x00001537; 0xfe05051b; 0x00a405b3; 0x03358593; 0x8005f593; 0x00a5e533; 0x02a93023; 0x00092e23; 0x00092c23; 0x0144a503; 0x00150513; 0x00a4aa23; 0x1540006f; 0x07800613; 0x40a60633; 0x00161513; 0x00a58533; 0x00055503; 0x00aa3533; 0x00154513; 0x00a66a33; w_125; w_126; 0x00050863; w_128; w_129; w_130; 0x000a059b; 0x00359513; 0x00a48533; 0x05853903; 0x08091e63; 0x00600613; 0x08c58a63; 0xffca059b; 0x01b00613; 0x08b66463; 0x001a7593; 0x00059663; 0x1d853503; 0x02050463; 0x00000913; 0x07c0006f; w_147; w_148; w_149; 0x000a0513; 0x00098593; w_152; 0xdd5ff06f; 0x001a6513; 0x0005059b; 0x00359593; 0x00b485b3; 0x0585b603; 0x1d85b583; 0x00060a63; 0x01862683; 0x00069863; 0x01c62603; 0x00061463; 0x00358593; 0x00d00613; 0x00c5e463; 0x000a0513; 0x0005059b; 0x00359593; 0x00b485b3; 0x0585b903; 0x00050a13; 0x00090663; 0x01892503; 0x0080006f; 0x00000513; 0x40a005bb; 0x00b575b3; 0x02058863; 0x40a0063b; 0x077cb6b7; 0x00c57633; 0x53168693; 0x02d60633; 0x01b6561b; 0x00c98633; 0x00064983; 0x40b5053b; 0x00a92c23; 0x0280006f; 0x000a091b; 0x00090513; 0x00040593; 0x064000ef; 0x04054863; 0x00050993; 0x00391913; 0x01248933; 0x05893903; 0x0144aa03; 0x00048513; w_203; 0x00090513; 0x00098593; 0x00040613; 0x000a0693; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03; 0x03010113; 0x0b90006f; w_216; w_217; w_218; 0xccdff06f]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z).
Variables (hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 : bv 20).
Variables (lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 : bv 12).
Variables (joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 : bv 21).
Hypothesis CODE : code_at segs base (malloc_code w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 880.
Let ralloc_meta_entry := (base + -728)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 11 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 9 11 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_37 : decode_any (Z_to_bv 32 w_37) = Some (Jal 1 joff_37, 4%Z).
Hypothesis E_37 : is_ecall (Z_to_bv 32 w_37) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Auipc 10 hi_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Load SZ1 false 10 10 lo_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_43 : decode_any (Z_to_bv 32 w_43) = Some (Auipc 10 hi_43, 4%Z).
Hypothesis E_43 : is_ecall (Z_to_bv 32 w_43) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (OpImm ALU_ADD 10 10 lo_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis D_57 : decode_any (Z_to_bv 32 w_57) = Some (Auipc 12 hi_57, 4%Z).
Hypothesis E_57 : is_ecall (Z_to_bv 32 w_57) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (OpImm ALU_ADD 19 12 lo_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 12 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_90 : decode_any (Z_to_bv 32 w_90) = Some (OpImm ALU_ADD 11 12 lo_90, 4%Z).
Hypothesis E_90 : is_ecall (Z_to_bv 32 w_90) = false.
Hypothesis D_125 : decode_any (Z_to_bv 32 w_125) = Some (Auipc 10 hi_125, 4%Z).
Hypothesis E_125 : is_ecall (Z_to_bv 32 w_125) = false.
Hypothesis D_126 : decode_any (Z_to_bv 32 w_126) = Some (Load SZ1 false 10 10 lo_126, 4%Z).
Hypothesis E_126 : is_ecall (Z_to_bv 32 w_126) = false.
Hypothesis D_128 : decode_any (Z_to_bv 32 w_128) = Some (Auipc 10 hi_128, 4%Z).
Hypothesis E_128 : is_ecall (Z_to_bv 32 w_128) = false.
Hypothesis D_129 : decode_any (Z_to_bv 32 w_129) = Some (OpImm ALU_ADD 10 10 lo_129, 4%Z).
Hypothesis E_129 : is_ecall (Z_to_bv 32 w_129) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (Auipc 10 hi_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (OpImm ALU_ADD 10 10 lo_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (Jal 1 joff_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_152 : decode_any (Z_to_bv 32 w_152) = Some (Jal 1 joff_152, 4%Z).
Hypothesis E_152 : is_ecall (Z_to_bv 32 w_152) = false.
Hypothesis D_203 : decode_any (Z_to_bv 32 w_203) = Some (Jal 1 joff_203, 4%Z).
Hypothesis E_203 : is_ecall (Z_to_bv 32 w_203) = false.
Hypothesis D_216 : decode_any (Z_to_bv 32 w_216) = Some (Auipc 10 hi_216, 4%Z).
Hypothesis E_216 : is_ecall (Z_to_bv 32 w_216) = false.
Hypothesis D_217 : decode_any (Z_to_bv 32 w_217) = Some (OpImm ALU_ADD 10 10 lo_217, 4%Z).
Hypothesis E_217 : is_ecall (Z_to_bv 32 w_217) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Jal 1 joff_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131960).
Hypothesis ANCH_41 : gw_anch (Z.shiftl (bv_signed hi_40) 12 + (base + 160) + bv_signed lo_41)%Z (RATP + 131731).
Hypothesis ANCH_44 : gw_anch (Z.shiftl (bv_signed hi_43) 12 + (base + 172) + bv_signed lo_44)%Z (RATP + 131960).
Hypothesis ANCH_59 : gw_anch (Z.shiftl (bv_signed hi_57) 12 + (base + 228) + bv_signed lo_59)%Z RDEBRUIJN.
Hypothesis ANCH_90 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_90)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_126 : gw_anch (Z.shiftl (bv_signed hi_125) 12 + (base + 500) + bv_signed lo_126)%Z (RATP + 131731).
Hypothesis ANCH_129 : gw_anch (Z.shiftl (bv_signed hi_128) 12 + (base + 512) + bv_signed lo_129)%Z (RATP + 131960).
Hypothesis ANCH_148 : gw_anch (Z.shiftl (bv_signed hi_147) 12 + (base + 588) + bv_signed lo_148)%Z (RATP + 131960).
Hypothesis ANCH_217 : gw_anch (Z.shiftl (bv_signed hi_216) 12 + (base + 864) + bv_signed lo_217)%Z (RATP + 131960).
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_37 : gw_anch (base + 148 + bv_signed joff_37)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_149 : gw_anch (base + 596 + bv_signed joff_149)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_152 : gw_anch (base + 608 + bv_signed joff_152)%Z (rvm_wait_entry + 524)%Z.
Hypothesis LINK_203 : gw_anch (base + 812 + bv_signed joff_203)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_218 : gw_anch (base + 872 + bv_signed joff_218)%Z (runlock_entry + 0)%Z.
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
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition runlock_post : ltac:(gw_rebind_ty (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq4.runlock_post segs) (@runlock_post) gw_tbl_0).
Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq3.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_1))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_6))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_7))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_8))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11))))))))).

Hypothesis runlock_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.runlock_spec) (base + -1984)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_12))) in let T := gw_fold_pcs T base (-1984)%Z [0; 244]%Z in exact T).

Hypothesis land_m4096 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.land_m4096) (base + 3092)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_12))) in let T := gw_fold_pcs T base (3092)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).

Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).
Definition rmrep_hdr_havoc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_hdr_havoc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_hdr_havoc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).
Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Definition rmrep_set_seq : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_set_seq) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_set_seq)).

Definition rreserved_disjoint2 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rreserved_disjoint2) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rreserved_disjoint2)).
Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).

Definition rmrep_put_group_new : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_put_group_new) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_put_group_new)).
Definition rmrep_set_mmap_counter : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_set_mmap_counter) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_set_mmap_counter)).

#[using="RDEBRUIJN rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_meta_entry rmunmap_entry runlock_spec land_m4096"] Lemma gw_all : True. Proof. exact I. Qed.

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
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by first [reflexivity | (cbn; lia)];
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame segs mX _ _ A bs') in FR; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [cells_size csize Nat.add]; lia];
apply (stk_write segs mX _ _ A bs') in ST; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia];
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ gw_exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); gw_exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section RC__1.

#[using="base rvm_wait_entry ralloc_meta_entry rmunmap_entry"] Lemma rzeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
(forall o, 0 <= o < Z.of_nat k -> bytes_at segs m (x + o) [b8 0]) -> bytes_at segs m x (zeros k).
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmunmap_entry segs.
intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
rewrite nth_error_repeat by gw_exact Hi.
destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
rewrite Z.add_0_r in HB. gw_exact HB.
Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmunmap_entry"] Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmunmap_entry x.
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

#[using="base rvm_wait_entry land_m4096 ralloc_meta_entry rmunmap_entry"] Lemma rbig_word_eq rid n : 0 <= n < 2^63 ->
Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof. clear - base rvm_wait_entry land_m4096 ralloc_meta_entry rmunmap_entry rid n.
intros Hn. rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
replace (n + 4064 + 51) with (n + 4115) by lia.
assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (Z.div_mod_to_equations; lia).
destruct (Z.lt_ge_cases i 12).
- rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
rewrite <- Z.lxor_lor by gw_exact D. rewrite <- Z.add_nocarry_lxor by gw_exact D. Z.div_mod_to_equations. lia.
Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmunmap_entry"] Lemma le4_sxv_succ c : 0 <= c -> le4 (Z_to_bv 64 (bv_unsigned (wz (sxv c)) + 1)) = le4 (wz (u32 (c + 1))).
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmunmap_entry c.
intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
unfold u32. rewrite (QnDM_c1.Mq0.mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmunmap_entry"] Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmunmap_entry c0.
intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
Z.div_mod_to_equations. lia.
Qed.

#[using="rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE ralloc_meta_entry rmunmap_entry"] Lemma rbig_fail1_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
rw_cells segs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk segs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
evt segs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom segs)
/\ stk segs m lo (bv_unsigned sp))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x98)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE ralloc_meta_entry rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until lo. intros FR ST LO SP48.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity| gw_exact ST].
Qed.

#[using="rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE ralloc_meta_entry rmunmap_entry"] Lemma rbig_fail2b_walk :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
rw_cells segs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk segs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
evt segs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom segs)
/\ stk segs m lo (bv_unsigned sp))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x264)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE ralloc_meta_entry rmunmap_entry segs base.
intros until lo. intros FR ST LO SP48.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. split; [reflexivity| gw_exact ST].
Qed.

#[using="runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_147 lo_148 joff_149 joff_152 CODE BASE4 BASER D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 ANCH_148 LINK_149 LINK_152 RNG_RATP runlock_spec ralloc_meta_entry rmunmap_entry"] Lemma rbig_fail2a_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
rw_cells segs m (RATP + 131960) [C4 (wz 0)] ->
evt segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 (base + 0x264)) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960)) xw ndw a2 a3 a4 a5 a6 a7
s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom segs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960)) (wz 0) a1 a2 a3 a4 a5 a6 a7
s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x18c)) fc None m (seg_rom segs)).
Proof. clear - runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_147 lo_148 joff_149 joff_152 CODE BASE4 BASER D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 ANCH_148 LINK_149 LINK_152 RNG_RATP runlock_spec ralloc_meta_entry rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until m. intros LK. gw_expose_fam RATP.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
step. step. step.
eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| gw_exact LK]. }
intros ms' ->.
try g_ret_pc_any.
step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists (a0 a1 : word) m',
ms' = MS (mkR (Z_to_bv 64 (base + 0x18c)) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m' (seg_rom segs)
/\ munch [((RATP + 132816), (RATP + 132848)); ((RATP + 132880), (RATP + 132881))]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -48)
/\ rw_cells segs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
/\ rmrep st' m'.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_40 lo_41 CODE D_40 E_40 D_41 E_41 ANCH_41 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmunmap_entry"] Lemma rbig_seq_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
(lo n : Z) (st : mstate),
rmrep st m -> 0 <= c_seq (ctx st) < 256 ->
bv_unsigned xw <> 2^64 - 1 ->
rw_cells segs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk segs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo -> mem_inv segs m ->
evt segs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960))
xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x98)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_40 lo_41 CODE D_40 E_40 D_41 E_41 ANCH_41 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros MR SEQ XNE FR ST LO ILO MI.
pose proof (munch_refl [((RATP + 132816), (RATP + 132848)); ((RATP + 132880), (RATP + 132881))]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
(gw_expose_fam RATP; unfold ralloc_meta_entry, alloc_ceiling in *). unfold ctx_tail_cells in C6.
replace ((RATP + 132880)) with (RATP + 132880) in C6 by first [reflexivity | (cbn; lia)]. replace ((RATP + 132816)) with (RATP + 132816) in US by first [reflexivity | (cbn; lia)].

step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.

step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.

step. rewrite ?zxb_b8 by lia. step.

assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
rw_cells segs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk segs mj lo (bv_unsigned sp + -48) -> mem_inv segs mj ->
munch [((RATP + 132816), (RATP + 132848)); ((RATP + 132880), (RATP + 132881))]%Z m mj -> wmono segs m mj ->
evt segs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960))
(Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x184)) fc None mj (seg_rom segs))).
{ intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. gw_expose_fam RATP.
replace ((RATP + 132880)) with (RATP + 132880) in C6j by first [reflexivity | (cbn; lia)].
pose proof (rw_cells_store_ok_at segs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (RATP + 132880)) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; gw_expose_fam RATP end.
raw_store_finishR ((RATP + 132880)) [b8 ns] FRj STj MUj WMj SOK.

step.
apply evt_done. (gw_expose_fam RATP; unfold rseq_post, ralloc_meta_entry). do 3 eexists. split; [reflexivity|].
split; [gw_exact MUj|]. split; [gw_exact WMj|]. split; [assumption|]. split; [assumption|]. split; [gw_exact FRj|]. gw_exact MR1. }
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| gw_exact MR| reflexivity| gw_exact FR| gw_exact ST| gw_exact MI| gw_exact MU| gw_exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). gw_exact PO.
-
pose proof (rw_cells_of_u8arr segs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
assert (UZ : u8arr segs m1 (RATP + 132816) (zeros 32)).
{ apply (u8arr_of_rw_cells segs m1 (RATP + 132816) 32). apply (rw_cells_congr segs m1 (RATP + 132816) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| gw_exact USC]. }
clear USC.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with MUc : munch _ m m1, WMc : wmono segs m m1 |- _ =>
assert (MRz : rmrep stz m1);
[ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia]
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia]
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia]
| left; unfold stz; rewrite unmap_seqs_empty; gw_expose_fam RATP; gw_exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia]
| left; gw_expose_fam RATP; replace ((RATP + 132880)) with (RATP + 132880) by first [reflexivity | (cbn; lia)];
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; gw_exact C6 ] |] end.

step. step.
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono segs m ?mX, FRc : rw_cells segs ?mX (bv_unsigned sp + -48) _, STc : stk segs ?mX _ _, MIc : mem_inv segs ?mX |- _ =>
eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| gw_exact MRz| reflexivity| gw_exact FRc| gw_exact STc| gw_exact MIc| gw_exact MUc| gw_exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). gw_exact PO.
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

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved land_m4096 ralloc_meta_entry rmunmap_entry MR TK G0 MSL RR GN AN SHN HC CR NR CLO"] Lemma rbig_succ_walk :
forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
bv_unsigned gw = G ->
rw_cells segs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
stk segs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv segs m ->
evt segs (fun ms' => exists (a0' a1' : word) m',
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960))
a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x324)) fc None m' (seg_rom segs)
/\ munch [(G, G + 40); (x, x + 8); ((RATP + 131980), (RATP + 131984))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -48)
/\ rw_cells segs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
/\ rmrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960))
gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x18c)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved land_m4096 ralloc_meta_entry rmunmap_entry MR TK G0 MSL RR GN AN SHN HC CR NR CLO segs base RATP RGOT_SSP st m g rid x n c lo G. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. try gw_hide G; first [clear lo | gw_hide lo | idtac]; try gw_hide c; try gw_hide n; try gw_hide x; try gw_hide rid; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
pose proof (munch_refl [(G, G + 40); (x, x + 8); ((RATP + 131980), (RATP + 131984))]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
change (meta_word meta0) with 0 in CH.
destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].

destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
assert (HDR : rw_cells segs m x [C8 (wz 0); C1 (b8 0)]).
{ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
- cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
apply rzeros_bytes_at; [lia| cbn; unfold alloc_ceiling in XC; lia|].
intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
- cbn. eapply wr_at_sub; [gw_exact XW| lia| lia]. }

pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
rewrite <- HG in CH.
(gw_expose_fam RATP; unfold alloc_ceiling in *).

step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.

unfold ctx_head_cells in CX1. rewrite HC in CX1.
pose proof (rw_cells_prefix segs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

step. step.

pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl segs m) as WMa.
step.
assert (PWX : pw st (Some (rid, 0)) = wz x).
{ unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CHA : rw_cells segs mX (conc st g) (meta_cells st (big_metaA rid)));
[ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; gw_exact CH
| pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
clear MUa WMa CHA.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl segs mX) as WMb end.
cbv delta [wz]. step.
set (stA := put_meta g (big_metaA rid) st) in MRA.
destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
{ eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
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
- gw_expose_fam RGOT_SSP. lia.
- gw_expose_fam RATP. lia. }
clear MRB0 MUb WMb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
{ eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| gw_exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. gw_exact HDR. }
clear MRB1.

step. step. step. step. step. step.
rewrite (unsigned_lit (n + 4115)) by lia.
assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
step. step. step.
set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
lazymatch goal with H : rw_cells segs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CHC : rw_cells segs mX (conc stB g) (meta_cells stB (big_meta rid n)));
[ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); gw_exact H
| pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
clear MUc WMc CHC MRB.

step. rewrite (sx32_wz_sxv c) by lia. step.

lazymatch goal with H : rw_cells segs ?mX (RATP + 131968) _ |- _ =>
pose proof (rw_cells_store_ok_at segs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (RATP + 131980)) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
clear H end.
st1. rewrite le4_swrap_succ by lia.
set (stC := put_meta g (big_meta rid n) stB) in MRC.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; gw_expose_fam RATP end.
clear MRC.
raw_store_finishR ((RATP + 131980)) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.

step.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|].
split; [gw_exact MRD| gw_exact TKB].
Qed.
End SUCC.

End RC__1.

End G.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq1.
Import QkTt.Mq5.
Import Qy8Z.Mq7.
Import Qy8Z.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z).
Variables (hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 : bv 20).
Variables (lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 : bv 12).
Variables (joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 : bv 21).
Hypothesis CODE : code_at segs base (malloc_code w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 880.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 11 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 9 11 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_37 : decode_any (Z_to_bv 32 w_37) = Some (Jal 1 joff_37, 4%Z).
Hypothesis E_37 : is_ecall (Z_to_bv 32 w_37) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Auipc 10 hi_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Load SZ1 false 10 10 lo_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_43 : decode_any (Z_to_bv 32 w_43) = Some (Auipc 10 hi_43, 4%Z).
Hypothesis E_43 : is_ecall (Z_to_bv 32 w_43) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (OpImm ALU_ADD 10 10 lo_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis D_57 : decode_any (Z_to_bv 32 w_57) = Some (Auipc 12 hi_57, 4%Z).
Hypothesis E_57 : is_ecall (Z_to_bv 32 w_57) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (OpImm ALU_ADD 19 12 lo_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 12 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_90 : decode_any (Z_to_bv 32 w_90) = Some (OpImm ALU_ADD 11 12 lo_90, 4%Z).
Hypothesis E_90 : is_ecall (Z_to_bv 32 w_90) = false.
Hypothesis D_125 : decode_any (Z_to_bv 32 w_125) = Some (Auipc 10 hi_125, 4%Z).
Hypothesis E_125 : is_ecall (Z_to_bv 32 w_125) = false.
Hypothesis D_126 : decode_any (Z_to_bv 32 w_126) = Some (Load SZ1 false 10 10 lo_126, 4%Z).
Hypothesis E_126 : is_ecall (Z_to_bv 32 w_126) = false.
Hypothesis D_128 : decode_any (Z_to_bv 32 w_128) = Some (Auipc 10 hi_128, 4%Z).
Hypothesis E_128 : is_ecall (Z_to_bv 32 w_128) = false.
Hypothesis D_129 : decode_any (Z_to_bv 32 w_129) = Some (OpImm ALU_ADD 10 10 lo_129, 4%Z).
Hypothesis E_129 : is_ecall (Z_to_bv 32 w_129) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (Auipc 10 hi_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (OpImm ALU_ADD 10 10 lo_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (Jal 1 joff_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_152 : decode_any (Z_to_bv 32 w_152) = Some (Jal 1 joff_152, 4%Z).
Hypothesis E_152 : is_ecall (Z_to_bv 32 w_152) = false.
Hypothesis D_203 : decode_any (Z_to_bv 32 w_203) = Some (Jal 1 joff_203, 4%Z).
Hypothesis E_203 : is_ecall (Z_to_bv 32 w_203) = false.
Hypothesis D_216 : decode_any (Z_to_bv 32 w_216) = Some (Auipc 10 hi_216, 4%Z).
Hypothesis E_216 : is_ecall (Z_to_bv 32 w_216) = false.
Hypothesis D_217 : decode_any (Z_to_bv 32 w_217) = Some (OpImm ALU_ADD 10 10 lo_217, 4%Z).
Hypothesis E_217 : is_ecall (Z_to_bv 32 w_217) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Jal 1 joff_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131960).
Hypothesis ANCH_41 : gw_anch (Z.shiftl (bv_signed hi_40) 12 + (base + 160) + bv_signed lo_41)%Z (RATP + 131731).
Hypothesis ANCH_44 : gw_anch (Z.shiftl (bv_signed hi_43) 12 + (base + 172) + bv_signed lo_44)%Z (RATP + 131960).
Hypothesis ANCH_59 : gw_anch (Z.shiftl (bv_signed hi_57) 12 + (base + 228) + bv_signed lo_59)%Z RDEBRUIJN.
Hypothesis ANCH_90 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_90)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_126 : gw_anch (Z.shiftl (bv_signed hi_125) 12 + (base + 500) + bv_signed lo_126)%Z (RATP + 131731).
Hypothesis ANCH_129 : gw_anch (Z.shiftl (bv_signed hi_128) 12 + (base + 512) + bv_signed lo_129)%Z (RATP + 131960).
Hypothesis ANCH_148 : gw_anch (Z.shiftl (bv_signed hi_147) 12 + (base + 588) + bv_signed lo_148)%Z (RATP + 131960).
Hypothesis ANCH_217 : gw_anch (Z.shiftl (bv_signed hi_216) 12 + (base + 864) + bv_signed lo_217)%Z (RATP + 131960).
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_37 : gw_anch (base + 148 + bv_signed joff_37)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_149 : gw_anch (base + 596 + bv_signed joff_149)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_152 : gw_anch (base + 608 + bv_signed joff_152)%Z (rmunmap_entry + 0)%Z.
Hypothesis LINK_203 : gw_anch (base + 812 + bv_signed joff_203)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_218 : gw_anch (base + 872 + bv_signed joff_218)%Z (runlock_entry + 0)%Z.
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
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_0))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_1))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_2)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_3)))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_4)))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_5)))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_6)))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_7)))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_8)))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_9)))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_10)))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_11)))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_12)))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq7.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_13))))).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_14)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_15 := (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq7.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_14))).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).
Definition rfresh_image : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rfresh_image) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rfresh_image)).

Definition rauxv_ok_pres : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq1.rauxv_ok_pres) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq1.rauxv_ok_pres)).

Definition rreserved_disjoint2 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rreserved_disjoint2) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rreserved_disjoint2)).
Definition rmalloc_fp_mono : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmalloc_fp_mono) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmalloc_fp_mono)).

#[using="RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmunmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1.

Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
(t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv segs m1 ->
stk segs m1 lo (bv_unsigned sp + -48) ->
rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells segs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
(forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
0 <= c_mmap_counter (ctx st2) < 2^32 ->
slot_ok st2 g b r idx n ->
(expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 (Some (g, idx))) s' Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960))
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x324)) fc None m1 (seg_rom segs)).

Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st2 m1 -> ticks_ok st2 -> mem_inv segs m1 -> stk segs m1 lo (bv_unsigned sp) ->
rw_cells segs m1 (errno_addr tp) [C4 errv] -> errv = Z_to_bv 64 12 -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 None) s' Q
(MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom segs)).

#[using="RIMG_HI rvm_wait_entry RNG_RATP LAY_hi_RATP LAY_win_4 rmmap_entry rmunmap_entry"] Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
lo <= a < sp \/ a < alloc_ceiling.
Proof. clear - RIMG_HI rvm_wait_entry RNG_RATP LAY_hi_RATP LAY_win_4 rmmap_entry rmunmap_entry st st2 lo sp m0 m2 a RATP. gw_expose_fam RATP.
intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; gw_exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. gw_expose_fam RATP. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

#[using="RIMG_HI rvm_wait_entry RNG_RATP LAY_hi_RATP LAY_win_4 rmmap_entry rmunmap_entry"] Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs :
rmrep st m0 -> rmrep st2 m2 ->
rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells segs m A cs ->
sp' <= A -> alloc_ceiling <= A -> rw_cells segs m' A cs.
Proof. clear - RIMG_HI rvm_wait_entry RNG_RATP LAY_hi_RATP LAY_win_4 rmmap_entry rmunmap_entry segs st st2 lo sp' m0 m m' m2 A cs.
intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [gw_exact PE| gw_exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

#[using="rvm_wait_entry rmmap_entry rmunmap_entry"] Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof. clear - rvm_wait_entry rmmap_entry rmunmap_entry st st2 lo sp1 sp2 a.
intros H [[X|X]|X]; [left; left; lia| left; right; gw_exact X| right; gw_exact X].
Qed.

#[using="Type"] Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. clear - st sta stb lo sp a. intros [HR _ _] H. eapply rmalloc_fp_mono; [gw_exact HR| gw_exact H]. Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved rmmap_entry rmunmap_entry"] Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
RDATA_LO <= a < RIMG_HI -> (RATP + 131968) <= a < (RATP + 132896) \/ (RATP + -164) <= a < (RATP + -164 + 4).
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved rmmap_entry rmunmap_entry RATP RIMG_HI RDATA_LO st st2 lo sp m0 m2 a. gw_expose_fam RATP.
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
- left. gw_exact H.
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
-
exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved rmmap_entry rmunmap_entry"] Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B :
rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved rmmap_entry rmunmap_entry st st2 lo sp m0 m2 m m' B RATP. gw_expose_fam RATP.
intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [gw_exact AUX| gw_exact PE| |].
- intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). unfold alloc_ceiling in *. lia.
- intros a Ha Hfp. gw_expose_fam RATP.
destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; gw_expose_fam RATP; lia.
Qed.

End RC__1.

End G.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq3.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 : Z).
Variables (hi_6 hi_26 hi_31 hi_93 : bv 20).
Variables (lo_7 lo_27 lo_32 lo_94 : bv 12).
Variables (joff_245 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (ntf_code w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 984.
Hypothesis D_6 : decode_any (Z_to_bv 32 w_6) = Some (Auipc 12 hi_6, 4%Z).
Hypothesis E_6 : is_ecall (Z_to_bv 32 w_6) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Load SZ8 true 9 12 lo_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 16 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 18 16 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Auipc 16 hi_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis D_32 : decode_any (Z_to_bv 32 w_32) = Some (OpImm ALU_ADD 16 16 lo_32, 4%Z).
Hypothesis E_32 : is_ecall (Z_to_bv 32 w_32) = false.
Hypothesis D_93 : decode_any (Z_to_bv 32 w_93) = Some (Auipc 13 hi_93, 4%Z).
Hypothesis E_93 : is_ecall (Z_to_bv 32 w_93) = false.
Hypothesis D_94 : decode_any (Z_to_bv 32 w_94) = Some (OpImm ALU_ADD 13 13 lo_94, 4%Z).
Hypothesis E_94 : is_ecall (Z_to_bv 32 w_94) = false.
Hypothesis D_245 : decode_any (Z_to_bv 32 w_245) = Some (Jal 1 joff_245, 4%Z).
Hypothesis E_245 : is_ecall (Z_to_bv 32 w_245) = false.
Hypothesis ANCH_7 : gw_anch (Z.shiftl (bv_signed hi_6) 12 + (base + 24) + bv_signed lo_7)%Z RGOT_SSP.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131968).
Hypothesis ANCH_32 : gw_anch (Z.shiftl (bv_signed hi_31) 12 + (base + 124) + bv_signed lo_32)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_94 : gw_anch (Z.shiftl (bv_signed hi_93) 12 + (base + 372) + bv_signed lo_94)%Z (RATP + 131968).
Hypothesis LINK_245 : gw_anch (base + 980 + bv_signed joff_245)%Z (e_197bc + 0)%Z.
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

Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qy8Z.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_0)).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_1))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_6))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_7))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_8))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rmrep_set_active : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_set_active) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_set_active)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_refl : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_refl) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_refl)).

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_active_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_active_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_active_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rfree_fp_ctx : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_ctx) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_ctx)).
Definition rfree_fp_meta : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_meta) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_meta)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.
Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

#[using="RGOT_SSP e_197bc RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 D_245 E_245 ANCH_7 ANCH_27 ANCH_32 ANCH_94 LINK_245 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [gw_exact MRold | gw_exact MSq | gw_exact MUq | gw_exact WMq |];
eapply rw_cells_congr; [ | | | gw_exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; tauto]);
clear MUq WMq CH end.
Section RC__1.

Definition rqpath_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (g : aptr) (m : word -> option byte) (st' : mstate) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a0 a2 a3 a5 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x380)) fc None m' (seg_rom segs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -96)
/\ rw_cells segs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved"] Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
conc st q = conc st g -> q = g.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved.
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

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 hi_93 lo_94 CODE D_93 E_93 D_94 E_94 ANCH_94 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rntf_qpath : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
rmrep st m -> mem_inv segs m -> meta_slot st g -> 0 <= sc < 48 ->
(active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
(active st sc <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
qa_facts st sc g ->
rw_cells segs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rqpath_post ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc lo st g m (qpath_st st sc g) fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (Z_to_bv 64 sc) a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x164)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 hi_93 lo_94 CODE D_93 E_93 D_94 E_94 ANCH_94 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR MI MSL SC ACT GNP QF FR FRL ST LO LOLE.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
(gw_expose_fam RATP; unfold alloc_ceiling in *).

st1. st1. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.

pose proof (rmrep_active_read st m sc (wa ((RATP + 132048) + 8 * sc)) MR SC eq_refl) as RDA. gw_expose_fam RATP.
st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1. st1.
replace (Z_to_bv 64 ((RATP + 131968) + sc * 8 + 80)) with (wa ((RATP + 132048) + 8 * sc)) by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. if_cases K; zify_cond K.
{
assert (HA : active st sc = Some g).
{ destruct ACT as [A0|(q & Aq & MSq)].
- exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
- rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
rewrite (rconc_meta_inj st m g q MR MSL MSq K). reflexivity. }
unfold qpath_st. rewrite HA, optr_eqb_refl.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [apply rpres_except_refl|]. split; [gw_exact WM|]. split; [gw_exact MI|]. split; [gw_exact ST|]. split; [gw_exact FR|gw_exact MR]. }
assert (HA : active st sc <> Some g).
{ intros E. apply K. rewrite E. unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
destruct (GNP HA) as [GN GP].
assert (QS : qpath_st st sc g = queue_st (LActive sc) g st).
{ unfold qpath_st. destruct (active st sc) as [h|]; [|reflexivity].
replace (optr_eqb (Some h) (Some g)) with false; [reflexivity|]. symmetry. cbn [optr_eqb]. apply aptr_eqb_neq. congruence. }
rewrite QS. clear QS K.

rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
clear CH.

st1. destruct (active st sc) as [hd|] eqn:HD.
-
destruct (QF hd HD ltac:(congruence)) as (MSh & pv & Hpv & NEp & MSp).
assert (NEh : hd <> g) by congruence.
pose proof (rmeta_slot_bounds st m hd MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st hd, conc st hd + 40)]%Z m) as MU.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1.
rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) MRa GP GN.
set (stA := put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) in MRa.
assert (MSha : meta_slot stA hd) by (apply meta_slot_put_meta; gw_exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta; gw_exact MSL).

rmeta_chunk MRa MSha CHh. unfold stA in CHh. rewrite get_meta_rec_put_other in CHh by gw_exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1. clear CHh.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH. unfold stA in CH. rewrite ?get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_next] in CH. rewrite ?GP in CH. cbn [oconc] in CH.
st1.
rmeta_close2 MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) stA) MR1 GP GN.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) st) in MR1.
assert (MSh1 : meta_slot st1 hd) by (apply meta_slot_put_meta; gw_exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; gw_exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta; gw_exact MSp).

rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1 in CH. rewrite !get_meta_rec_put_other in CH by (gw_exact NEp).
st1.
rmeta_close2 MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2 GP GN.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 hd) by (apply meta_slot_put_meta; gw_exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; gw_exact MSg1).

rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; gw_exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_prev m_set_next oconc] in CH.
st1. clear CH. st1.

rmeta_open (conc st hd) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close2 MR2 MSh2 MUh WMh CH (put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2) MR3 GP GN.
assert (EQ3 : queue_st (LActive sc) g st = put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2).
{ unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_link.
rewrite !upd_meta_put, Hpv. cbn iota. rewrite !upd_meta_put.
unfold st2, st1. rewrite (get_meta_rec_put_other st g _ pv NEp). reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia].
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSp | lia].
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSh | lia]. }
split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|gw_exact MR3].
-
unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); ((RATP + 131968), (RATP + 132896))]%Z m) as MU.

st1.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1.
rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) MRb GP GN.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) in MRb.

pose proof MRb as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok segs _ _ (actives stB) sc (Z_to_bv 64 ((RATP + 131968) + sc * 8 + 80)) ACTS
ltac:(rewrite actives_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa ((RATP + 132048) + 8 * sc)) (le8 (pw stB (Some g))))
by ((gw_expose_fam RATP; unfold pw, wz); cbn [oconc]; f_equal; unfold wa; f_equal; lia);
pose proof (rmrep_set_active stB mX sc (Some g) MRb SC) as MR3
end.
assert (EQ3 : queue_st (LActive sc) g st = set_active sc (Some g) stB).
{ unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_single. rewrite upd_meta_put. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3 SOK.

pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX (wa ?A) ?bs) _) =>
pose proof (length_le8 (pw stB (Some g))) as L8;
apply (rw_cells_frame segs mX _ _ A bs) in FR; [|gw_expose_fam RATP; lia|rewrite L8; gw_expose_fam RATP; lia|rewrite L8, FRL; gw_expose_fam RATP; cbn; lia];
apply (stk_write segs mX _ _ A bs) in ST; [|gw_expose_fam RATP; lia|rewrite L8; gw_expose_fam RATP; lia];
apply (munch_write _ _ mX A bs) in MU; [|gw_expose_fam RATP; lia|rewrite L8; gw_expose_fam RATP; lia|rewrite L8; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs) in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs) in HI;
[| rewrite L8; destruct ACTS as [_ AW]; gw_expose_fam RATP; apply (wr_at_store_ok segs mX _ _ (8 * sc) 8 AW); [lia| rewrite actives_length; lia] ]
end;
remember (write_to_mem mX (wa A) bs) as m3 eqn:Em3; clear Em3 L8 ACTS
end.
apply evt_done. unfold rqpath_post. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia].
+ apply rfree_fp_ctx. gw_expose_fam RATP. lia. }
split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|gw_exact MR3].
Qed.

End RC__1.

End G.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq4.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QCa8.Mq4.
Import Qy8Z.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition realloc_code (w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 : Z) : list Z :=
[0x0040006f; 0x04050863; 0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x01613023; 0xffffe637; 0xfff6061b; 0x00165613; 0x02c5e263; w_15; 0x00050593; 0x00000513; 0x00c00613; 0x00c5a023; 0x3cc0006f; 0x00058513; 0x8ccff06f; 0x00f57613; 0x00060463; 0x00000023; 0xffc54603; 0xffd54883; 0xffe55803; 0x00060e63; 0x00080463; 0x00000023; 0xff856803; 0x01085613; 0x00061463; 0x00000023; 0x00481613; 0x40c506b3; 0xff06b483; 0x0104b603; 0xff068693; 0x01f8f293; 0x00d60463; 0x00000023; 0x0204b703; 0x01f77313; 0x00537463; 0x00000023; 0x0184a783; 0x00100693; 0x005696bb; 0x00d7f7b3; 0x00078463; 0x00000023; 0x01c4a783; 0x00d7f6b3; 0x00068463; 0x00000023; 0xfffff6b7; w_59; 0x00d4f6b3; 0x0006b683; w_62; 0x00f68463; 0x00000023; 0x03471693; 0x02f00e13; w_67; 0x03a6d693; 0x00169393; w_70; 0x02de6463; 0x00778e33; 0x000e5e03; 0x025e0eb3; 0x01d87463; 0x00000023; 0x00128e93; 0x03ce8e33; 0x01c87863; 0x0100006f; 0x03f00e13; 0x01c68463; 0x00000023; 0x00c75e13; 0x000e0c63; 0x008e1e13; 0xfffe0e13; 0x010e7463; 0x00000023; 0x1e030663; 0x007783b3; 0x0003d803; 0x00481813; 0x025802b3; 0x0a000e13; 0x005602b3; 0x01028313; 0x01030833; 0xffc80293; 0x0058d393; 0x03c8e663; 0x00500893; 0x01138463; 0x00000023; 0xff886383; 0x00400893; 0x0078e463; 0x00000023; 0xff784883; 0x00088463; 0x00000023; 0x40a288b3; 0x0078f463; 0x00000023; 0x40728933; 0x00094383; 0x00038463; 0x00000023; 0x0002c383; 0x00038463; 0x00000023; 0x000203b7; 0xfeb38e1b; 0x08be6c63; 0x08b8ea63; 0x00358613; 0x09d00713; 0x00465613; 0x18e5e063; 0x00160713; 0x077cb8b7; 0x0027531b; 0x00e36333; 0x0017571b; 0x00e36333; 0x0023531b; 0x00e36733; 0x00475313; 0x00e36733; 0x00875313; 0x00e36733; 0x00170313; 0xfff74713; 0x00e37733; w_145; 0x53188893; w_147; 0x03170733; 0x01b7571b; 0x00e30733; 0x00074703; 0x00271713; 0x07c74713; 0x07900893; 0x40e888b3; 0x00189893; 0x011788b3; 0x0008d883; 0x0f166463; 0x07a00893; 0x0e40006f; 0xfec3839b; 0x1075e063; 0x03000793; 0x0ef6ec63; 0x03f00793; 0x00f68463; 0x00000023; 0x00001a37; 0x406509b3; 0xfffff6b7; 0xfffa0a1b; 0x014587b3; 0x013787b3; 0x01478793; 0x00d7f433; 0x00d77733; 0x02870663; 0x00100693; 0x00050a93; 0x00060513; 0x00058b13; 0x00070593; 0x00040613; w_185; 0x000b0593; 0x00050613; 0x000a8513; 0xfff00693; 0x08d60a63; 0x0204b703; 0x01360533; 0x008606b3; 0x01050513; 0x014777b3; 0xffc68713; 0x00a585b3; 0x0087e7b3; 0x40b7083b; 0x00c4b823; 0x02f4b023; 0xfe068e23; 0x0c080863; 0x40b7063b; 0x40c005bb; 0x00b70733; 0x00500593; 0x00070023; 0x0cb64063; 0xfe068ba3; 0xfec6ac23; 0x0b80006f; 0xfffff837; 0x01077833; 0xff080813; 0xe19ff06f; 0x07800893; 0x40e88733; 0x00171893; 0x011787b3; 0x0007d783; 0x00f63633; 0x00164613; 0x00c76633; 0x0016061b; 0x04d65263; 0x00050493; 0x00058413; 0x00058513; 0xd8dfe0ef; 0x08050063; 0x409905b3; 0x00040613; 0x00b46463; 0x00058613; 0x00050413; 0x00048593; w_238; 0x00048513; 0xbd8fe0ef; 0x00040513; 0x0540006f; 0x00a585b3; 0x40b2863b; 0x02060463; 0x40b2863b; 0x40c005bb; 0x00b282b3; 0x00500593; 0x00028023; 0x00b64c63; 0xfe080ba3; 0xfec82c23; 0x0100006f; 0x00000593; 0x0080006f; 0x00060593; 0xffd54603; 0x01f67613; 0x00559593; 0x00c5e5b3; 0xfeb50ea3; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x00013b03; 0x04010113; 0x00008067]%Z.

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
Variables (e_24f80 : Z).
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
Hypothesis LINK_238 : gw_anch (base + 952 + bv_signed joff_238)%Z (e_24f80 + 0)%Z.
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

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))).

Hypothesis land_pow2_testbit : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.land_pow2_testbit) (base + -5788)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-5788)%Z [0; 244]%Z in exact T).
Hypothesis sllw1_word' : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.sllw1_word') (base + -5788)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-5788)%Z [0; 244]%Z in exact T).

Hypothesis zx32_wz : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq3.gw_all) (@Qy8Z.Mq3.zx32_wz) (base + -6248)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-6248)%Z [0; 36; 80; 108; 180; 260]%Z in exact T).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rmrep_shadow_read2 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read2) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read2)).
Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_group_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_group_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_group_read)).
Definition rmrep_area_check_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_area_check_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_area_check_read)).
Definition rmrep_ctx_secret_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_ctx_secret_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_ctx_secret_read)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RDEBRUIJN rerrno_loc_entry rmremap_entry e_24f80 RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_15 E_15 D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 D_145 E_145 D_147 E_147 D_185 E_185 D_238 E_238 ANCH_62 ANCH_70 ANCH_147 LINK_15 LINK_185 LINK_238 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmremap_entry land_pow2_testbit sllw1_word' zx32_wz"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rrealloc_entry : Z := (base + 0x4).

Definition rrhead_post (ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (G B sc mword stride idx E rsv : Z) : machine_state -> Prop :=
fun ms' => exists t2 t3 t4,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp
(Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) t2
s0 (wz G)
a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 (RDEBRUIJN + 32)) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - bv_unsigned a0))
(Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1e8)) fc None m0 (seg_rom segs).

#[using="rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 hi_59 hi_67 lo_62 lo_70 CODE D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 ANCH_62 ANCH_70 land_pow2_testbit sllw1_word' zx32_wz rmremap_entry"] Lemma rr_head_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m0 : mem)
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret r32 : Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
let stride := if (maplen =? 0) || negb (last_idx =? 0) then 16 * size_class sc else maplen * 4096 - 16 in
let E := B + 16 + stride * idx + stride - 4 in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes segs m0 (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes segs m0 (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes segs m0 (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes segs m0 (wa B) 8 = Some (le8 (wz G)) ->
rw_cells segs m0 G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes segs m0 (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes segs m0 (wa (RATP + 131968)) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes segs m0 (wa ((RDEBRUIJN + 32) + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
(maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
16 <= stride -> P <= E -> E + 1 <= 2^64 ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at segs m0 (E - 4) (le4 (wz r32)) /\ bytes_at segs m0 (E - 5) [b8 0]) ->
rsv <= E - P -> bytes_at segs m0 (E - rsv) [b8 0] -> bytes_at segs m0 E [b8 0] ->
evt segs (rrhead_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m0 G B sc mword stride idx E rsv)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5c)) fc None m0 (seg_rom segs)).
Proof. clear - rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 hi_59 hi_67 lo_62 lo_70 CODE D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 ANCH_62 ANCH_70 land_pow2_testbit sllw1_word' zx32_wz rmremap_entry segs base RATP RDEBRUIJN. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN.
intros until next. intros idx mword stride E rsv0 rsv HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }

st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }

st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
st1.
assert (RG' : ov_read_bytes segs m0 (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
{ replace (P - off16 * 16 + -16) with B by lia. gw_exact RG. }
st1.
set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }

st1. rewrite sx32_wz_sxv by lia. st1. st1.
rewrite sllw1_word' by lia.
assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); gw_exact Hav).
assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); gw_exact Hfr).
st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

pose proof (sxv_range freed) as SXF.
st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. gw_expose_fam RATP. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1.
assert (MW12 : Z.shiftr mword 12 = maplen).
{ subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia. }
assert (MWP : mword - mword mod 4096 = 4096 * maplen).
{ subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia. }
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
pose proof (bytes_at_read segs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
pose proof (bytes_at_read segs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
assert (HBW : bv_unsigned (wz B) = B) by (apply wz_unsigned; lia).

assert (K0c : forall a7v t3v t4v,
evt segs (rrhead_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m0 G B sc mword stride idx E rsv)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) (Z_to_bv 64 rsv) s0 gw
a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 (RDEBRUIJN + 32)) (Z_to_bv 64 (E + 4)) a7v
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
F (Z_to_bv 64 (base + 0x1c0)) fc None m0 (seg_rom segs))).
{ intros a7v t3v t4v.

st1. st1. if_cases Ka; zify_cond Ka. 2:{ exfalso. rewrite ?unsigned_lit in Ka by lia. lia. }

st1. replace (E - rsv) with (E - rsv) by lia.
change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
st1. st1. if_cases Kb; zify_cond Kb. 2:{ exfalso. apply Kb. reflexivity. }

change (Z_to_bv 64 E) with (wa E).
st1. st1. if_cases Kc; zify_cond Kc. 2:{ exfalso. apply Kc. reflexivity. }
apply evt_done. unfold rrhead_post. exists (wz 0), t3v, t4v. rewrite GW, HP. reflexivity. }

assert (K44 : forall t2v t3v t4v,
evt segs (rrhead_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m0 G B sc mword stride idx E rsv)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) t2v s0 gw
a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 (RDEBRUIJN + 32)) (Z_to_bv 64 stride) (wz b3)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
F (Z_to_bv 64 (base + 0x178)) fc None m0 (seg_rom segs))).
{ intros t2v t3v t4v.

st1. st1. st1. st1. st1. st1. st1.
replace (B + stride * idx + 16 + stride + -4) with E by (subst E; lia).
replace (B + stride * idx + 16 + stride) with (E + 4) by (subst E; lia).
replace (B + stride * idx + 16) with (E + 4 - stride) by (subst E; lia).
fold rsv0.

st1. if_cases Kr; zify_cond Kr; rewrite ?wz_unsigned in Kr by lia.
-
replace rsv0 with rsv by (unfold rsv; replace (160 <=? b3) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
apply K0c.
- destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
pose proof (bytes_at_read segs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; lia)) as RD4.
rewrite Z.add_0_r in RD4. change (firstn _ _) with (le4 (wz r32)) in RD4.
pose proof (bytes_at_read segs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.

st1. st1. if_cases K8; zify_cond K8. 2:{ exfalso. rewrite ?unsigned_lit in K8 by lia. lia. }

replace (Z_to_bv 64 (E + 4)) with (Z_to_bv 64 (E - 4 + 8)) by (f_equal; lia).
st1. rewrite ?zx32_wz by lia. st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }

replace (Z_to_bv 64 (E - 4 + 8)) with (Z_to_bv 64 (E - 5 + 9)) by (f_equal; lia).
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. apply K10. reflexivity. }
replace (Z_to_bv 64 (E - 5 + 9)) with (Z_to_bv 64 (E + 4)) by (f_equal; lia).
replace (wz r32) with (Z_to_bv 64 rsv) by (unfold rsv; replace (160 <=? b3) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
apply K0c. }

assert (K9c : forall t3v t4v,
evt segs (rrhead_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m0 G B sc mword stride idx E rsv)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 gw
a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword) (Z_to_bv 64 (RDEBRUIJN + 32)) (wz off16) (wz b3)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
F (Z_to_bv 64 (base + 0x150)) fc None m0 (seg_rom segs))).
{ intros t3v t4v.

st1. rewrite MW12. st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
-
specialize (SC48 ltac:(left; gw_exact Km)). specialize (RS SC48).
st1. replace ((RDEBRUIJN + 32) + sc * 2) with ((RDEBRUIJN + 32) + 2 * sc) by (gw_expose_fam RDEBRUIJN; lia).
change (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * sc)) with (wa ((RDEBRUIJN + 32) + 2 * sc)).
pose proof (size_class_range sc ltac:(lia)) as SZ.
st1. st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (size_class sc * 16) with stride by (unfold stride; rewrite (proj2 (Z.eqb_eq _ _) Km); cbn [orb]; lia).
apply K44.
-
st1. st1. st1. if_cases Ko; zify_cond Ko.
2:{ exfalso. specialize (Hml Km). rewrite Z.shiftl_mul_pow2 in Ko by lia. change (2^8) with 256 in Ko. change 18446744073709551615 with (Z.ones 64) in Ko.
rewrite Z.land_ones, ?wz_unsigned, ?unsigned_lit in Ko by lia. rewrite Z.mod_small in Ko by lia. lia. }

st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
+
st1. st1. rewrite land_pgmask by lia. rewrite ?(wz_unsigned mword), MWP by lia. st1. st1.
replace (4096 * maplen + -16) with stride.
2:{ unfold stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia. }
apply K44.
+
specialize (SC48 ltac:(right; gw_exact Kl)). specialize (RS SC48).
st1. replace ((RDEBRUIJN + 32) + sc * 2) with ((RDEBRUIJN + 32) + 2 * sc) by (gw_expose_fam RDEBRUIJN; lia).
change (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * sc)) with (wa ((RDEBRUIJN + 32) + 2 * sc)).
pose proof (size_class_range sc ltac:(lia)) as SZ.
st1. st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (size_class sc * 16) with stride.
2:{ unfold stride. replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite orb_true_r. lia. }
apply K44. }

st1. if_cases K8; zify_cond K8.
-  specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
apply K9c.
- specialize (RS ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).

st1. replace ((RDEBRUIJN + 32) + sc * 2) with ((RDEBRUIJN + 32) + 2 * sc) by (gw_expose_fam RDEBRUIJN; lia).
change (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * sc)) with (wa ((RDEBRUIJN + 32) + 2 * sc)).
pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }

st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1. apply K9c.
Qed.

#[using="rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 hi_59 hi_67 lo_62 lo_70 CODE D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 ANCH_62 ANCH_70 RNG_RDEBRUIJN ROM_RSIZE_CLASSES land_pow2_testbit sllw1_word' zx32_wz rmremap_entry"] Lemma rr_head_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m0 : mem)
st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo8 + 256 * hi in
let idx := Z.land b3 31 in
let base_ := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
let stride := get_stride mr in
let E := conc st base_ + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m0 -> mem_inv segs m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base_ = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base_ ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
(m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at segs m0 (E - 4) (le4 (wz r32)) /\ bytes_at segs m0 (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at segs m0 (E - rsv) [b8 0] -> bytes_at segs m0 E [b8 0] ->
evt segs (rrhead_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m0 (conc st g) (conc st base_) (m_sizeclass mr) (meta_word mr) stride idx E rsv)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5c)) fc None m0 (seg_rom segs)).
Proof. clear - rvm_wait_entry w_15 w_59 w_62 w_67 w_70 w_145 w_147 w_185 w_238 hi_59 hi_67 lo_62 lo_70 CODE D_59 E_59 D_62 E_62 D_67 E_67 D_70 E_70 ANCH_62 ANCH_70 RNG_RDEBRUIJN ROM_RSIZE_CLASSES land_pow2_testbit sllw1_word' zx32_wz rmremap_entry segs base RDEBRUIJN. gw_expose_fam RDEBRUIJN.
intros until r32. cbv zeta. intros MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0.
set (po := snd p) in *. set (off16 := lo8 + 256 * hi) in *. set (idx := Z.land b3 31) in *.
set (base_ := aadd p (- (UNIT * off16) - UNIT)) in *. set (mr := get_meta_rec st g) in *.
set (strideW := if (m_maplen mr =? 0) || negb (m_last_idx mr =? 0) then 16 * size_class (m_sizeclass mr) else m_maplen mr * 4096 - 16).
assert (STR : get_stride mr = strideW).
{ unfold strideW, get_stride, UNIT. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn; lia. }
rewrite STR in *.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). unfold alloc_ceiling in BC.

destruct (rmrep_shadow_read st m0 (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
destruct (rmrep_shadow_read st m0 (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
destruct (rmrep_shadow_read2 st m0 (fst p) r (po - 2) lo8 hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; gw_exact C1)) as (R2 & LO & HI).
rewrite <- le2_lohi in R2 by lia.

destruct (rmrep_group_read st m0 base_ gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.

pose proof (rmrep_meta_chunk st m0 g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.

pose proof (rmrep_area_check_read st m0 (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
pose proof (rmrep_ctx_secret_read st m0 MR) as RC.

destruct (WG base_ gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base_ aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
assert (HB : conc st base_ = (r_base r + po) - 16 * off16 - 16).
{ unfold base_. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
destruct MS as (aa & ara & k & Ha & Hkk & Eg).
destruct (WA aa ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
assert (HG : conc st g = r_base rg + snd aa + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st aa rg Hrg). reflexivity. }
destruct (WR (fst aa) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). unfold alloc_ceiling in RBC.
assert (Hm : (r_base rg + snd aa + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
{ unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (r_base rg + snd aa + (24 + 40 * k)) with ((24 + 40 * k) + (snd aa / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
{ rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst aa) _ rg Hrg).
replace ((snd aa + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (snd aa + (24 + 40 * k)) with ((24 + 40 * k) + (snd aa / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
assert (MW : meta_word mr = m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) by first [reflexivity | (cbn; lia)].
rewrite MW. unfold UNIT, IB in *.
eapply (rr_head_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0
(r_base r + po) (conc st g) (conc st base_) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st)) r32
(pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
all: try (replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia; gw_exact R4).
all: try (replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia; gw_exact R3).
all: try (replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia; gw_exact R2).
all: try (intros Hlt; apply rsize_classes_read; [gw_exact MI | lia]).
all: try (pose proof (round_up_pg_ge (r_len r)); lia).
Qed.

End RC__1.

End G.
End Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QFkE QSfG QoCS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 QytA QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QLsg Qy5Y.Mq4 QlQE QFkE.
Import Qy8Z.Mq6.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Q7S0.Mq1 Ql2m.Mq3 QGeV QSfG.Mq2 QoCS.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
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

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq6.rarea_rep segs) (@rarea_rep) gw_tbl_0))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq6.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq6.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq6.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq6.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq6.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))))))).

Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rshadow_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rshadow_rep_ext) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rshadow_rep_ext)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rbytes_at_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rbytes_at_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rbytes_at_agree)).
Definition rwr_at_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rwr_at_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rwr_at_agree)).
Definition rrw_cells_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rrw_cells_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rrw_cells_agree)).
Definition ru64arr_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.ru64arr_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.ru64arr_agree)).
Definition ru8arr_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.ru8arr_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.ru8arr_agree)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition ptrs_in_but (rid : N) (g b : aptr) (st : mstate) : Prop :=
let P := fun x : N => x <> rid in
let c := ctx st in
optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
/\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
/\ (forall sc, optr_in P (active st sc))
/\ match c_brk c with BrkLive q _ => P q | _ => True end
/\ (forall g', optr_in P (m_prev (get_meta_rec st g')) /\ optr_in P (m_next (get_meta_rec st g'))
/\ (g' <> g -> optr_in P (m_mem (get_meta_rec st g'))))
/\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
/\ (forall b' gh, (s_groups st) !! b' = Some gh -> (b' <> b -> P (fst b')) /\ optr_in P (g_meta gh)).

#[using="Type"] Lemma bytes_at_pointwise m m' A A' bs :
bytes_at segs m A bs -> 0 <= A' -> A' + Z.of_nat (length bs) <= 2^64 ->
(forall i, 0 <= i < Z.of_nat (length bs) -> m' (wa (A' + i)) = m (wa (A + i))) ->
(forall i, 0 <= i < Z.of_nat (length bs) -> m (wa (A + i)) <> None) -> bytes_at segs m' A' bs.
Proof. clear - segs m m' A A' bs.
intros (H0 & H1 & H) A0 A1 E SM. split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite E by lia.
specialize (H i Hi). specialize (SM (Z.of_nat i) ltac:(lia)). unfold mrd in H.
destruct (m (wa (A + Z.of_nat i))); [gw_exact H| exfalso; apply SM; reflexivity].
Qed.

#[using="ref_wview_overlay ref_mrd_overlay"] Lemma rwr_at_of_bytes m A bs : bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= 0x10000 \/ RIMG_HI <= A) ->
wr_at segs m A (Z.of_nat (length bs)).
Proof. clear - ref_wview_overlay ref_mrd_overlay segs RIMG_HI m A bs. gw_expose_win.
intros (H0 & H1 & H) D. split; [lia|]. split; [lia|]. intros i Hi.
specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia.
rewrite ref_mrd_overlay in H by (rewrite wa_unsigned by lia; lia). rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia).
rewrite H. destruct (nth_error bs (Z.to_nat i)) eqn:E; [discriminate|]. apply nth_error_None in E. lia.
Qed.

#[using="Type"] Lemma bytes_at_agree m m' A bs : bytes_at segs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at segs m' A bs.
Proof. clear - segs m m' A bs. intros. eapply rbytes_at_agree; eauto. Qed.

Section REMAP.
Variables (st : mstate) (m m' : word -> option byte) (rid : N) (r : region) (g b : aptr) (ai : Z) (nb nd : Z).
Let ol := round_up_pg (r_len r).
Let mr := get_meta_rec st g.
Let st' := remap_region rid nb nd g st.
Let G := conc st g.
Let mr' := m_set_maplen (nd / 4096) mr.

Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Hb : (s_groups st) !! b = Some (mkGhdr (Some g) ai).
Hypothesis Fb : fst b = rid.
Hypothesis Sb : snd b = 0.
Hypothesis MSg : meta_slot st g.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis PT : ptrs_in_but rid g b st.
Hypothesis NB0 : 0 < nb.
Hypothesis NBA : nb mod 4096 = 0.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis ND16 : 16 <= nd.
Hypothesis NBC : nb + nd <= alloc_ceiling.

Hypothesis RFI : ranges_free ref_reserved nb nd = true.
Hypothesis RFX : forall q r', (s_regions st) !! q = Some r' -> q <> rid -> nb + nd <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb.

Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < nb \/ nb + nd <= a) -> (a < r_base r \/ r_base r + ol <= a) ->
(a < G + 16 \/ G + 24 <= a) -> (a < G + 32 \/ G + 40 <= a) -> m' (wa a) = m (wa a).
Hypothesis CP : forall o, 0 <= o < Z.min ol nd -> m' (wa (nb + o)) = m (wa (r_base r + o)).
Hypothesis ZF : forall o, ol <= o < nd -> m' (wa (nb + o)) = Some (b8 0).
Hypothesis MW1 : bytes_at segs m' (G + 16) (le8 (wz nb)).
Hypothesis MW2 : bytes_at segs m' (G + 32) (le8 (wz (meta_word mr'))).
Hypothesis MWo : forall a, G <= a < G + 16 \/ G + 24 <= a < G + 32 -> m' (wa a) = m (wa a).

Hypothesis SHX : forall o v, Z.min ol nd <= o < nd -> cell_read (get_shadow st' rid) o = Known v -> v = 0.
Hypothesis SHK : forall o v, 0 <= o < Z.min ol nd -> cell_read (get_shadow st' rid) o = Known v -> cell_read (get_shadow st rid) o = Known v.

#[using="r Hr"] Lemma rmr_regions : s_regions st' = <[rid := mkRegion RKGroup nb nd]> (s_regions st).
Proof. clear - r Hr st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
unfold st', remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity.
Qed.
#[using="r Hr"] Lemma rmr_lookup_new : (s_regions st') !! rid = Some (mkRegion RKGroup nb nd).
Proof. clear - r Hr st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. rewrite rmr_regions. apply lookup_insert_eq. Qed.
#[using="r Hr"] Lemma rmr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. clear - r Hr q st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. rewrite rmr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="r Hr"] Lemma rmr_lookup_inv q r' : (s_regions st') !! q = Some r' -> (q = rid /\ r' = mkRegion RKGroup nb nd) \/ (q <> rid /\ (s_regions st) !! q = Some r').
Proof. clear - r Hr q r' st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; try gw_hide rid; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
intros H. destruct (N.eq_dec q rid) as [->|NE].
- left. rewrite rmr_lookup_new in H. inversion H. auto.
- right. rewrite rmr_lookup_old in H by gw_exact NE. auto.
Qed.
#[using="r Hr"] Lemma rmr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. clear - r Hr q st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. unfold conc, get_region. rewrite rmr_lookup_old by assumption. reflexivity. Qed.
#[using="r Hr"] Lemma rmr_conc_new off : conc st' (rid, off) = nb + off.
Proof. clear - r Hr off st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold conc, get_region. cbn [fst snd]. rewrite rmr_lookup_new. reflexivity. Qed.
#[using="r Hr"] Lemma rmr_groups : s_groups st' = s_groups st.
Proof. clear - r Hr st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold st', remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="r Hr"] Lemma rmr_areas : s_areas st' = s_areas st.
Proof. clear - r Hr st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold st', remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="r Hr"] Lemma rmr_ctx : ctx st' = ctx st.
Proof. clear - r Hr st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold st', remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="r Hr"] Lemma rmr_reserved : s_reserved st' = s_reserved st.
Proof. clear - r Hr st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold st', remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="r Hr"] Lemma rmr_tick : s_tick st' = s_tick st.
Proof. clear - r Hr st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold st', remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="r Hr"] Lemma rmr_meta_other q : q <> g -> get_meta_rec st' q = get_meta_rec st q.
Proof. clear - r Hr q st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
intros NE. unfold st', remap_region. rewrite get_meta_rec_upd. rewrite (aptr_eqb_neq _ _) by congruence.
unfold upd_shadow, upd_region, get_region. rewrite Hr. reflexivity.
Qed.
#[using="r Hr"] Lemma rmr_meta_g : get_meta_rec st' g = mr'.
Proof. clear - r Hr st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide mr'; first [clear G | gw_hide G | idtac]; try gw_hide st'; try gw_hide mr; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
unfold st', remap_region. rewrite get_meta_rec_upd, aptr_eqb_refl. unfold mr', mr.
unfold upd_shadow, upd_region, get_region. rewrite Hr. reflexivity.
Qed.
#[using="r Hr"] Lemma rmr_shadow_other q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. clear - r Hr q st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
intros NE. unfold st', remap_region. rewrite get_shadow_upd_meta. unfold upd_shadow, upd_region, get_region, get_shadow. rewrite Hr.
cbn [s_shadow set_shadow set_regions]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="r Hr"] Lemma rmr_active sc : active st' sc = active st sc.
Proof. clear - r Hr sc st m m' rid g b ai nb nd ol mr st' G mr' MR Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold active. rewrite rmr_ctx. reflexivity. Qed.

Let WF := proj1 MR.

#[using="segs RATP RGOT_SSP st m rid MR Hr WF"] Lemma rmr_r_facts : 0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r /\ r_base r + ol <= alloc_ceiling /\ ranges_free ref_reserved (r_base r) ol = true.
Proof. clear - segs RATP RGOT_SSP st m rid MR Hr WF ref_reserved m' r g b ai nb nd ol mr st' G mr' Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; try gw_hide r; first [clear m' | gw_hide m' | idtac]. pose proof WF as (_ & WR & _). exact (WR rid r Hr). Qed.

#[using="segs RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved m r b nb nd ol MR Hr Kr Fb MSg NB0 ND16 WF"] Lemma rmr_g_facts : exists ra, (s_regions st) !! (fst g) = Some ra /\ fst g <> rid /\ G = r_base ra + snd g /\ 0 <= snd g /\ snd g + 40 <= round_up_pg (r_len ra)
/\ r_kind ra <> RKGroup /\ 0 < r_base ra /\ r_base ra + round_up_pg (r_len ra) <= alloc_ceiling /\ lr_lo ra <= G.
Proof. clear - segs RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved m r b nb nd ol MR Hr Kr Fb MSg NB0 ND16 WF st m' rid g ai mr st' G mr' Hb Sb Hmem PT NBA NDA NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear mr' | gw_hide mr' | idtac]; try gw_hide G; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; try gw_hide st.
pose proof WF as (_ & WR & _ & WA & _). destruct MSg as (a & ar & k & Ha & Hk & Eg).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & A0 & A1 & AL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LO.
assert (EG : G = conc st a + (AREA_HDR + META_SIZE * k)). { unfold G. rewrite Eg. rewrite conc_aadd by (rewrite Hra; eauto). reflexivity. }
exists ra. rewrite Eg. cbn [aadd fst snd]. split; [gw_exact Hra|]. split.
{ intros E. rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
split. { rewrite EG, Ca. lia. }
unfold AREA_HDR, META_SIZE, NSLOTS in *. repeat split; try lia; auto.
Qed.

#[using="segs RATP RGOT_SSP ref_reserved RC__ st m rid g b nb nd G MR Hr Fb NB0 ND16 WF"] Lemma rmr_ol_ge : r_len r <= ol /\ ol mod 4096 = 0 /\ 0 <= ol.
Proof. clear - segs RATP RGOT_SSP ref_reserved RC__ st m rid g b nb nd G MR Hr Fb NB0 ND16 WF m' r ai ol mr st' mr' Kr Hb Sb MSg Hmem PT NBA NDA NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; try gw_hide ol; first [clear ai | gw_hide ai | idtac]; try gw_hide r; first [clear m' | gw_hide m' | idtac]. unfold ol. pose proof (round_up_pg_ge (r_len r)). pose proof (round_up_pg_mod (r_len r)). pose proof rmr_r_facts. lia. Qed.

#[using="RC__ st rid r g b nb ol G Fb NDA"] Lemma rmr_nd_round : round_up_pg nd = nd.
Proof. clear - RC__ st rid r g b nb ol G Fb NDA m m' ai nd mr st' mr' MR Hr Kr Hb Sb MSg Hmem PT NB0 NBA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK WF. first [clear WF | gw_hide WF | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]. rewrite QLsg.round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Hypothesis ONLYB : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = rid -> b' = b.

#[using="segs RATP RGOT_SSP m r b ol G MR Hr Fb Sb PT NB0 NBA NDA ND16 NBC RFI RFX WF ONLYB"] Lemma rmr_regions_wf : rregions_wf st'.
Proof. clear - segs RATP RGOT_SSP m r b ol G MR Hr Fb Sb PT NB0 NBA NDA ND16 NBC RFI RFX WF ONLYB st m' rid g ai nb nd mr st' mr' Kr Hb MSg Hmem AG CP ZF MW1 MW2 MWo SHX SHK. first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear g | gw_hide g | idtac]; try gw_hide rid; first [clear m' | gw_hide m' | idtac]; first [clear st | gw_hide st | idtac].
pose proof MR as (WF0 & _). pose proof WF0 as (RS & WR & DJ & WA & WG).
pose proof rmr_r_facts as (RB0 & RBAL & RL0 & RBC & RRF). pose proof rmr_ol_ge as (OL1 & OL2 & OL3).
split; [rewrite rmr_reserved; gw_exact RS|]. split; [|split; [|split]].
- intros q r' Hq. destruct (rmr_lookup_inv q r' Hq) as [[-> ->]|[NE H]].
+ cbn [r_base r_len r_kind]. rewrite rmr_nd_round. repeat split; try lia. gw_exact RFI.
+ exact (WR q r' H).
- intros q1 r1 q2 r2 H1 H2 NE.
destruct (rmr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rmr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ cbn [r_base r_len]. rewrite rmr_nd_round. unfold lr_lo at 2. cbn [r_kind r_base]. pose proof (RFX q2 r2 H2' NE2). lia.
+ cbn [r_base r_len]. rewrite rmr_nd_round. unfold lr_lo at 1. cbn [r_kind r_base]. pose proof (RFX q1 r1 H1' NE1). lia.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. rewrite rmr_areas in Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists ra. rewrite rmr_lookup_old by gw_exact Pa. auto.
- intros b' gh Hb'. rewrite rmr_groups in Hb'. destruct (WG b' gh Hb') as (rb & Hrb & Kb & B0' & B16 & BM).
destruct (N.eq_dec (fst b') rid) as [E|NE].
+ pose proof (ONLYB b' gh Hb' E) as ->. eexists. rewrite Fb, rmr_lookup_new. split; [reflexivity|].
cbn [r_kind r_len]. rewrite rmr_nd_round, Sb. repeat split; try lia.
+ exists rb. rewrite rmr_lookup_old by gw_exact NE. auto 6.
Qed.

#[using="RC__ rid b Fb NB0 ND16 AG"] Lemma rmr_agree A n : 0 <= A -> A + n <= 2^64 ->
(A + n <= nb \/ nb + nd <= A) -> (A + n <= r_base r \/ r_base r + ol <= A) -> (A + n <= G + 16 \/ G + 40 <= A) ->
agree_on m m' A n.
Proof. clear - RC__ rid b Fb NB0 ND16 AG A n st m m' r g ai nb nd ol mr st' G mr' MR Hr Kr Hb Sb MSg Hmem PT NBA NDA NBC RFI RFX CP ZF MW1 MW2 MWo SHX SHK WF ONLYB. first [clear ONLYB | gw_hide ONLYB | idtac]; first [clear WF | gw_hide WF | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear g | gw_hide g | idtac]; first [clear r | gw_hide r | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros A0 An D1 D2 D3 a Ha. apply AG; lia. Qed.

#[using="segs RATP RGOT_SSP RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved RC__ st rid r g b nb nd ol G MR Hr Kr Fb MSg NB0 ND16 RFI AG WF"] Lemma rmr_agree_image A n : 0x10000 <= A -> A + n <= RIMG_HI -> agree_on m m' A n.
Proof. clear - segs RATP RGOT_SSP RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved RC__ st rid r g b nb nd ol G MR Hr Kr Fb MSg NB0 ND16 RFI AG WF RIMG_HI A n m m' ai mr st' mr' Hb Sb Hmem PT NBA NDA NBC RFX CP ZF MW1 MW2 MWo SHX SHK ONLYB. gw_expose_win. first [clear ONLYB | gw_hide ONLYB | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac].
intros A0 An a Ha. pose proof rmr_r_facts as (RB0 & RBAL & RL0 & RBC & RRF). pose proof rmr_ol_ge as (OL1 & OL2 & OL3).
destruct rmr_g_facts as (ra & Hra & NRg & EG & G0 & G40 & NK & RA0 & RAC & GLO).
pose proof (proj1 (proj2 WF)) as WR. destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa).
pose proof (rreserved_disjoint1 _ _ RFI ltac:(lia)) as D1.
pose proof (rreserved_disjoint1 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len ra)); lia)) as D3.
unfold alloc_ceiling in *.
apply AG; try lia.
destruct (Z.eq_dec ol 0) as [Z0|Z0]; [lia|]. pose proof (rreserved_disjoint1 _ _ RRF ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma rmr_rw_cells_agree A cs : rw_cells segs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof. clear - segs A cs st m m' rid r g b ai nb nd ol mr st' G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK WF ONLYB. first [clear ONLYB | gw_hide ONLYB | idtac]; first [clear WF | gw_hide WF | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Fb | gw_hide Fb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear G | gw_hide G | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ol | gw_hide ol | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear b | gw_hide b | idtac]; first [clear g | gw_hide g | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. eapply rrw_cells_agree; eauto. Qed.

#[using="RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved RC__ m r b ol G MR Hr Kr Fb MSg PT NB0 ND16 RFI AG WF"] Lemma rmr_rep_ctx : rmrep_ctx st' m'.
Proof. clear - RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved RC__ m r b ol G MR Hr Kr Fb MSg PT NB0 ND16 RFI AG WF RATP st m' rid g ai nb nd mr st' mr' Hb Sb Hmem NBA NDA NBC RFX CP ZF MW1 MW2 MWo SHX SHK ONLYB. gw_expose_fam RATP. first [clear ONLYB | gw_hide ONLYB | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear mr' | gw_hide mr' | idtac]; try gw_hide st'; first [clear mr | gw_hide mr | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear g | gw_hide g | idtac]; try gw_hide rid; first [clear m' | gw_hide m' | idtac]; try gw_hide st.
pose proof MR as (_ & CX & _). destruct PT as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
assert (Hconc : forall q, fst q <> rid -> conc st' q = conc st q) by (intros; apply rmr_conc; assumption).
assert (PW : forall p, optr_in (fun x => x <> rid) p -> pw st' p = pw st p).
{ intros [q|] Hq; cbn in Hq; unfold pw, oconc; [rewrite Hconc by gw_exact Hq|]; reflexivity. }
assert (E1 : ctx_head_cells st' = ctx_head_cells st).
{ unfold ctx_head_cells. rewrite rmr_ctx. rewrite !PW by assumption. reflexivity. }
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros a. rewrite rmr_active. apply PW. apply (H6 (Z.of_nat a)). }
assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite rmr_ctx. reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite rmr_ctx. reflexivity. }
assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite rmr_ctx. reflexivity. }
assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
{ unfold ctx_tail_cells, brk_word. rewrite rmr_ctx. destruct (c_brk (ctx st)) as [| |q off]; try reflexivity.
rewrite (Hconc (q, off)) by gw_exact H7. reflexivity. }
unfold rmrep_ctx. rewrite E1, E2, E3, E4, E5, E6.
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6).
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (rmr_agree_image (RATP + 131968) 928 ltac:(gw_expose_fam RATP; lia) ltac:(gw_expose_fam RATP; lia)) as AGC.
gw_expose_fam RATP.
split; [|split; [|split; [|split; [|split]]]].
- eapply rrw_cells_agree; [gw_exact C1|]. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
- eapply ru64arr_agree; [gw_exact C2|]. rewrite L1. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
- eapply ru64arr_agree; [gw_exact C3|]. rewrite L2. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
- eapply ru8arr_agree; [gw_exact C4|]. rewrite L3. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
- eapply ru8arr_agree; [gw_exact C5|]. rewrite L4. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
- eapply rrw_cells_agree; [gw_exact C6|]. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved st m rid r g b nb nd ol G MR Hr Kr Fb MSg NB0 ND16 RFI AG WF"] Lemma rmr_rep_globals : rmrep_globals m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved st m rid r g b nb nd ol G MR Hr Kr Fb MSg NB0 ND16 RFI AG WF RATP RGOT_SSP m' ai mr st' mr' Hb Sb Hmem PT NBA NDA NBC RFX CP ZF MW1 MW2 MWo SHX SHK ONLYB. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. first [clear ONLYB | gw_hide ONLYB | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear m' | gw_hide m' | idtac].
pose proof MR as (_ & _ & GL & _). destruct GL as (G1 & G2 & G3 & G4 & G5).
(gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold rmrep_globals in *).
split; [|split; [|split; [|split]]].
- eapply rrw_cells_agree; [gw_exact G1|]. apply rmr_agree_image; cbn; lia.
- eapply rrw_cells_agree; [gw_exact G2|]. apply rmr_agree_image; cbn; lia.
- eapply rrw_cells_agree; [gw_exact G3|]. apply rmr_agree_image; cbn; lia.
- eapply rrw_cells_agree; [gw_exact G4|]. apply rmr_agree_image; cbn; lia.
- eapply rrw_cells_agree; [gw_exact G5|]. apply rmr_agree_image; cbn; lia.
Qed.

#[using="segs RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved m g b G MR Hr Kr Fb NB0 NBA NDA ND16 RFX WF"] Lemma rmr_area_facts a ar : (s_areas st) !! a = Some ar ->
exists ra, (s_regions st) !! (fst a) = Some ra /\ fst a <> rid /\ conc st a = r_base ra + snd a
/\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len ra) /\ snd a mod 4096 = 0 /\ 0 < r_base ra /\ r_base ra + round_up_pg (r_len ra) <= alloc_ceiling
/\ (conc st a + 4096 <= nb \/ nb + nd <= conc st a)
/\ (conc st a + 4096 <= r_base r \/ r_base r + ol <= conc st a).
Proof. clear - segs RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved m g b G MR Hr Kr Fb NB0 NBA NDA ND16 RFX WF a ar st m' rid r ai nb nd ol mr st' mr' Hb Sb MSg Hmem PT NBC RFI AG CP ZF MW1 MW2 MWo SHX SHK ONLYB. first [clear ONLYB | gw_hide ONLYB | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; try gw_hide ol; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear ai | gw_hide ai | idtac]; try gw_hide r; try gw_hide rid; first [clear m' | gw_hide m' | idtac]; try gw_hide st.
intros Ha. pose proof WF as (RS & WR & DJ & WA & WG).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & A0 & A1 & AL & NK & RB0 & RBAL & RBC).
assert (NE : fst a <> rid). { intros E. rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LO.
exists ra. repeat (split; [first [gw_exact Hra| gw_exact NE| gw_exact Ca| gw_exact A0| gw_exact A1| gw_exact AL| gw_exact RB0| gw_exact RBC]|]).
split.
- pose proof (RFX _ _ Hra NE). lia.
- pose proof (lr_lo_group r Kr) as LR. unfold ol. destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
Qed.

#[using="segs RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved RC__ m rid r g b nb nd ol G MR Fb NB0 ND16 WF"] Lemma rmr_area_sep a ar a' ar' : (s_areas st) !! a = Some ar -> (s_areas st) !! a' = Some ar' -> a <> a' ->
conc st a + 4096 <= conc st a' \/ conc st a' + 4096 <= conc st a.
Proof. clear - segs RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved RC__ m rid r g b nb nd ol G MR Fb NB0 ND16 WF a ar a' ar' st m' ai mr st' mr' Hr Kr Hb Sb MSg Hmem PT NBA NDA NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK ONLYB. first [clear ONLYB | gw_hide ONLYB | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear MSg | gw_hide MSg | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear m' | gw_hide m' | idtac]; try gw_hide st.
intros Ha Ha' NE. pose proof WF as (RS & WR & DJ & WA & WG).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & A0 & A1 & AL & NK & RB0 & RBAL & RBC).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & A0' & A1' & AL' & NK' & RB0' & RBAL' & RBC').
rewrite Ca, Ca'.
destruct (N.eq_dec (fst a) (fst a')) as [E|NEr].
- rewrite <- E in Hra'. assert (ra' = ra) by congruence. subst ra'.
assert (snd a <> snd a') by (intros E2; apply NE; apply injective_projections; assumption).
Z.div_mod_to_equations. nia.
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ _ _ _ _ Hra Hra' NEr); lia.
Qed.

#[using="segs RATP RGOT_SSP ref_reserved RC__ m rid r b nb nd ol MR Fb MSg WF"] Lemma rmr_g_area : exists a0 ar0 k0, (s_areas st) !! a0 = Some ar0 /\ 0 <= k0 < NSLOTS /\ g = aadd a0 (AREA_HDR + META_SIZE * k0)
/\ G = conc st a0 + AREA_HDR + META_SIZE * k0.
Proof. clear - segs RATP RGOT_SSP ref_reserved RC__ m rid r b nb nd ol MR Fb MSg WF st m' g ai mr st' G mr' Hr Kr Hb Sb Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK ONLYB. first [clear ONLYB | gw_hide ONLYB | idtac]; first [clear SHK | gw_hide SHK | idtac]; first [clear SHX | gw_hide SHX | idtac]; first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RFX | gw_hide RFX | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; first [clear ND16 | gw_hide ND16 | idtac]; first [clear NDA | gw_hide NDA | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear NB0 | gw_hide NB0 | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear Kr | gw_hide Kr | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear mr' | gw_hide mr' | idtac]; try gw_hide G; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; first [clear ai | gw_hide ai | idtac]; first [clear g | gw_hide g | idtac]; first [clear m' | gw_hide m' | idtac]; try gw_hide st.
destruct MSg as (a0 & ar0 & k0 & Ha & Hk & Eg). exists a0, ar0, k0. split; [gw_exact Ha|]. split; [gw_exact Hk|]. split; [gw_exact Eg|].
destruct (rarea_conc st a0 ar0 WF Ha) as (ra & Hra & Ca & _).
unfold G. rewrite Eg. rewrite conc_aadd by (rewrite Hra; eauto). lia.
Qed.

#[using="RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_mrd_overlay RC__ m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 RFX AG MW1 MW2 MWo SHX SHK WF ONLYB"] Lemma rmr_rep_areas : rmrep_areas st' m'.
Proof. clear - RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_mrd_overlay RC__ m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 RFX AG MW1 MW2 MWo SHX SHK WF ONLYB segs st m' rid g nb nd st' NBC RFI CP ZF. gw_expose_win. first [clear ZF | gw_hide ZF | idtac]; first [clear CP | gw_hide CP | idtac]; first [clear RFI | gw_hide RFI | idtac]; first [clear NBC | gw_hide NBC | idtac]; try gw_hide st'; first [clear nd | gw_hide nd | idtac]; try gw_hide nb; try gw_hide g; try gw_hide rid; try gw_hide m'; try gw_hide st.
pose proof MR as (_ & _ & _ & AR & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct rmr_g_area as (a0 & ar0 & k0 & Ha0 & Hk0 & Eg & EG).
destruct (rmr_area_facts a0 ar0 Ha0) as (ra0 & Hra0 & NE0 & Ca0 & A00 & A01 & AL0 & RB00 & RBC0 & DN0 & DO0).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & P8 & P9 & _).
assert (PW : forall p, optr_in (fun x => x <> rid) p -> pw st' p = pw st p).
{ intros [q|] Hq; cbn in Hq; unfold pw, oconc; [rewrite rmr_conc by gw_exact Hq|]; reflexivity. }
intros a ar Ha. rewrite rmr_areas in Ha. destruct (AR a ar Ha) as (X1 & X2 & X3).
destruct (rmr_area_facts a ar Ha) as (ra & Hra & NEa & Ca & Aa0 & Aa1 & ALa & RBa & RBCa & DNa & DOa).
destruct (P9 a ar Ha) as [_ Pn]. unfold alloc_ceiling in *.

assert (GW : a <> a0 -> conc st a + 4096 <= G + 16 \/ G + 40 <= conc st a).
{ intros NE. destruct (rmr_area_sep a ar a0 ar0 Ha Ha0 NE); unfold AREA_HDR, META_SIZE, NSLOTS in *; lia. }
unfold rarea_rep. rewrite (rmr_conc a) by gw_exact NEa. rewrite (PW _ Pn).
split; [|split].
- eapply rrw_cells_agree; [gw_exact X1|]. cbn [cells_size csize Nat.add].
apply rmr_agree; try lia. destruct (aptr_eq_dec a a0) as [->|NE]; [|pose proof (GW NE); lia].
rewrite EG. unfold AREA_HDR, META_SIZE. lia.
- intros k Hk. set (q := aadd a (AREA_HDR + META_SIZE * k)).
assert (Cq : conc st q = conc st a + AREA_HDR + META_SIZE * k) by (unfold q; rewrite conc_aadd by (rewrite Hra; eauto); lia).
destruct (aptr_eq_dec q g) as [Eq|NEq].
+
rewrite Eq, rmr_meta_g.
assert (Ea : a = a0 /\ k = k0).
{ destruct (aptr_eq_dec a a0) as [->|NE].
- split; [reflexivity|]. unfold q in Eq. rewrite Eg in Eq. apply (f_equal snd) in Eq. cbn in Eq. unfold META_SIZE in Eq. lia.
- exfalso. pose proof (GW NE). assert (EqG : conc st q = G) by (rewrite Eq; reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
destruct Ea as [-> ->].
pose proof (X2 k0 Hk0) as Xg. fold q in Xg. rewrite Eq in Xg. change (get_meta_rec st g) with mr in Xg.
replace (conc st a0 + AREA_HDR + META_SIZE * k0) with G by lia.

unfold meta_cells. unfold mr'. cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen].
fold mr. rewrite Hmem. destruct (P8 g) as (Pp & Pq & _). rewrite (PW _ Pp), (PW _ Pq).
assert (Eb : pw st' (Some b) = wz nb).
{ unfold pw, oconc. replace b with (rid, 0) by (destruct b; cbn in Fb, Sb; subst; reflexivity). rewrite rmr_conc_new, Z.add_0_r. reflexivity. }
rewrite Eb.
replace (conc st a0 + AREA_HDR + META_SIZE * k0) with G in Xg by lia.
pose proof (rw_cells_bytes_at _ _ _ _ Xg) as XB. unfold meta_cells in XB. rewrite Hmem in XB. cbn [cells_bytes cbytes app] in XB. rewrite ?app_nil_r in XB.
destruct rmr_g_facts as (rg & Hrg & NRg & EGr & Gs0 & Gs40 & NKg & RG0 & RGC & GLO).
pose proof (proj1 (proj2 WF) _ _ Hrg) as (_ & _ & _ & _ & RFg).
pose proof (rreserved_disjoint1 _ _ RFg ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)) as DIg.
assert (GI : G + 40 <= 0x10000 \/ RIMG_HI <= G) by lia.

assert (B' : bytes_at segs m' G (le8 (pw st (m_prev mr)) ++ le8 (pw st (m_next mr)) ++ le8 (wz nb) ++ le4 (wz (m_avail mr)) ++ le4 (wz (m_freed mr)) ++ le8 (wz (meta_word mr')))).
{ apply bytes_at_app in XB as [B1 XB]. rewrite length_le8 in XB. apply bytes_at_app in XB as [B2 XB]. rewrite length_le8 in XB.
apply bytes_at_app in XB as [_ XB]. rewrite length_le8 in XB. apply bytes_at_app in XB as [B4 XB]. rewrite length_le4 in XB.
apply bytes_at_app in XB as [B5 _]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in B2, B4, B5.
replace (G + 8 + 8 + 8) with (G + 24) in B4 by lia. replace (G + 8 + 8 + 8 + 4) with (G + 28) in B5 by lia.
apply bytes_at_app. split. { eapply bytes_at_agree; [gw_exact B1|]. rewrite length_le8. intros x Hx. apply MWo. lia. }
rewrite length_le8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. apply bytes_at_app. split. { eapply bytes_at_agree; [gw_exact B2|]. rewrite length_le8. intros x Hx. apply MWo. lia. }
rewrite length_le8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. apply bytes_at_app. split. { replace (G + 8 + 8) with (G + 16) by lia. gw_exact MW1. }
rewrite length_le8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. apply bytes_at_app. split. { replace (G + 8 + 8 + 8) with (G + 24) by lia. eapply bytes_at_agree; [gw_exact B4|]. rewrite length_le4. intros x Hx. apply MWo. lia. }
rewrite length_le4. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. apply bytes_at_app. split. { replace (G + 8 + 8 + 8 + 4) with (G + 28) by lia. eapply bytes_at_agree; [gw_exact B5|]. rewrite length_le4. intros x Hx. apply MWo. lia. }
rewrite length_le4. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. replace (G + 8 + 8 + 8 + 4 + 4) with (G + 32) by lia. gw_exact MW2. }
apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; gw_exact B'|].
cbn [cells_size csize Nat.add]. pose proof (rwr_at_of_bytes _ _ _ B' ltac:(rewrite !app_length, !length_le8, !length_le4; cbn; lia)) as W'.
rewrite !app_length, !length_le8, !length_le4 in W'. gw_exact W'.
+
rewrite (rmr_meta_other q NEq).
assert (EC : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q)).
{ destruct (P8 q) as (Pp & Pn' & Pm). unfold meta_cells. rewrite (PW _ Pp), (PW _ Pn'), (PW _ (Pm NEq)). reflexivity. }
rewrite EC. eapply rrw_cells_agree; [exact (X2 k Hk)|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
rewrite <- Cq. apply rmr_agree; try (unfold AREA_HDR, META_SIZE, NSLOTS in *; lia).

destruct (aptr_eq_dec a a0) as [->|NE].
* assert (k <> k0) by (intros ->; apply NEq; unfold q; rewrite Eg; reflexivity). rewrite Cq, EG. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
* pose proof (GW NE). unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
- eapply rrw_cells_agree; [gw_exact X3|]. cbn [cells_size csize Nat.add].
apply rmr_agree; try lia. destruct (aptr_eq_dec a a0) as [->|NE]; [|pose proof (GW NE); lia].
rewrite EG. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
Qed.

#[using="RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_mrd_overlay RC__ m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP MW1 MW2 MWo SHX SHK WF ONLYB"] Lemma rmr_rep_groups : rmrep_groups st' m'.
Proof. clear - RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_mrd_overlay RC__ m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP MW1 MW2 MWo SHX SHK WF ONLYB segs st m' rid g nb nd st' ZF. first [clear ZF | gw_hide ZF | idtac]; try gw_hide st'; first [clear nd | gw_hide nd | idtac]; try gw_hide nb; try gw_hide g; try gw_hide rid; try gw_hide m'; try gw_hide st.
pose proof MR as (_ & _ & _ & _ & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof rmr_r_facts as (RB0 & RBAL & RL0 & RBC & RRF). pose proof rmr_ol_ge as (OL1 & OL2 & OL3).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10).
destruct rmr_g_area as (a0 & ar0 & k0 & Ha0 & Hk0 & Eg & EG).
destruct (rmr_area_facts a0 ar0 Ha0) as (ra0 & Hra0 & NE0 & Ca0 & A00 & A01 & AL0 & RB00 & RBC0 & DN0 & DO0).
destruct rmr_g_facts as (rg & Hrg & NRg & EGr & Gs0 & Gs40 & NKg & RG0 & RGC & GLO).
assert (PW : forall p, optr_in (fun x => x <> rid) p -> pw st' p = pw st p).
{ intros [q|] Hq; cbn in Hq; unfold pw, oconc; [rewrite rmr_conc by gw_exact Hq|]; reflexivity. }
unfold alloc_ceiling in *.
intros b' gh Hb'. rewrite rmr_groups in Hb'. destruct (GR b' gh Hb') as (w8 & R & Hw8). destruct (P10 b' gh Hb') as [Pb Pg].
destruct (aptr_eq_dec b' b) as [->|NE].
-
rewrite Hb in Hb'. inversion Hb'; subst gh. cbn [g_meta] in R |- *.
exists w8. split; [|gw_exact Hw8].
assert (Cb' : conc st' b = nb). { replace b with (rid, 0) by (destruct b; cbn in Fb, Sb; subst; reflexivity). rewrite rmr_conc_new. lia. }
assert (Cb : conc st b = r_base r). { rewrite (conc_region' st b r) by (rewrite Fb; gw_exact Hr). lia. }
rewrite Cb'. rewrite Cb in R. rewrite (PW (Some g)) by gw_exact Pg.
destruct (WG b _ Hb) as (rb & Hrb & _ & _ & B16 & _). rewrite Fb, Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite Sb in B16.
pose proof (rw_cells_bytes_at _ _ _ _ R) as BB. cbn [cells_bytes cbytes] in BB. rewrite ?app_nil_r in BB.
pose proof (rw_cells_wr_at _ _ _ _ 9 R ltac:(cbn; lia)) as (_ & _ & WB).
pose proof (rreserved_disjoint1 _ _ RRF ltac:(lia)) as DIr. pose proof (rreserved_disjoint1 _ _ RFI ltac:(lia)) as DIn.
assert (B' : bytes_at segs m' nb (le8 (pw st (Some g)) ++ [w8])).
{ eapply (bytes_at_pointwise m m' (r_base r) nb); [gw_exact BB| lia| rewrite app_length, length_le8; cbn; lia| |].
- rewrite app_length, length_le8. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add]. intros i Hi. apply CP. lia.
- rewrite app_length, length_le8. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add]. intros i Hi E.
specialize (WB i ltac:(lia)). rewrite ref_wview_overlay in WB by (rewrite wa_unsigned by lia; lia). exact (WB E). }
apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| cbn [cells_bytes cbytes app]; cbn [app] in B'; gw_exact B'|].
cbn [cells_size csize Nat.add]. pose proof (rwr_at_of_bytes _ _ _ B' ltac:(rewrite app_length, length_le8; cbn; lia)) as W'.
rewrite app_length, length_le8 in W'. gw_exact W'.
-
specialize (Pb NE). exists w8. split; [|gw_exact Hw8]. rewrite (rmr_conc b') by gw_exact Pb. rewrite (PW _ Pg).
eapply rrw_cells_agree; [gw_exact R|]. cbn [cells_size csize Nat.add].
destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RBb0 & RBbC). rewrite Cb. unfold alloc_ceiling in RBbC.
pose proof (RFX _ _ Hrb Pb) as X1. rewrite (lr_lo_group rb Kb) in X1.
assert (X2 : r_base rb + round_up_pg (r_len rb) <= r_base r \/ r_base r + ol <= r_base rb).
{ pose proof (lr_lo_group r Kr). pose proof (lr_lo_group rb Kb). unfold ol. destruct (DJ _ _ _ _ Hrb Hr Pb); lia. }
assert (X3 : r_base rb + round_up_pg (r_len rb) <= lr_lo rg \/ r_base rg + round_up_pg (r_len rg) <= r_base rb).
{ assert (NEg : fst b' <> fst g) by (intros E; rewrite E, Hrg in Hrb; assert (rb = rg) by congruence; subst; exact (NKg Kb)).
pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrg NEg); lia. }
pose proof (lr_lo_ge rg). apply rmr_agree; lia.
Qed.

#[using="RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved ref_wview_overlay RC__ m r b ol G MR Hr Kr Fb MSg PT NB0 NDA ND16 NBC RFI RFX AG CP ZF SHX SHK WF ONLYB"] Lemma rmr_rep_shadow : rmrep_shadow st' m'.
Proof. clear - RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved ref_wview_overlay RC__ m r b ol G MR Hr Kr Fb MSg PT NB0 NDA ND16 NBC RFI RFX AG CP ZF SHX SHK WF ONLYB st m' rid g ai nb nd mr st' mr' Hb Sb Hmem NBA MW1 MW2 MWo. first [clear MWo | gw_hide MWo | idtac]; first [clear MW2 | gw_hide MW2 | idtac]; first [clear MW1 | gw_hide MW1 | idtac]; first [clear NBA | gw_hide NBA | idtac]; first [clear Hmem | gw_hide Hmem | idtac]; first [clear Sb | gw_hide Sb | idtac]; first [clear Hb | gw_hide Hb | idtac]; first [clear mr' | gw_hide mr' | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear mr | gw_hide mr | idtac]; try gw_hide nd; try gw_hide nb; first [clear ai | gw_hide ai | idtac]; try gw_hide g; try gw_hide rid; try gw_hide m'; first [clear st | gw_hide st | idtac].
pose proof MR as (_ & _ & _ & _ & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof rmr_r_facts as (RB0 & RBAL & RL0 & RBC & RRF). pose proof rmr_ol_ge as (OL1 & OL2 & OL3).
destruct rmr_g_facts as (rg & Hrg & NRg & EGr & Gs0 & Gs40 & NKg & RG0 & RGC & GLO).
pose proof (rreserved_disjoint1 _ _ RFI ltac:(lia)) as DIn.
unfold alloc_ceiling in *.
intros q rq Hq Kq. destruct (rmr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
-
destruct (SH rid r Hr Kr) as [HW HB]. unfold rshadow_rep. cbn [r_base r_len]. rewrite rmr_nd_round.
assert (OLD : forall o, 0 <= o < ol -> m (wa (r_base r + o)) <> None).
{ intros o Ho. destruct HW as (_ & _ & W). specialize (W o Ho). rewrite ref_wview_overlay in W; [gw_exact W|].
rewrite wa_unsigned by lia. pose proof (rreserved_disjoint1 _ _ RRF ltac:(lia)). lia. }
split.
+ split; [lia|]. split; [lia|]. intros i Hi. rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia).
destruct (Z.lt_ge_cases i (Z.min ol nd)) as [LT|GE].
* rewrite CP by lia. apply OLD. lia.
* rewrite ZF by lia. discriminate.
+ intros o v Ho Hc. destruct (Z.lt_ge_cases o (Z.min ol nd)) as [LT|GE].
* pose proof (SHK o v ltac:(lia) Hc) as Hc0. destruct (HB o v ltac:(lia) Hc0) as [Bo Hv]. split; [|gw_exact Hv].
eapply (bytes_at_pointwise m m' (r_base r + o) (nb + o)); [gw_exact Bo| lia| cbn; lia| |]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; intros i Hi.
-- replace (nb + o + i) with (nb + (o + i)) by lia. replace (r_base r + o + i) with (r_base r + (o + i)) by lia. apply CP. lia.
-- replace (r_base r + o + i) with (r_base r + (o + i)) by lia. apply OLD. lia.
* pose proof (SHX o v ltac:(lia) Hc) as ->. split; [|lia].
split; [lia|]. split; [cbn; lia|]. cbn [length]. intros i Hi. destruct i; [|lia]. cbn [nth_error Z.of_nat].
unfold mrd. rewrite Z.add_0_r. rewrite ZF by lia. reflexivity.
-
eapply rshadow_rep_ext; [apply rmr_shadow_other; gw_exact NE|].
destruct (SH q rq H Kq) as [HW HB]. destruct (WR _ _ H) as (QB0 & _ & _ & QBC & _).
pose proof (RFX _ _ H NE) as X1. rewrite (lr_lo_group rq Kq) in X1.
assert (X2 : r_base rq + round_up_pg (r_len rq) <= r_base r \/ r_base r + ol <= r_base rq).
{ pose proof (lr_lo_group r Kr). pose proof (lr_lo_group rq Kq). unfold ol. destruct (DJ _ _ _ _ H Hr NE); lia. }
assert (X3 : r_base rq + round_up_pg (r_len rq) <= lr_lo rg \/ r_base rg + round_up_pg (r_len rg) <= r_base rq).
{ assert (NEg : q <> fst g) by (intros E; rewrite E, Hrg in H; assert (rq = rg) by congruence; subst; exact (NKg Kq)).
pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ H Hrg NEg); lia. }
pose proof (lr_lo_ge rg).
assert (AGq : agree_on m m' (r_base rq) (round_up_pg (r_len rq))) by (apply rmr_agree; lia).
split.
+ eapply rwr_at_agree; [gw_exact HW| gw_exact AGq].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
eapply rbytes_at_agree; [gw_exact Bt|]. cbn. eapply agree_on_sub; [gw_exact AGq| lia| lia].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_mrd_overlay m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK WF ONLYB"] Theorem rmrep_remap : rmrep st' m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_mrd_overlay m r b ai ol mr G mr' MR Hr Kr Hb Fb Sb MSg Hmem PT NB0 NBA NDA ND16 NBC RFI RFX AG CP ZF MW1 MW2 MWo SHX SHK WF ONLYB st m' rid g nb nd st'. first [clear st' | gw_hide st' | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear st | gw_hide st | idtac].
split; [gw_exact rmr_regions_wf|]. split; [gw_exact rmr_rep_ctx|]. split; [gw_exact rmr_rep_globals|].
split; [gw_exact rmr_rep_areas|]. split; [gw_exact rmr_rep_groups| gw_exact rmr_rep_shadow].
Qed.

End REMAP.

#[using="Type"] Lemma ranges_free_except_In old l a n b0 k : ranges_free_except old l a n = true -> In (b0, k) l -> b0 <> old -> a + n <= b0 \/ b0 + k <= a.
Proof. clear - old l a n b0 k.
intros H HI NE. unfold ranges_free_except in H. rewrite forallb_forall in H. specialize (H _ HI). cbn [fst snd] in H.
apply Bool.orb_prop in H as [H|H]; [apply Z.eqb_eq in H; lia|].
unfold iv_disjoint in H. apply Bool.orb_prop in H as [X|X]; apply Z.leb_le in X; lia.
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved"] Lemma rr_answer_cases (live : list (Z * Z)) (B ol nd : Z) (x : mremap_ans) :
let zz := match x with MrErr e => neg_errno e | MrInPlace => B | MrMoved a => a end in
mremap_answer_ok live B ol nd zz = true ->
match x with
| MrErr e => e = 12
| MrInPlace => True
| MrMoved a => (a mod 4096 = 0 /\ 0 < a /\ a + nd <= alloc_ceiling) /\ avoids a nd [] = true /\ a <> B mod 2^64
end ->
0 < B -> 0 < ol -> 0 < nd -> ol <> nd -> ol mod 4096 = 0 -> nd mod 4096 = 0 -> B + ol <= alloc_ceiling ->
(B + ol <= 0x10000 \/ RIMG_HI <= B) ->
In (B, ol) live -> (forall y, In y ref_reserved -> In y live) ->
match x with
| MrErr e => is_err zz = true
| MrInPlace => is_err zz = false /\ (nd < ol \/ (ol < nd /\ B + nd <= alloc_ceiling /\ (B + nd <= 0x10000 \/ RIMG_HI <= B + ol)
/\ forall b0 k, In (b0, k) live -> b0 <> B -> B + nd <= b0 \/ b0 + k <= B + ol))
| MrMoved a => is_err zz = false /\ ol < nd /\ (a + nd <= 0x10000 \/ RIMG_HI <= a) /\ (B + ol <= a \/ a + nd <= B)
/\ ranges_free live a nd = true
end.
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RIMG_HI ref_reserved live B ol nd x. gw_expose_win.
cbv zeta. intros OK DF B0 OL0 ND0 NE OLA NDA BC BI INr INimg.
unfold mremap_answer_ok in OK. rewrite (round_up_pg_id ol), (round_up_pg_id nd) in OK by assumption.
unfold is_errno_form, is_err, TWO64, alloc_ceiling, PGSZ in *.

assert (IMG : forall P : Z -> Z -> Prop, (forall b0 k, In (b0, k) live -> b0 <> B -> P b0 k) ->
match ref_reserved with
| [(a1, k1); (a2, k2); (a3, k3); (a4, k4)] => P a1 k1 /\ P a2 k2 /\ P a3 k3 /\ P a4 k4
| _ => True
end).
{ intros P HP. rewrite ?LAY_ref_reserved. repeat split; (apply HP; [apply INimg; rewrite ?LAY_ref_reserved; cbn; tauto| lia]). }
rewrite ?LAY_ref_reserved in IMG.
destruct x as [e| |na].
- apply Z.ltb_lt. unfold neg_errno. lia.
- split; [apply Z.ltb_ge; lia|].
apply Bool.orb_prop in OK as [OK|OK]; [apply Bool.orb_prop in OK as [OK|OK]|].
+ exfalso. apply andb_prop in OK as [X1 X2]. apply Z.leb_le in X1. lia.
+ apply andb_prop in OK as [_ OK]. apply Bool.orb_prop in OK as [OK|OK].
* left. apply Z.leb_le in OK. lia.
* apply andb_prop in OK as [X1 X2]. apply Z.leb_le in X1.
assert (HF : forall b0 k, In (b0, k) live -> b0 <> B -> B + nd <= b0 \/ b0 + k <= B + ol).
{ intros b0 k HI NEb. pose proof (ranges_free_except_In _ _ _ _ _ _ X2 HI NEb). lia. }
destruct (IMG _ HF) as (I1 & I2 & I3 & I4).
assert (ol < nd \/ nd <= ol) as [LT|LE] by lia; [| left; lia]. right. split; [gw_exact LT|]. split; [lia|]. split; [lia| gw_exact HF].
+ exfalso. apply andb_prop in OK as [OK _]. apply andb_prop in OK as [OK _]. apply andb_prop in OK as [OK _]. apply andb_prop in OK as [OK _].
apply andb_prop in OK as [OK _]. rewrite Z.eqb_refl in OK. discriminate.
- destruct DF as ((NA & N0 & NC) & _ & NNE).
assert (NEB : na <> B) by (rewrite Z.mod_small in NNE by lia; gw_exact NNE).
split; [apply Z.ltb_ge; lia|].
apply Bool.orb_prop in OK as [OK|OK]; [apply Bool.orb_prop in OK as [OK|OK]|].
+ exfalso. apply andb_prop in OK as [X1 X2]. apply Z.leb_le in X1. lia.
+ exfalso. apply andb_prop in OK as [OK _]. apply Z.eqb_eq in OK. lia.
+ apply andb_prop in OK as [OK RFR]. apply andb_prop in OK as [OK _]. apply andb_prop in OK as [OK _]. apply andb_prop in OK as [OK _].
apply andb_prop in OK as [_ LT]. apply Z.ltb_lt in LT.
pose proof (ranges_free_In _ _ _ _ _ RFR INr) as DJ.
assert (HF : forall b0 k, In (b0, k) live -> b0 <> B -> na + nd <= b0 \/ b0 + k <= na).
{ intros b0 k HI _. exact (ranges_free_In _ _ _ _ _ RFR HI). }
destruct (IMG _ HF) as (I1 & I2 & I3 & I4).
split; [gw_exact LT|]. split; [lia|]. split; [lia| gw_exact RFR].
Qed.

#[using="Type"] Lemma rptrs_in_but st LB m rid r g b gai :
CINV st LB -> rmrep st m ->
(s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
(s_groups st) !! b = Some (mkGhdr (Some g) gai) -> fst b = rid ->
(forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = rid -> b' = b) ->
ptrs_in_but rid g b st.
Proof. clear - st LB m rid r g b gai.
intros C MR Hr Kr Hb Fb ONLYB. pose proof (KINV_of_CINV _ _ C) as K. pose proof (ci_mp _ _ C) as (M1 & M2 & M3 & M4 & M5).
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (MSr : forall q, meta_slot st q -> fst q <> rid).
{ intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
assert (NGr : forall p, ng_ptr st p -> optr_in (fun x => x <> rid) p).
{ intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
assert (OM : forall p, (forall q, p = Some q -> meta_slot st q) -> optr_in (fun x => x <> rid) p).
{ intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
unfold ptrs_in_but. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
- apply OM. intros h Hh. exact (proj1 (kinv_free_head st LB _ h K Hh)).
- apply NGr. gw_exact M1.
- apply NGr. gw_exact M2.
- apply NGr. gw_exact M3.
- apply NGr. gw_exact M4.
- intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st LB _ sc a K Ha))).
- destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB; try exact I.
intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
- intros g'. split; [| split].
+ apply OM. intros pv Hp. exact (proj2 (LP g' pv Hp)).
+ apply OM. intros nx Hn. exact (proj2 (LN g' nx Hn)).
+ intros NE. destruct (m_mem (get_meta_rec st g')) as [q|] eqn:MB; cbn; [| exact I].
intros E. destruct (ZINV_of_CINV _ _ C g' q MB) as [[ai' Hq]|[]].
pose proof (ONLYB q _ Hq E) as ->. rewrite Hb in Hq. inversion Hq. subst. exact (NE eq_refl).
- intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
- intros b' gh Hb'. split.
+ intros NE E. exact (NE (ONLYB b' gh Hb' E)).
+ destruct (ki_grps _ _ _ K b' gh Hb') as (g' & Hg & _). rewrite Hg. cbn. apply MSr.
assert (HBh : hosts st b' g') by (exists (g_active_idx gh); rewrite Hb'; destruct gh; cbn in Hg |- *; subst; reflexivity).
exact (go_slot _ _ _ (ki_gmetas _ _ _ K b' g' HBh)).
Qed.

#[using="segs RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved"] Lemma ticks_ok_remap_region rid nb nd g st : ticks_ok st -> ticks_ok (remap_region rid nb nd g st).
Proof. clear - segs RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ROM_reservedZ LAY_ref_reserved rid nb nd g st.
intros [T1 T2].
assert (GEN : forall sh q, (s_shadow (remap_region rid nb nd g st)) !! q = Some sh ->
exists sh0, (forall u hl, r_hav sh !! u = Some hl -> r_hav sh0 !! u = Some hl)
/\ (forall pg t, r_havp sh !! pg = Some t -> r_havp sh0 !! pg = Some t)
/\ ((s_shadow st) !! q = Some sh0 \/ sh0 = shadow0)).
{ intros sh q Hq. unfold remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region in Hq.
assert (Hq' : (<[rid := shadow_truncate (remap_bound st rid nd) (get_shadow st rid)]> (s_shadow st)) !! q = Some sh).
{ destruct (s_regions st !! rid); gw_exact Hq. }
clear Hq. destruct (N.eq_dec q rid) as [->|NE].
- rewrite lookup_insert_eq in Hq'. inversion Hq'; subst sh. exists (get_shadow st rid). split; [|split].
+ cbn [shadow_truncate r_hav]. intros u hl H. rewrite map_lookup_filter in H. destruct (r_hav (get_shadow st rid) !! u); [|discriminate]. cbn in H. case_decide; [inversion H; subst; reflexivity| discriminate].
+ cbn [shadow_truncate r_havp]. intros pg t H. rewrite map_lookup_filter in H. destruct (r_havp (get_shadow st rid) !! pg); [|discriminate]. cbn in H. case_decide; [inversion H; subst; reflexivity| discriminate].
+ unfold get_shadow. destruct (s_shadow st !! rid) as [sh0|] eqn:E; cbn; [left; reflexivity| right; reflexivity].
- rewrite lookup_insert_ne in Hq' by congruence. exists sh. split; [auto|]. split; [auto| left; gw_exact Hq']. }
assert (TK' : s_tick (remap_region rid nb nd g st) = s_tick st).
{ unfold remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. destruct (s_regions st !! rid); reflexivity. }
split; intros q sh; [intros u hl ch Hq Hu Hin| intros pg t Hq Hpg]; rewrite TK'.
- destruct (GEN sh q Hq) as (sh0 & X1 & X2 & [X3|X3]).
+ eapply T1; [gw_exact X3| apply X1; gw_exact Hu| gw_exact Hin].
+ subst sh0. specialize (X1 _ _ Hu). cbn in X1. rewrite lookup_empty in X1. discriminate.
- destruct (GEN sh q Hq) as (sh0 & X1 & X2 & [X3|X3]).
+ eapply T2; [gw_exact X3| apply X2; gw_exact Hpg].
+ subst sh0. specialize (X2 _ _ Hpg). cbn in X2. rewrite lookup_empty in X2. discriminate.
Qed.

#[using="Type"] Lemma strip_remap_fin p n e k rid nb nd g t st :
strip (havoc p n (set_size p e n k (wr8 e 0 (remap_region rid nb nd g (set_tick t st))))) = strip (remap_region rid nb nd g (strip st)).
Proof. clear - p n e k rid nb nd g t st.
rewrite strip_havoc. unfold set_size.
assert (SW : forall q v stx, strip (wr8 q v stx) = strip stx) by (intros; reflexivity).
assert (SW32 : forall q v stx, strip (wr32 q v stx) = strip stx) by (intros; unfold wr32; rewrite !SW; reflexivity).
destruct (5 <=? e.2 - p.2 - n); destruct (negb (e.2 - p.2 - n =? 0)); rewrite ?SW, ?SW32, ?SW.
all: unfold remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region, remap_bound, get_region; cbn [s_regions strip set_tick];
destruct (s_regions st !! rid); reflexivity.
Qed.

#[using="Type"] Lemma get_stride_remap mr nd : m_last_idx mr = 0 -> nd mod 4096 = 0 -> 0 < nd < 2^60 -> get_stride (m_set_maplen (nd / 4096) mr) = nd - 16.
Proof. clear - mr nd.
intros LI NDA ND. unfold get_stride, m_set_maplen. cbn [m_last_idx m_maplen m_sizeclass]. rewrite LI. cbn [Z.eqb].
change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
replace (nd / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia). cbn. unfold UNIT. Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma ctx_havoc' p n st : ctx (havoc p n st) = ctx st.
Proof. clear - p n st. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma ctx_set_size' p e n b st : ctx (set_size p e n b st) = ctx st.
Proof. clear - p e n b st. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.

#[using="Type"] Lemma write_other m a bs x : 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x) -> write_to_mem m (wa a) bs x = m x.
Proof. clear - m a bs x.
intros Ha Hl Hx. rewrite write_to_mem_spec by assumption.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. lia.
Qed.

Section FIN.
Variables (st : mstate) (rid : N) (r : region) (g : aptr) (nb nd : Z) (p e : aptr) (n k : Z).
Hypothesis Hr : (s_regions st) !! rid = Some r.
Let stR := remap_region rid nb nd g st.
Let stW := wr8 e 0 stR.
Let stF := havoc p n (set_size p e n k stW).

#[using="r Hr"] Lemma fin_regions_R : s_regions stR = <[rid := mkRegion RKGroup nb nd]> (s_regions st).
Proof. clear - r Hr st rid g nb nd p e n k stR stW stF. first [clear stF | gw_hide stF | idtac]; first [clear stW | gw_hide stW | idtac]; try gw_hide stR; first [clear k | gw_hide k | idtac]; first [clear n | gw_hide n | idtac]; first [clear e | gw_hide e | idtac]; first [clear p | gw_hide p | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. unfold stR, remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="Type"] Lemma fin_regions_W : s_regions stW = s_regions stR.
Proof. clear - st rid r g nb nd p e n k Hr stR stW stF. first [clear stF | gw_hide stF | idtac]; first [clear stW | gw_hide stW | idtac]; first [clear stR | gw_hide stR | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear k | gw_hide k | idtac]; first [clear n | gw_hide n | idtac]; first [clear e | gw_hide e | idtac]; first [clear p | gw_hide p | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear g | gw_hide g | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. reflexivity. Qed.
#[using="r Hr"] Lemma fin_lookup_W : (s_regions stW) !! rid = Some (mkRegion RKGroup nb nd).
Proof. clear - r Hr st rid g nb nd p e n k stR stW stF. first [clear stF | gw_hide stF | idtac]; first [clear stW | gw_hide stW | idtac]; first [clear stR | gw_hide stR | idtac]; first [clear k | gw_hide k | idtac]; first [clear n | gw_hide n | idtac]; first [clear e | gw_hide e | idtac]; first [clear p | gw_hide p | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. rewrite fin_regions_W, fin_regions_R. apply lookup_insert_eq. Qed.
#[using="r Hr"] Lemma fin_groups_W : s_groups stW = s_groups st.
Proof. clear - r Hr st rid g nb nd p e n k stR stW stF. first [clear stF | gw_hide stF | idtac]; try gw_hide stW; try gw_hide stR; first [clear k | gw_hide k | idtac]; first [clear n | gw_hide n | idtac]; first [clear e | gw_hide e | idtac]; first [clear p | gw_hide p | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. unfold stW, stR, remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="r Hr"] Lemma fin_meta_W : get_meta_rec stW g = m_set_maplen (nd / 4096) (get_meta_rec st g).
Proof. clear - r Hr st rid g nb nd p e n k stR stW stF. first [clear stF | gw_hide stF | idtac]; try gw_hide stW; try gw_hide stR; first [clear k | gw_hide k | idtac]; first [clear n | gw_hide n | idtac]; try gw_hide e; first [clear p | gw_hide p | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; try gw_hide g; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac].
unfold stW. change (get_meta_rec (wr8 e 0 stR) g) with (get_meta_rec stR g).
unfold stR, remap_region. rewrite get_meta_rec_upd, aptr_eqb_refl. unfold upd_shadow, upd_region, get_region. rewrite Hr. reflexivity.
Qed.
#[using="r Hr"] Lemma fin_conc q : conc stF q = if (fst q =? rid)%N then nb + snd q else conc st q.
Proof. clear - r Hr q st rid g nb nd p e n k stR stW stF. try gw_hide stF; try gw_hide stW; try gw_hide stR; first [clear k | gw_hide k | idtac]; first [clear n | gw_hide n | idtac]; first [clear e | gw_hide e | idtac]; first [clear p | gw_hide p | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear g | gw_hide g | idtac]; try gw_hide rid; first [clear st | gw_hide st | idtac].
unfold stF. rewrite conc_havoc, conc_set_size. change (conc stW q) with (conc stR q).
unfold conc, get_region. rewrite fin_regions_R. destruct (N.eqb_spec (fst q) rid) as [E|NE].
- rewrite E, lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="r Hr"] Lemma fin_ctx : ctx stF = ctx st.
Proof. clear - r Hr st rid g nb nd p e n k stR stW stF. try gw_hide stF; try gw_hide stW; try gw_hide stR; first [clear k | gw_hide k | idtac]; first [clear n | gw_hide n | idtac]; first [clear e | gw_hide e | idtac]; first [clear p | gw_hide p | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear g | gw_hide g | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac].
unfold stF. rewrite ctx_havoc', ctx_set_size'. change (ctx stW) with (ctx stR).
unfold stR, remap_region, upd_meta, put_meta, upd_shadow, upd_region, get_region. rewrite Hr. reflexivity.
Qed.
#[using="r Hr"] Lemma fin_brk_link pb : match c_brk (ctx st) with BrkLive q _ => q <> rid | _ => True end -> brk_link st pb -> brk_link stF pb.
Proof. clear - r Hr pb st rid g nb nd p e n k stR stW stF. first [clear stF | gw_hide stF | idtac]; first [clear stW | gw_hide stW | idtac]; first [clear stR | gw_hide stR | idtac]; first [clear k | gw_hide k | idtac]; first [clear n | gw_hide n | idtac]; first [clear e | gw_hide e | idtac]; first [clear p | gw_hide p | idtac]; first [clear nd | gw_hide nd | idtac]; first [clear nb | gw_hide nb | idtac]; first [clear g | gw_hide g | idtac]; try gw_hide rid; try gw_hide st.
intros Hq H. unfold brk_link in *. rewrite fin_ctx. destruct (c_brk (ctx st)) as [| |q off]; try exact I.
rewrite fin_conc. cbn [fst snd]. replace (q =? rid)%N with false by (symmetry; apply N.eqb_neq; gw_exact Hq). gw_exact H.
Qed.
End FIN.

End RC__1.

End G.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QytA QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
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

Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_0)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).
Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_del_group : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_del_group) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_del_group)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Ltac rctx_same := intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.

Definition rmrep_put_group_new : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_put_group_new) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_put_group_new)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved"] Lemma rmrep_set_bounce : forall st m i v,
rmrep st m -> 0 <= i < 32 ->
rmrep (set_bounce i v st) (write_to_mem m (wa ((RATP + 132848) + i)) [b8 v]).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RATP segs. gw_expose_fam RATP.
intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (munch_write [((RATP + 132848) + i, (RATP + 132848) + i + 1)] m m ((RATP + 132848) + i) [b8 v] (munch_refl _ m)
ltac:(gw_expose_fam RATP; lia) ltac:(cbn; gw_expose_fam RATP; lia) ltac:(cbn; lia)) as MU.
pose proof (wmono_write segs m m (wa ((RATP + 132848) + i)) [b8 v] (wmono_refl segs m)) as WM.
eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
- rctx_same.
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- right. split; [reflexivity| rctx_same].
- left. rewrite bouncess_set by lia. replace ((RATP + 132848) + i) with (((RATP + 132848)) + i) by lia.
apply (u8arr_write segs m ((RATP + 132848)) (bouncess st) i (b8 v)); [gw_exact X5| rewrite bouncess_length; lia].
- right. split; [| rctx_same].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.
End RC__1.

Section RC__2.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved"] Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
conc st q = conc st g -> q = g.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved.
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

Section RC__3.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_regroup : forall st m m' b gh g ai (w8' : byte),
rmrep st m -> (s_groups st) !! b = Some gh ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
munch [(conc st b, conc st b + 9)]%Z m m' -> wmono segs m m' ->
rw_cells segs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
rmrep (put_group b (Some g) ai st) m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
pose proof (rmrep_del_group st m b MR) as MR1.
assert (MR2 : rmrep (del_group b st) m').
{ eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
pose proof (round_up_pg_ge (r_len r)).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
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
- gw_expose_fam RGOT_SSP. lia.
- gw_expose_fam RATP. lia. }
rewrite <- put_group_del.
eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | gw_exact Hr | gw_exact Kr | gw_exact B0 | gw_exact B16 | gw_exact BA | gw_exact RC | gw_exact Hw8].
unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_set_group_ai : forall st m m' b g ai0 ai (w8' : byte),
rmrep st m -> (s_groups st) !! b = Some (mkGhdr (Some g) ai0) ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
munch [(conc st b, conc st b + 9)]%Z m m' -> wmono segs m m' ->
rw_cells segs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
rmrep (set_group_active_idx b ai st) m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved segs.
intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
eapply rmrep_regroup; eauto.
Qed.

#[using="Type"] Lemma rmrep_ctr_byte_read : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
ov_read_bytes segs m (wa ((RATP + 131980))) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof. clear - segs RATP. gw_expose_fam RATP.
intros st m (_ & (HD & _) & _) CR.
destruct HD as [[_ HB] _]. unfold ctx_head_cells in HB. cbn [cells_bytes cbytes app] in HB.
replace (RATP + 131980) with (RATP + 131968 + 12) by lia; rewrite (bytes_at_read segs m (RATP + 131968) _ 12 1 HB).
all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
change (Z.to_nat 12) with 12%nat.
unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

End RC__3.

End G.
End Mqc.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq2.

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
Hypothesis land_ones_l : gw_hyp ltac:(let T := gw_callee_type0 (Q91D.land_ones_l segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 524; 700; 720; 752; 768; 1412; 1424; 1436]%Z in exact T).
Hypothesis sra63_K_neg : gw_hyp ltac:(let T := gw_callee_type0 (Q8QT.sra63_K_neg segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 996; 1524; 1532]%Z in exact T).
Hypothesis sra63_K_pos : gw_hyp ltac:(let T := gw_callee_type0 (Q8QT.sra63_K_pos segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 996; 1524; 1532]%Z in exact T).
Hypothesis ndr_lt64 : gw_hyp ltac:(let T := gw_callee_type0 (Q8QT.ndr_lt64 segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 996; 1524; 1532]%Z in exact T).
Hypothesis ndr_ge64 : gw_hyp ltac:(let T := gw_callee_type0 (Q8QT.ndr_ge64 segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 996; 1524; 1532]%Z in exact T).

Definition divtf3_stmt := Eval cbv beta delta [QVbl.divtf3_stmt] in (QVbl.divtf3_stmt segs base).

Definition if_ltb_t := @QkTt.if_ltb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_ltb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_ltb_f := @QkTt.if_ltb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_ltb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_leb_t := @QkTt.if_leb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_leb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_leb_f := @QkTt.if_leb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_leb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_eqb_t := @QkTt.if_eqb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_eqb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_eqb_f := @QkTt.if_eqb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_eqb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_nltb_t := @QkTt.if_nltb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_nltb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_nltb_f := @QkTt.if_nltb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_nltb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_nleb_t := @QkTt.if_nleb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_nleb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_nleb_f := @QkTt.if_nleb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_nleb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_neqb_t := @QkTt.if_neqb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_neqb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_neqb_f := @QkTt.if_neqb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_neqb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition Lepi := @QkTt.Lepi segs base CODE BASE4 BASER mulhu_shl32.
Definition Lzero := @QkTt.Lzero segs base CODE BASE4 BASER mulhu_shl32.
Definition Linf := @QkTt.Linf segs base CODE BASE4 BASER mulhu_shl32.
Ltac decide_ifs ::=
repeat (match goal with
| |- context [if (?x <? ?y) then ?A else ?B] => first [rewrite (if_ltb_t x y A B) by lia | rewrite (if_ltb_f x y A B) by lia]
| |- context [if negb (?x <? ?y) then ?A else ?B] => first [rewrite (if_nltb_t x y A B) by lia | rewrite (if_nltb_f x y A B) by lia]
| |- context [if (?x <=? ?y) then ?A else ?B] => first [rewrite (if_leb_t x y A B) by lia | rewrite (if_leb_f x y A B) by lia]
| |- context [if negb (?x <=? ?y) then ?A else ?B] => first [rewrite (if_nleb_t x y A B) by lia | rewrite (if_nleb_f x y A B) by lia]
| |- context [if (?x =? ?y) then ?A else ?B] => first [rewrite (if_eqb_t x y A B) by lia | rewrite (if_eqb_f x y A B) by lia]
| |- context [if negb (?x =? ?y) then ?A else ?B] => first [rewrite (if_neqb_t x y A B) by lia | rewrite (if_neqb_f x y A B) by lia]
end).

Definition divtf3_post := Eval cbv beta delta [Qy8Z.divtf3_post] in (Qy8Z.divtf3_post segs).
Definition divtf3_core := @Qy8Z.divtf3_core segs base CODE BASE4 BASER land_ones_l mulhu_shl32.

Definition LnormA := @QCa8.Mq2.LnormA segs base CODE BASE4 BASER sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64.
Definition LnormB := @QCa8.Mq2.LnormB segs base CODE BASE4 BASER sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Section Walk.
Variables (sp a0 a1 a2 a3 : word).
Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation E_sgn := (Z.land (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63) 18446744073709551615).
Notation E_aExp := (Z.shiftr (Z.land (Z.shiftl a_hi 1) 18446744073709551615) 49).
Notation E_bExp := (Z.shiftr (Z.land (Z.shiftl b_hi 1) 18446744073709551615) 49).
Notation E_aSig := (Z.land a_hi 281474976710655).
Notation E_bSig := (Z.land b_hi 281474976710655).
Notation E_aAbs := (Z.land a_hi 9223372036854775807).
Notation E_bAbs := (Z.land b_hi 9223372036854775807).
Notation MONE := (Z_to_bv 64 (-1)).
Notation M48 := (Z_to_bv 64 281474976710655).

Ltac hyp :=
match goal with
| H : mem_inv _ ?m |- mem_inv _ ?m => exact H
| H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
| H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
| H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
| H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
| H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
| H : bv_unsigned ?w = _ |- bv_unsigned ?w = _ => exact H
| H : ?x = ?y |- ?x = ?y => exact H
| H : ?x <> ?y |- ?x <> ?y => exact H
| H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
| |- (_ <= _ <= _)%Z => lia
| |- (0 <= _ < _)%Z => first [zrange2 | lia]
end.
Ltac join L := eapply L; try hyp.

Ltac model_in H := sf_model_in H.
Ltac eblia := rewrite ?Z.shiftl_mul_pow2 in * by lia; blia.
Ltac decide_in_cond H c :=
match c with
| context [Z.eqb ?x ?y] =>
first [ rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia) ]
| context [Z.ltb ?x ?y] =>
first [ rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia) ]
| context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia) ]
end.
Ltac decide_head H :=
cbn_bool_in H;
lazymatch type of H with
| _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond H c end
end;
cbn_bool_in H.
Ltac res_words := rewrite ?lo64_mk128, ?hi64_mk128 by zrange; first [ apply Z_to_bv_lit_self | weq ].
Ltac exact_HR0 :=
lazymatch goal with |- ?g =>
match goal with
| HR : ?t |- _ => constr_eq t g; exact HR
| HR : @eq Z ?r ?t |- _ => fail 0 "exact_HR: goal" g "but HR:" r "=" t
end
end.
Ltac exact_HR := rewrite ?unsigned_lit by zrange; cbv delta [INF_HI QNAN_HI QUIET_HI]; exact_HR0.

#[using="CODE BASE4 BASER mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Lemma Lbchk : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (sc1 : Z) w3 w4
y1 y8 y9 y13 y28' y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
y28' = Z_to_bv 64 sc1 ->
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(-600 <= sc1 <= 16)%Z ->
R = FD_p2b a_hi b_lo b_hi (bv_unsigned w3) (bv_unsigned w4) sc1 ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
w4 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 w3
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28' y29 y30 y31)
F (Z_to_bv 64 (base + 0x7f8)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros -> MI MU WM ST FR SPLO Rsc HR.
pose_word_ranges.
assert (Ra : 0 <= E_aExp < 32768).
{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
assert (Rb : 0 <= E_bExp < 32768).
{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
unfold FD_p2b in HR. model_in HR.
zstep. zstep. if_cases K; zify_cond K; decide_head HR.
-
join divtf3_core; exact_HR.
- rewrite norm_denormal_eta in HR. cbn_bool_in HR.
eapply LnormB; [zrange | lia |]. intros.
pose proof (nd_clz_range E_bSig b_lo).
pose proof (nd_hi_range E_bSig b_lo ltac:(zrange)). pose proof (nd_lo_range E_bSig b_lo).
join divtf3_core; rewrite ?unsigned_lit by first [assumption | zrange]; exact_HR.
Qed.

#[using="CODE BASE4 BASER mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Lemma Lp2r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y1 y8 y9 y13 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
R = FD_p2 a_lo a_hi b_lo b_hi ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 (Z_to_bv 64 E_aSig)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) y29 y30 y31)
F (Z_to_bv 64 (base + 0x558)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO HR.
pose_word_ranges.
unfold FD_p2 in HR. model_in HR.
zstep. zstep. if_cases K; zify_cond K; decide_head HR.
-
do 2 zstep. join Lbchk; [reflexivity | lia | exact_HR].
- rewrite norm_denormal_eta in HR. cbn_bool_in HR.
eapply LnormA; [zrange |]. intros.
pose proof (nd_clz_range E_aSig a_lo).
pose proof (nd_hi_range E_aSig a_lo ltac:(zrange)). pose proof (nd_lo_range E_aSig a_lo).
join Lbchk; [reflexivity | lia | rewrite ?unsigned_lit by first [assumption | zrange]; exact_HR].
Qed.

#[using="CODE BASE4 BASER mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Lemma Linfr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y1 y8 y9 y13 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
R = FD_inf a_lo a_hi b_lo b_hi ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
a0 (Z_to_bv 64 E_sgn) a2 y13 (Z_to_bv 64 E_bAbs) MONE M48 (Z_to_bv 64 E_aSig)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) y29 y30 y31)
F (Z_to_bv 64 (base + 0x400)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO HR.
pose_word_ranges.
unfold FD_inf in HR. model_in HR.
do 4 zstep. zstep. if_cases K7; zify_cond K7; decide_head HR.
-
do 2 zstep. zstep. if_cases K9; zify_cond K9; decide_head HR.
+
zstep. zstep. if_cases K11; zify_cond K11; decide_head HR.
*  zstep. zstep. if_cases K12; zify_cond K12; decide_head HR.
-- join Lzero; exact_HR.
-- do 3 zstep. join Lzero. all: zsimp; exact_HR.
* zstep. zstep. if_cases K12; zify_cond K12; decide_head HR.
--  join Linf; exact_HR.
-- join Lp2r; exact_HR.
+  join Lzero; exact_HR.
-
do 2 zstep. zstep. if_cases K8; zify_cond K8; decide_head HR.
+ join Linf; exact_HR.
+ subst R. do 4 zstep. join Lepi; res_words.
Qed.

#[using="CODE BASE4 BASER mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Lemma Lbr : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y1 y8 y9 y14 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
R = FD_b a_lo a_hi b_lo b_hi ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
a0 (Z_to_bv 64 E_sgn) a2 a3 y14 MONE M48 (Z_to_bv 64 E_aSig)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E_aAbs) (Z_to_bv 64 9223372036854775807) y30 y31)
F (Z_to_bv 64 (base + 0x3e8)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO HR.
pose_word_ranges.
unfold FD_b in HR. model_in HR.
do 3 zstep. zstep. if_cases K5; zify_cond K5; decide_head HR.
-
zstep. zstep. if_cases K6; zify_cond K6; decide_head HR.
+  join Linfr; exact_HR.
+ subst R. do 5 zstep. join Lepi; res_words.
- zstep. zstep. if_cases K6; zify_cond K6; decide_head HR.
+  subst R. do 5 zstep. join Lepi; res_words.
+ join Linfr; exact_HR.
Qed.

#[using="CODE BASE4 BASER mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Lemma Lspec : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
y1 y8 y9 y28 y29 y30 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
R = FD_a a_lo a_hi b_lo b_hi ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp (Z_to_bv 64 E_bSig) (Z_to_bv 64 E_aExp) (Z_to_bv 64 E_bExp) y8 y9
a0 (Z_to_bv 64 E_sgn) a2 a3 a1 MONE M48 (Z_to_bv 64 E_aSig)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 (base + 0x3cc)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO HR.
pose_word_ranges.
unfold FD_a in HR. model_in HR.
do 4 zstep. zstep. if_cases K3; zify_cond K3; decide_head HR.
-
zstep. zstep. if_cases K4; zify_cond K4; decide_head HR.
+ join Lbr; exact_HR.
+ subst R. do 4 zstep. join Lepi; res_words.
- zstep. zstep. if_cases K4; zify_cond K4; decide_head HR.
+ subst R. do 4 zstep. join Lepi; res_words.
+ join Lbr; exact_HR.
Qed.

#[using="CODE BASE4 BASER mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Lemma divtf3_walk : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk segs m (bv_unsigned sp - 112) (bv_unsigned sp) ->
mem_inv segs m ->
(4096 <= bv_unsigned sp)%Z ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_div_w a_lo a_hi b_lo b_hi) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until m. intros ST MI SPLO.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl segs m) as WM.
pose_word_ranges.
carve_frame 112%nat ST.
remember (f128_div_w a_lo a_hi b_lo b_hi) as R eqn:HR.
unfold f128_div_w in HR. model_in HR.
do 14 zstep. do 16 zstep.
rewrite <- (Z_to_bv_land64 (Z.shiftl (Z.shiftr (Z.lxor b_hi a_hi) 63) 63)).
assert (Ra : 0 <= E_aExp < 32768).
{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }
assert (Rb : 0 <= E_bExp < 32768).
{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. zb_masks. Z.div_mod_to_equations. lia. }

zstep. if_cases K1; zify_cond K1; decide_head HR.
-  join Lspec; exact_HR.
- unfold FD_0b in HR. model_in HR.
zstep. zstep. if_cases K2; zify_cond K2; decide_head HR.
+ join Lspec; exact_HR.
+ zstep. join divtf3_core; exact_HR.
Qed.
End Walk.

#[using="CODE BASE4 BASER mulhu_shl32 land_ones_l sra63_K_neg sra63_K_pos ndr_lt64 ndr_ge64"] Theorem divtf3_spec : divtf3_stmt.
Proof.
unfold divtf3_stmt. intros.
rewrite f128_div_words by (pose_word_ranges; assumption).
apply divtf3_walk; assumption.
Qed.

End G.
