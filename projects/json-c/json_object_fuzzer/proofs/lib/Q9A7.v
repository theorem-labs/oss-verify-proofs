(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QlEo_c1 QWxq_c1 Qfw3_c1 Q5Rg Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QlEo_c1.Mq0 QWxq_c1.Mq1 Qfw3_c1.Mq2 Q5Rg.Mq0.
Import ListNotations.
Open Scope bv_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma mmap_len_ge : forall len, (len <= mmap_len len)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma mmap_len_nonneg : forall len, (0 <= len)%Z -> (0 <= mmap_len len)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma mmap_len_aligned : forall len, (len mod 4096 = 0)%Z -> mmap_len len = len.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Definition munmap_ret (a : range_ans) : word :=
match a with RgErr _ => Z_to_bv 64 (-1) | RgDone _ => Z_to_bv 64 0 end.
Definition rg_errno (a : range_ans) (errv : word) : word :=
match a with RgErr e => Z_to_bv 64 e | RgDone _ => errv end.

#[using="Type"] Lemma land_ldiff_distr' x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

#[using="Type"] Lemma land_m4096 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x - x mod 4096)%Z.
Proof.
intros Hx.
assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
rewrite land_ldiff_distr'. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.

#[using="Type"] Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Definition mmap_fix_errno (e : Z) : Z := if (e =? 1)%Z then 12%Z else e.

Definition mmap_raw (isnone : bool) (x len : Z) (m : word -> option byte) : word -> option byte :=
if isnone then apply_unmaps m [(wa x, Z_to_bv 64 (mmap_len len))]
else apply_zeros m [(wa x, Z_to_bv 64 (mmap_len len))].

Definition fixed_shape (A L : Z) (r : word) (u : bool) : resp :=
if u then mkEffectU r [] [] [(wa A, Z_to_bv 64 (mmap_len L))] [] [] else mkEffectU r [] [] [] [] [].

#[using="Type"] Lemma alloc_ceiling_val : alloc_ceiling = rc_ceil.
Proof. reflexivity. Qed.
End RC__1.

Ltac sys_nret_raw :=
rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
let p' := eval vm_compute in (p + 4)%Z in
replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
| _ => idtac
end);
first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ]. Ltac mkr__sys_nret_raw_0 := rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
let p' := eval vm_compute in (p + 4)%Z in
replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
| _ => idtac
end);
first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Export Qfw3_c1.Mq3.
Export QZAi.
Import ListNotations.
Open Scope bv_scope.

Lemma b2z_Zb2z : b2z = Z.b2z. Proof. reflexivity. Qed.

Ltac zb_masks_in H :=
repeat match type of H with
| context [Z.land ?x ?m] =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z in H
by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
end.

Ltac zs_wrap e ::= zs_wrap_land e. Ltac mkr__zs_wrap_0 e := zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H. Ltac mkr__zs_wrap_in_1 e H := zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land. Ltac mkr__zs_idioms_2 := zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H. Ltac mkr__zs_idioms_in_3 H := zs_idioms_land_in H.

Ltac unfold_sf_in H :=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H. Ltac mkr__unfold_sf_in_4 H := cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H.
Ltac unfold_sf :=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI].

Ltac norm_model H := unfold_sf_in H; zb_fold_lits_in H.

Ltac get_head t := lazymatch t with ?g _ => get_head g | _ => t end.

Tactic Notation "model_hyp" ident(HR) constr(t) :=
assert (HR : t = t) by reflexivity;
let h := get_head t in unfold h in HR at 2;
norm_model HR.

Notation W64 := 18446744073709551615%Z.

Ltac model_eval :=
lazy -[Z.shiftr Z.shiftl Z.land Z.lor Z.lxor Z.lnot Z.mul Z.add Z.sub Z.opp Z.modulo Z.div
Z.ltb Z.eqb Z.leb Z.pow bv_unsigned].

Tactic Notation "model_end" constr(X) constr(t) :=
replace (Z_to_bv 64 X) with (Z_to_bv 64 t) by (f_equal; model_eval; reflexivity).

Lemma lo64_mk128' : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi)%Z -> lo64 (mk128 hi lo) = lo.
Proof.
intros hi lo Hlo Hhi. unfold lo64, mk128. rewrite wrap64_mod.
rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low, (Z.testbit_neg_r _ (i - 64)) by lia. cbn. apply andb_true_r.
- rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
symmetry. destruct (Z.eq_dec lo 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma lo64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> lo64 (mk128 hi lo) = lo.
Proof. intros. apply lo64_mk128'; lia. Qed.

Lemma hi64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (mk128 hi lo) = hi.
Proof.
intros hi lo Hlo Hhi. unfold hi64, mk128. rewrite wrap64_mod.
rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 lo), Z.div_small, Z.lor_0_r by lia. apply Z.mod_small. lia.
Qed.

Lemma mk128_regs : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z ->
Z_to_bv 64 (lo64 (mk128 hi lo)) = Z_to_bv 64 lo /\ Z_to_bv 64 (hi64 (mk128 hi lo)) = Z_to_bv 64 hi.
Proof. intros. rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.

Lemma land_even_mask : forall y, Z.land y 18446744073709551614 = (Z.land y 18446744073709551615 - Z.land y 1)%Z.
Proof.
intros y. change 18446744073709551615%Z with (Z.lor 18446744073709551614 1).
rewrite Z.land_lor_distr_r, lor_disjoint_add; [lia|].
rewrite (Z.land_comm (Z.land y _) (Z.land y 1)), Z.land_assoc, (Z.land_comm (Z.land y 1) y), Z.land_assoc, Z.land_diag.
rewrite <- Z.land_assoc. change (Z.land 1 18446744073709551614) with 0%Z. apply Z.land_0_r.
Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof. intros. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma round_even_idiom : forall x, (0 <= x)%Z ->
Z_to_bv 64 (Z.land (x + 1) 18446744073709551614) = Z_to_bv 64 (x + Z.land x 1).
Proof.
intros x Hx. apply Z_to_bv_eqm. rewrite land_even_mask, land_W64, !land_1.
Z.div_mod_to_equations. lia.
Qed.

Ltac bool_atom_cases :=
repeat match goal with
| |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
| |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
| |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
end.

Ltac weq :=
first [ reflexivity
| f_equal; zeq
| rewrite round_even_idiom by zrange_nonneg; weq_arith
| weq_arith ]
with weq_arith :=
apply Z_to_bv_eqm; rewrite ?land_even_mask, ?land_1; zb_masks; cbv delta [Z.b2z]; cbn [negb];
bool_atom_cases; cbn [negb]; pose_word_ranges; Z.div_mod_to_equations; lia.

Ltac ms_eq :=
first [ reflexivity
| lazymatch goal with
| |- Z_to_bv 64 _ = Z_to_bv 64 _ => weq
| |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
| |- Z_to_bv 64 (bv_unsigned _) = _ => apply Z_to_bv_bv_unsigned
| |- context [mkR] => unfold mkR; ms_eq
| |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; ms_eq
| |- TNode _ _ _ = TNode _ _ _ => f_equal; ms_eq
| |- Some _ = Some _ => f_equal; ms_eq
end ].

Ltac sf_finish :=
apply evt_done;
lazymatch goal with |- ?P ?ms => try unfold P end; hnf;
rewrite ?lo64_mk128, ?hi64_mk128 by zrange;
repeat (lazymatch goal with |- ex _ => eexists end);
split; [ ms_eq | repeat match goal with |- _ /\ _ => split end; try assumption ].

Lemma signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Ltac signed_lits_in H :=
repeat match type of H with
| context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_of_Z z) in H by lia
end.

Lemma mod64_land63 : forall y, (y mod 64 = Z.land y 63)%Z.
Proof. intros. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land63_idem : forall y, Z.land (Z.land y 63) 63 = Z.land y 63.
Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

Ltac zs_idioms_sf :=
match goal with
| |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
| |- context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem
end.
Ltac zs_idioms_sf_in H :=
match type of H with
| context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
| context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem in H
end.
Ltac zs_idioms ::= zs_idioms_sf. Ltac mkr__zs_idioms_5 := zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H. Ltac mkr__zs_idioms_in_6 H := zs_idioms_sf_in H.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Ltac name_list xs L :=
lazymatch type of L with
| length _ = O => destruct xs; [clear L | cbn in L; discriminate]
| length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
end.

Ltac window base k HW :=
lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
let xs := fresh "xs" in let L := fresh "L" in
destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
end.

Ltac woff base c :=
let cz := eval vm_compute in (Z.of_nat c) in
lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

Ltac anorm REG imm :=
lazymatch REG with
| Z_to_bv 64 ?E =>
let E' :=
lazymatch imm with
| 0%Z => E
| _ => lazymatch E with
| Z.add ?x ?a =>
let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
lazymatch isl with
| true => let s := eval vm_compute in (a + imm)%Z in
lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
| false => constr:(Z.add E imm)
end
| _ => constr:(Z.add E imm)
end
end in
constr:(Z_to_bv 64 E')
| _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
end.

Ltac cur_mem_addr :=
lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (Load _ _ _ ?rs ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
| Some (Store _ ?rs _ ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
end end end. Ltac mkr__cur_mem_addr_0 := lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (Load _ _ _ ?rs ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
| Some (Store _ ?rs _ ?imm, _) =>
let rz := eval vm_compute in (bv_unsigned rs) in
let immz := eval vm_compute in (bv_signed imm) in
let REG := reg_val rz in anorm REG immz
end end end.

Ltac addr_tac :=
unfold wa;
first [ reflexivity
| f_equal; lia
| lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

Definition ld_facts (base : Z) (c j kw : nat) (i : Z) : Prop :=
(0 <= base)%Z /\ (c + j <= kw)%nat /\ (i = base + Z.of_nat c)%Z.

Lemma mc_read1 : forall segs m S src kw base xsw c i a b,
bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
ld_facts base c 1 kw i -> nth_error xsw c = Some b -> a = wa (S + i) ->
ov_read_bytes segs m a 1 = Some [b].
Proof.
intros segs m S src kw base xsw c i a b SRC HW (Hb & Hc & Hi) Hn Ha.
eapply (u8ro_read segs m S src i b a SRC); [ | lia | exact Ha ].
rewrite <- Hn. eapply window_nth; eauto; lia.
Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
ld_facts base c 4 kw i -> a = wa (S + i) ->
exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
intros segs m S src kw base xsw c i a SRC HW HL (Hb & Hc & Hi) ->.
assert (L : (Z.to_nat base + kw <= length src)%nat).
{ apply (f_equal (@length byte)) in HW. rewrite length_firstn, length_skipn, HL in HW. lia. }
exists (firstn 4 (skipn (Z.to_nat i) src)). split; [|split].
- apply (bytes_at_read segs m S src i 4 SRC); lia.
- eapply window_sub; eauto; lia.
- rewrite length_firstn, length_skipn. lia.
Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
(S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
firstn kw (skipn (Z.to_nat base) src) = xsw ->
st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ (_ & _ & _ & HP & Hk & _) Ha.
eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
st_facts S D n base c k kw P ->
xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
bytes_at segs (write_to_mem m1 a xs) S src /\
u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
wmono segs m0 (write_to_mem m1 a xs).
Proof.
intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW
(Hb & Hc & HPb & HP & Hk & SEP & D0 & Dn) Hxs Hl Ha.
pose proof (proj1 CP) as Lbs.
assert (SOK : store_ok segs m1 a (length xs) = true).
{ rewrite Hl. eapply mc_store_ok; eauto. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; eauto; lia. }
subst a. split; [|split; [|split; [|split; [|split]]]].
- apply bytes_at_write_other; [exact SRC | lia | lia | rewrite LEN; lia].
- apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN. lia.
- apply (f_equal (@length byte)) in CP || idtac.
rewrite <- Hl. apply copied_updZ; [exact CP | lia | | rewrite LEN; lia].
rewrite Hl, Hxs. eapply window_sub; eauto; lia.
- apply mem_inv_store; assumption.
- apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
- apply wmono_write. exact WM.
Qed.

Ltac ld1 HW c :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
let i := woff base c in
let a := cur_mem_addr in
let RD := fresh "RD" in
pose proof (mc_read1 segs m S src k base xs c i a _ SRC HW
ltac:(unfold ld_facts; lia) ltac:(reflexivity) ltac:(addr_tac)) as RD;
zstep; try clear RD;
lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end
end end.

Ltac ld4 HW c w :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
let i := woff base c in
let a := cur_mem_addr in
let RD := fresh "RD" in let Ew := fresh "E" w in let Lw := fresh "L" w in
destruct (mc_read4 segs m S src k base xs c i a SRC HW ltac:(reflexivity) ltac:(unfold ld_facts; lia) ltac:(addr_tac))
as [w [RD [Ew Lw]]];
cbn [firstn skipn] in Ew;
zstep; try clear RD
end end.

Ltac zify_bytes :=
repeat match goal with
| |- context [bv_unsigned ?b] =>
lazymatch type of b with
| byte => pose proof (byte_range b); generalize dependent (bv_unsigned b); intros
end
end.
Ltac solve_le K :=
repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
first [ apply le4_of_mod32; [reflexivity|] | apply le1_of_mod8 ];
cbn [map le_val]; rewrite ?unsigned_lit_wrap; rewrite ?lw_unsigned4;
zify_bytes;
rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?bv_swrap32_eq, ?bv_wrap32_eq by lia;
lazymatch K with
| 0%Z => idtac
| _ => first [ rewrite (lor_add _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
| rewrite (lor_add' _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ] ]
end;
Z.div_mod_to_equations; lia.

Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.

Ltac by_le K :=
symmetry;
repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
first
[ lazymatch goal with
| |- le4 (Z_to_bv 64 (Z.lor (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _) _)) = _ =>
lazymatch k with 24%Z => apply merge_a24 | 16%Z => apply merge_a16 | 8%Z => apply merge_a8 end
| |- le4 (Z_to_bv 64 (Z.lor _ (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _))) = _ =>
lazymatch k with 24%Z => apply merge_r24 | 16%Z => apply merge_r16 | 8%Z => apply merge_r8 end
| |- le1 (Z_to_bv 64 (Z.shiftr _ ?k)) = _ =>
lazymatch k with 8%Z => apply lwb1 | 16%Z => apply lwb2 end
| |- le1 (sext _ _) = _ => apply lwb0
end
| solve_le K ].

Ltac cst_core HW c k bytes_tac SF :=
lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
let kz := eval vm_compute in (Z.of_nat k) in
lazymatch goal with
| SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
|- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
replace bs0 with xs by bytes_tac;
let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
as (SRC' & DST' & CP' & MI' & MU' & WM');
change (Z.of_nat k) with kz in CP';
clear SRC DST CP MI MU WM SF;
repeat match goal with
| H : store_ok segs m _ _ = true |- _ => clear H
| H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
end;
let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
rename MI' into MI; rename MU' into MU; rename WM' into WM
end end.

Ltac cst HW c k bytes_tac :=
lazymatch goal with SF : st_facts _ _ _ _ c k _ _ |- _ => cst_core HW c k bytes_tac SF end.

Ltac st HW c k bytes_tac :=
lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
lazymatch goal with
| SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
let a := cur_mem_addr in
let SF := fresh "SF" in let SOK := fresh "SOK" in
assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
zstep; [ cst_core HW c k bytes_tac SF | .. ]
end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

Ltac by_win HW c :=
lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
| symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
end.

Ltac cp_norm P' :=
lazymatch goal with CP : copied ?src ?bs (Z.to_nat ?P) |- _ => replace (Z.to_nat P) with (Z.to_nat P') in CP by lia end.

Definition mc_inv (segs : list MemImageType.Segment) (S D : Z) (src : list byte) (W : list ivl)
(m0 m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

Ltac inv_tac :=
lazymatch goal with
| |- mc_inv _ _ _ _ _ _ _ _ _ =>
split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.

Ltac use_side :=
first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

Ltac finish2 :=
apply evt_done;
lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
hnf;
repeat (lazymatch goal with |- ex _ => eexists end);
lazymatch goal with
| |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
| |- _ = _ => cbv delta [mkR]; reflexivity
end;
repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac mc_fin :=
lazymatch goal with
| DST : u8arr _ ?m1 _ ?bs, CP : copied ?src ?bs (Z.to_nat ?P), L : length ?src = _ |- _ =>
let E := fresh "E" in
pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
apply rw_cells_of_u8arr in DST; rewrite L in DST
end;
finish2.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac lstep := zstep; fix_lit_store.
