(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Export Walk.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Export SoftFloat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_SFModel () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.SoftFloat."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "2and"; "2eq"; "3Z"; "4b2z"; "4hi64"; "4lo64"; "4mk128"; "5add"; "5b2z"; "5land"; "5le"; "5lor"; "5lt"; "5modulo"; "5opp"]; ["5pow"; "5sub"; "0a"; "0b"; "0hi"; "0lo"; "6Z_to_bv"; "6bv"; "6bv_signed"; "0x"; "0y"; "0z"]]).
Lemma b2z_Zb2z : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "7'2'0'3pQ821&4&9%63321"). Proof. reflexivity. Qed.
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
Ltac zs_wrap e ::= zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H.
Ltac unfold_sf_in H :=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
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
Lemma lo64_mk128' : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "J'3'1&;zr1%3221&=&@+2+R0%3221%5271%;271r3%<2;1'2&6&7r4%2216%411%63E18p081p0;1pQ<H1pQ:I1").
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
Lemma lo64_mk128 : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "L'3'1&;zr1%3221&=&@+2+R0%3221%5271%;271r3%<2;1%9225%?221'2&6&7r4%2218%411%63G1:p081p0=1pQ<J1pQ:K1").
Proof. intros. apply lo64_mk128'; lia. Qed.
Lemma hi64_mk128 : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "L'3'1&;zr1%3221&=&@+2+R0%3221%5271%;271r3%<2;1%9225%?221'2&5&7r4%2218%411%63G13p081p0=1pQ<J1pQ:K1").
Proof.
intros hi lo Hlo Hhi. unfold hi64, mk128. rewrite wrap64_mod.
rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 lo), Z.div_small, Z.lor_0_r by lia. apply Z.mod_small. lia.
Qed.
Lemma mk128_regs : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "Q8'3'1&;zr1%3221&=&@+2+R0%3221%5271%;271r3%<2;1%9225%?221'2'GyR0%211&F&6&7r4%221<%411%6281%729?%<3921&5%116%;2=1%<2>9%A3>21%Q2261p0D1p0I1pQ<Q61pQ:Q71").
Proof. intros. rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.
Lemma lor_disjoint_add : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "A'3'2&:r2r1%3221z%63721&<r3%2217&8%1239%<3=31p071pQ8?1pQ6@1").
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.
Lemma land_even_mask : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel ">'3'2&:r1+_oooooooooooN%3221&A+_oooooooooooO%6251+1%8271%5231%;3<71pQF=1").
Proof.
intros y. change 18446744073709551615%Z with (Z.lor 18446744073709551614 1).
rewrite Z.land_lor_distr_r, lor_disjoint_add; [lia|].
rewrite (Z.land_comm (Z.land y _) (Z.land y 1)), Z.land_assoc, (Z.land_comm (Z.land y 1) y), Z.land_assoc, Z.land_diag.
rewrite <- Z.land_assoc. change (Z.land 1 18446744073709551614) with 0%Z. apply Z.land_0_r.
Qed.
Lemma land_1 : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel ";'3'2&:r1+1%3221&>+2%2251%83941pQF:1").
Proof. intros. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_W64 : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel ">'3'2&:r1+_oooooooooooO%3221&>&@+2+R0%3221%5281%;3<71pQF=1").
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.
Lemma round_even_idiom : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "H'3&;zr1%3221'2'GyR0%211&F&:&8r2+1%3221+_oooooooooooN%6221%82:1%8265%8271%;2=1%@3=41p0B1pQDG1").
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
Lemma signed_of_Z : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "H'3'1&;&?&@+2+QO%3221%511r1%8221&=%1235%<231'2&HyR0&Fr2%2231%5241%73E13p091pQHG1").
Proof.
intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Ltac signed_lits_in H :=
repeat match type of H with
| context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_of_Z z) in H by lia
end.
Lemma mod64_land63 : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel ";'3'2&>r1+R0%3221&:+QO%2251%83941pQF:1").
Proof. intros. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land63_idem : ltac2:(TCodec.tc2 tcn__CJ_Lib_SFModel "9'3'2&:r1+QO%3221%4212%63712pQF81").
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
Ltac zs_idioms ::= zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H.
