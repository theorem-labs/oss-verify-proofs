(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_malloc_fast () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4Segment"; "5sxv"; "6wz"]; ["7CB"; "7cell"; "8le4"; "9rw_cells"; ":ctz32"; ":lowbit"; ";add"; ";div"; ";land"; ";le"; ";leb"; ";lt"; ";modulo"; ";mul"; ";opp"; ";pow"]; [";shiftr"; ";sub"; ";testbit"; "0a"; "0b"; "0bs"; "0c"; "0i"; "0k"; "0m"; "0n"; "0rest"; "0segs"; "<Z_to_bv"; "<bv"; "<bv_swrap"]; ["<bv_unsigned"; "<bv_wrap"; "0u"; "0v"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma swrap_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "A'<'9'Q>yR0%211&Q=&Q?yQ0r1%3221%5271&?&>%115%311%>3;51pS:@1").
Proof. intros x. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.
Lemma sxv_testbit_lo' : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "G'<'8&Izr1%3221&K+Q0%2241%8241'9'1&Q2&>r3%211r2%5221%6242%93821p0;1pR@E1pS8F1").
Proof. intros v i.
intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. apply Z.mod_pow2_bits_low. lia.
Qed.
Lemma sxv_cases' : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "Q1'<&Lr1&O+2+Q0%3221%6251';'8&K+O%9281%32;1'9&>r2%211%43B1@%:261&I%129C&Q1&F+R0%F2E1%32H1%521E%>3L;1%D281%F2;1tS6OH1pS8Q01").
Proof. intros v.
cbv zeta. pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
rewrite <- (sxv_congr (v mod 2^32) v) by (apply Z.mod_mod; lia).
destruct (sxv_cases (v mod 2^32) ltac:(lia)); tauto.
Qed.
Lemma testbit_31_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "B'<'9'1&Q2r1+O%3221&J&O+2%2215&L+Q0%5241%32:1%8251%?3>:1pS8A1").
Proof. intros v.
rewrite <- (Z.mod_pow2_bits_low v 32 31) by lia. rewrite Z.testbit_eqb by lia.
pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
destruct (Z.leb_spec (2^31) (v mod 2^32)).
- replace (v mod 2^32 / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
- rewrite Z.div_small by lia. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_sxv_testbit_hi := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "G'<'8&I+Or1%3221&K+R0%2241%8241'9'1&Q2&>r3%211r2%5221%624?%93821p0;1pR@E1pS8F1")) (only parsing).
Variable v : ltac:(sec_ty2 constr:(SEC_T_sxv_testbit_hi) 0%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_sxv_testbit_hi) 1%nat 0%nat).
Lemma sxv_testbit_hi : ltac:(sec_stmt2 constr:(SEC_T_sxv_testbit_hi) 2%nat 0%nat).
Proof.
intros Hi. rewrite testbit_31_mod32. rewrite Z.testbit_eqb by lia.
assert (P31 : 2^31 <= 2^i) by (apply Z.pow_le_mono_r; lia).
assert (P63 : 2^i <= 2^63) by (apply Z.pow_le_mono_r; lia).
assert (E64 : 2^64 = 2^(64-i) * 2^i) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (E2 : 2^(64-i) = 2 * 2^(64-i-1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
assert (P1 : 1 <= 2^(64-i-1)) by (apply Z.pow_le_mono_r with (b:=0) in Hi || idtac; apply (Z.pow_le_mono_r 2 0); lia).
destruct (sxv_cases' v) as [[Hu E]|[Hu E]]; rewrite E.
- rewrite Z.div_small by lia. cbn. symmetry. apply Z.leb_gt. lia.
- pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
replace ((v mod 2^32 + 2^64 - 2^32) / 2^i) with (2^(64-i) - 1) by (Z.div_mod_to_equations; nia).
rewrite E2. replace (2 * 2^(64-i-1) - 1) with (1 + (2^(64-i-1) - 1) * 2) by lia.
rewrite Z.mod_add by lia. cbn. symmetry. apply Z.leb_le. lia.
Qed.
End SE.
Lemma sxv_testbit_high : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "B'<&I+R0r1%3221'9'1&Q2&>r3%211r2%5221(3%93821p0;1pR@@1pS8A1").
Proof. intros v i.
intros. pose proof (sxv_range v). destruct (Z.eq_dec (sxv v) 0) as [->|]. apply Z.bits_0.
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.
Lemma sxv_land : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast ">'<'9&H&>r2%211r1%411%6231%7253%711%:3;31pR:<1pR8=1").
Proof. intros a b.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 32); [| destruct (Z.lt_ge_cases i 64)].
- rewrite !sxv_testbit_lo' by lia. symmetry. apply Z.land_spec.
- rewrite !sxv_testbit_hi by lia. rewrite Z.land_spec. reflexivity.
- rewrite !sxv_testbit_high by lia. reflexivity.
Qed.
Lemma sxv_idem : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "8'<'9&>r1%211%311%53612pS871").
Proof. intros v. apply sxv_congr. apply sxv_mod32. Qed.
Lemma land_opp_odd : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "?'<'9&H&F&M+2r1%3221+1%6221&N%112%:231%<3=15pR8>1").
Proof. intros a.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
destruct (Z.eq_dec n 0) as [->|].
- rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
- replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.
Lemma land_opp_even : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "?'<'9&H&M+2r1%3221&N%112%7231%315%9261%9281%<3=41pR8>1").
Proof. intros a.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
destruct (Z.eq_dec n 0) as [->|].
- rewrite !Z.testbit_even_0. reflexivity.
- replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.
Lemma lowbit_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "J'<&Kzr1%3221':'8&I%1265'9&Hr3&N%112%4231&O+2%221>%93B41%<228%>221%?2=1qRBF1%B2G1p0D1pRDI1").
Proof.
intros m Hm.
pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
intros x IH Hx0 Hx.
destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
- destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
- exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.
Lemma land_opp_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "A'<&Izr1%3221'9&H&O+2r2%3221&N%112%7231%93>14p0;1pRB@1").
Proof. intros k.
intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.
Lemma lowbit_nonzero : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "H'<&Kzr1%3221':'8&I%1265'9&Er3%211&O+2%221<%73@41%:226%<221%=2;1qRBD1%@2E1p0B1pRDG1").
Proof. intros m. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.
Lemma lowbit_0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "6'9'<&Ez%211%53412").
Proof. reflexivity. Qed.
Lemma ctz32_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "?'<&Izr1%3221'9&D&O+2r2%3221%511%73<13p091pRB>1").
Proof. intros k. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.
Lemma negw_and_lowbit : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "Q:'<'8&Izr1%3221&K&O+2+Q0%3221%5271%;271'9'Q>yR0%211&Q=&H&Q@&Q?yQ0&Q1&?&>r2%211%411%92=1%72J1%:291%>2@1%=2A1%?215%A2C1&E%11;%=11%?11%J3G51p0L1pS8Q91").
Proof. intros v.
intros Hv. rewrite swrap_word. rewrite !wz_unsigned by apply sxv_range.
rewrite sxv_land. unfold lowbit, wz. f_equal.
rewrite (Z.land_comm v (- v)).
transitivity (sxv (Z.land (sxv (0 - sxv v)) (sxv v))); [rewrite sxv_land, sxv_idem; reflexivity|].
transitivity (sxv (Z.land (sxv (- v)) (sxv v))); [| rewrite sxv_land, sxv_idem; reflexivity].
f_equal. f_equal. apply sxv_congr.
rewrite <- Zminus_mod_idemp_r, sxv_mod32, Zminus_mod_idemp_r. replace (0 - v) with (- v) by lia. reflexivity.
Qed.
Lemma lowbit_pow2_id : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "?'<&Izr1%3221'9&E&O+2r2%3221%511%73<12p091pRB>1").
Proof. intros k. intros. unfold lowbit. apply land_opp_pow2. assumption. Qed.
Lemma mulw_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "J'<'9'Q>yR0%211&Q=&Q?yQ0&M&Q@&?&>r2%211%411%62<1r1%9221%<2;1%>2@1%<284%:11%<11%F3C41pR>H1pR8I1").
Proof. intros a c.
rewrite wz_unsigned by apply sxv_range. rewrite swrap_word. unfold wz. f_equal. apply sxv_congr.
rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
Lemma srliw27_val : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "M'<'9&Q?yQ0&Q0&QA&Q@yR0&?&>r1%211%411%7261%92;1+K%<221%?2>1&G&L&O+2+Q0%3221%52>1%524:%8221%J3K:1pR8L1").
Proof. intros a.
rewrite wz_unsigned by apply sxv_range.
change (bv_wrap 32 (sxv a)) with ((sxv a) mod 2^32). rewrite sxv_mod32.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.
Lemma le4_avail_sub : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "Q9'<'8&Izr1%3221r2%5231%7231&Kr3&O+2+Q0%3221%6251'9'5'Q>y8%211%411&B&?&>&Q1r4%311%41B%4221%611%811%:11%827G%;11%=11%D3?41p0F1p0N1pR:Q71pR8Q81").
Proof. intros a b.
intros. apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
rewrite sxv_mod32, <- Zminus_mod_idemp_r, sxv_mod32, <- Zminus_mod_idemp_l, sxv_mod32, Zminus_mod_idemp_l, Zminus_mod_idemp_r.
reflexivity.
Qed.
Lemma srliw27_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "Q2'<'9'Q>yR0%211&Q=&Q?yQ0&Q0&QA&Q@&?&>r1%211%411%62=1%82:1+K%;221%>2=1%@2B1&G&L&O+2+Q0%3221%52?1%524;%8221%D11%O3L;1pR8Q11").
Proof. intros a. rewrite srliw27_val. reflexivity. Qed.
End CEIL_WRAP_1.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma rw_cells_CB_len : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_malloc_fast "Q7'5'=%211'Q>yR0%211'7y8%511%311p051'<'6%=15'A%?11&Cr6r5r4(2(@r3r2%3221r1%63<21%;4:981'9&4%12F8%33C1<p051pRHB1pR<E1pRFG1p2I1pRDK1pRJQ41").
Proof. intros segs m A n bs rest. intros [[[H _] _] _]. exact H. Qed.
End CEIL_WRAP_2.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.
