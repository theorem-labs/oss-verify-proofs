(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocKit_B MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocKit_B3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_B3.CEIL_WRAP_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.Z."], [["1cons"; "1list"; "1nil"; "2and"; "2eq"; "2iff"; "3Z"; "4sxv"; "5mw_ok"; "6b8"; "6meta_slot"; "6meta_word"; "6pw"; "6unmap_seqs"; "6usages"; "6wz"]; ["7upd"; "8le1"; "8le4"; "9aptr"; "9c_unmap_seq"; "9conc"; "9get_meta_rec"; "9m_freeable"; "9m_last_idx"; "9m_maplen"; "9m_sizeclass"; "9mctx"; "9meta"; "9mstate"; "9oconc"; "9optr"]; ["9set_active"; "9set_unmap_seq_map"; "9set_usage"; "9upd_ctx"; ":land"; ":ldiff"; ":le"; ":lor"; ":lt"; ":modulo"; ":mul"; ":opp"; ":pow"; ":shiftl"; ":shiftr"; ":sub"]; [":to_nat"; "0a"; "0c"; "0f"; "0i"; "0k"; "0mr"; "0q"; "0sc"; "0st"; ";insert"; "<Z_to_bv"; "<bv"; "<bv_swrap"; "<bv_unsigned"; "=Z_countable"]; [">map_insert"; "?gmap"; "?gmap_partial_alter"; "@eq_dec"; "0v"; "0y"; "0z"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
destruct (Z.eqb_spec i sc); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma usages_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "Q3'M'6'3&Q6zr2%3221&Q8+Q@%2241%8241'4'1'QLyR0%211%411&>&Q2r3r4%332@1%511&@%714&Q@%117&?%11G%64>531%C3>81p0E1pT:O1pSBQ01pSDQ21").
Proof. intros st sc v.
intros Hsc. unfold usages.
replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
intros i Hi. rewrite usage_set_usage.
destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.
Lemma unmap_seq_set st i v j :
unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma unmap_seqs_set : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "QD'M'6'3&Q6zr2%3221&Q8+Q0%2241%8241'4'1'QLy8%211%411&=&Q3'K&Q1&QJ'R1&R3&QO%34H21H&R0&R2%14K54K%34LL41r4r3&Dr1%211%>7Q2Q2:6541%@213qS6B1%D218%F11&@%H1;&Q@%11<&9%11Q8%64O531%Q43O81p0Q61pT:Q@1pS:QA1pSDQC1").
Proof. intros st i v.
intros Hi. unfold unmap_seqs.
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite unmap_seq_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.
Lemma step_seq_eq st :
step_seq st = if c_seq (ctx st) =? 255
then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma record_seq_eq sc st :
record_seq sc st = if sc_in_seq_range sc
then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
else st.
Proof. reflexivity. Qed.
Lemma conc_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "B'M'Kp011&C'4'6&E&Q3r2r3%3221r1%6221%7242%:3921pS@<1pS8>1pSDA1"). Proof. intros st f q. reflexivity. Qed.
Lemma rec_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "B'M'Kp011&C'4'L&F&Q3r2r3%3221r1%6221%7242%:3921pS@<1pS8>1pSDA1"). Proof. intros st f q. reflexivity. Qed.
Lemma pw_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "D'M'Kp011&O'4'QLyR0%211&<&Q3r2r3%3221r1%6221%7242%<3921pS@>1pS8@1pSDC1"). Proof. intros st f q. destruct q; reflexivity. Qed.
Lemma oconc_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "B'M'Kp011&O'4'6&N&Q3r2r3%3221r1%6221%7242%:3921pS@<1pS8>1pSDA1"). Proof. intros st f q. destruct q; reflexivity. Qed.
Lemma conc_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "B'M'6&C'4&E&Q2r3r2r4%43321r1%7221%8242%:3<21pS@<1pT:>1pSB?1pSDA1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma rec_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "C'M'6&C'4'L&F&Q2r3r2r4%43321r1%7221%8242%;3:21pS@=1pT:?1pSB@1pSDB1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma oconc_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "B'M'6&O'4&N&Q2r3r2r4%43321r1%7221%8242%:3<21pS@<1pT:>1pSB?1pSDA1"). Proof. intros st sc v q. destruct q; reflexivity. Qed.
Lemma conc_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "C'M'6&O&C'4&E&Q0r3r2r4%43321r1%7221%8242%:3=21pS@<1pT:>1pSB@1pSDB1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma rec_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "D'M'6&O&C'4'L&F&Q0r3r2r4%43321r1%7221%8242%;3:21pS@=1pT:?1pSBA1pSDC1"). Proof. intros st sc v q. reflexivity. Qed.
Lemma oconc_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "B'M'6&O'4&N&Q0r3r2r4%43321r1%7221%8242%:3<21pS@<1pT:=1pSB?1pSDA1"). Proof. intros st sc v q. destruct q; reflexivity. Qed.
Lemma meta_slot_upd_ctx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "A'M'Kp011&C&:r3r1%3221&Q3r4%2251r2%8221p061pS@;1pS8=1pSD@1"). Proof. intros st f q. intros H; exact H. Qed.
Lemma meta_slot_set_usage : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "B'M'6&C&:r4r1%3221&Q2r3r5%33621r2%9221p071pS@<1pT:>1pSB?1pSDA1"). Proof. intros st sc v q. intros H; exact H. Qed.
Lemma meta_slot_set_active : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "C'M'6&O&C&:r4r1%3221&Q0r3r5%33621r2%9221p071pS@<1pT:>1pSB@1pSDB1"). Proof. intros st sc v q. intros H; exact H. Qed.
End CEIL_WRAP_1.
Ltac ctx_norm H := rewrite ?conc_set_usage, ?rec_set_usage, ?oconc_set_usage, ?conc_set_active, ?rec_set_active, ?oconc_set_active,
?conc_upd_ctx, ?rec_upd_ctx, ?oconc_upd_ctx in H.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Definition mw_ok (mr : meta) : Prop :=
0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.
Lemma meta_word_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "D'L&8r1%211'3&Q6z&;r2%211%5241&Q8&Q<+2+R0%3221%5271%=271p0?1pS>C1").
Proof. intros mr. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
Lemma meta_word_last_idx : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "A'L&8r1%211'4'6&Q4&;r2%211+O%5221&H%115%:3931p0<1pS>@1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_sc : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "D'L&8r1%211'4'6&Q4&Q>&;r2%211+6%5221+QO%8221&J%117%=3<31p0?1pS>C1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia.
replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma meta_word_shr6_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "G'L&8r1%211'3&Q6z&Q>&;r2%211+6%5221%8271&Q8&Q<+2+R0%3221%5271%@271p0B1pS>F1").
Proof. intros mr. intros H. pose proof (meta_word_range mr H). destruct H as (LI & FB & SCR & ML). rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma meta_word_freeable : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "C'L&8r1%211'4'6&Q4&;r2%211+Q0%5221&Q:&G%116%3251%<3;51p0>1pS>B1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^6) with 64. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
Lemma meta_word_maplen : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "A'L&8r1%211'4'6&Q>&;r2%211+<%5221&I%115%:3931p0<1pS>@1").
Proof. intros mr.
intros (LI & FB & SCR & ML).
rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma meta_word_lt4096 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "D'L&8r1%211&5&Q8&;r2%211+TP0%5221'4'6&I%117z%53421%=271p0?1pS>C1").
Proof. intros mr. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
Section SE.
Local Abbreviation SEC_T_negw_word := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "J'6'4'QLyR0%211&QK&QMyQ0&Q?z&QN&?&7r1%211%411%62=1%9281%<2;1%>2@1&Q;%118%:11%<11%G3D51pT<I1")) (only parsing).
Variable y : ltac:(sec_ty2 constr:(SEC_T_negw_word) 0%nat 0%nat).
Lemma negw_word : ltac:(sec_stmt2 constr:(SEC_T_negw_word) 1%nat 0%nat).
Proof.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.
End SE.
Lemma land_neg_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "I'6&Q6zr2%3221'4&Q4r4&Q;&Q<+2r3%3221%511%8271&Q5&Q?+1%2261%42<1%?3D61p0A1p0B1pS<G1pS8H1").
Proof. intros f k.
intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
rewrite <- Z.ldiff_land. reflexivity.
Qed.
Lemma ldiff_le : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 ">'6&Q6zr2%3221&Q5r4r3%3221%8213p061p071pS4<1pS8=1").
Proof. intros f a.
intros Hf Ha.
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.
Lemma land_upper : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "A'6&Q6zr2%3221'3&Q4r4r3%3221%9281%:224%7221p091p0:1pS4?1pS8@1").
Proof. intros f a.
intros Hf Ha. split; [apply Z.land_nonneg; lia|].
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.
Lemma le4_sxv : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "Q1'6'3&Q6zr1%3221&Q8&Q<+2+Q0%3221%5271%;271'4'1'QLy8%211%411&B&QKyR0&7r2%211%5241%711&?%115%:11%A3<41p0C1pT:Q01").
Proof. intros v.
intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
rewrite sxv_mod32. reflexivity.
Qed.
Lemma le1_lit : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "O'6'3&Q6zr1%3221&Q8+X0%2241%8241'4'1'QLy8%211%411&A&QKyR0r2%3221%511(0&9%115(2%11<%53=31%B3=71p0D1pT>N1").
Proof. intros z.
intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma sllw1_word : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "Q3'6'3&Q6zr1%3221&Q8+Q0%2241%8241'4'QLyR0%211&QK&QMyQ0&Q=+1&Q9r2%221>%5241%8271%:2<1&?&7&Q<+2%2219%411%611%F3C81p0H1pS:Q21").
Proof. intros i.
intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.
Lemma lor_sxv_zero : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_B3 "N'6'3&Q6zr2%3221&Q8&Q<+2+Q0%3221%5271%;271&5'4&Q7&7r4%211r3%411%6231%83F1C%8264%:3H1E%<231p0>1p0?1pS4L1pS8M1").
Proof. intros f a.
intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.
End CEIL_WRAP_2.
Ltac unmask64 K :=
try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
