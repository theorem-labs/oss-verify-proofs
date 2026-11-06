(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocKit_A3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocKit_AB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "3Z"; "0F"; "4sxv"; "5mw_ok"; "6b8"; "6bouncess"; "6meta_word"]; ["6wz"; "7upd"; "8le1"; "9aptr"; "9del_group"; "9g_meta"; "9get_group"; "9ghdr"; "9m_last_idx"; "9m_sizeclass"; "9mask_upto"; "9meta"; "9mstate"; "9optr"; "9put_group"; "9set_bounce"]; ["9set_group_active_idx"; "9span_loop"; ":add"; ":eqb"; ":even"; ":land"; ":le"; ":lor"; ":lt"; ":lxor"; ":modulo"; ":mul"; ":of_nat"; ":opp"; ":pow"; ":shiftr"]; [":sub"; ":to_nat"; "0a"; "0ai"; "0b"; "0c"; "0cnt"; "0gh"; "0i"; "0k"; "0mo"; "0mr"; "0size"; "0span"; "0st"; ";Z_to_bv"]; [";bv"; ";bv_swrap"; ";bv_unsigned"; "0v"; "0w"; "0x"; "0z"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma bounces_set st i v j :
bounces (set_bounce i v st) j = if Z.eqb j i then v else bounces st j.
Proof.
unfold bounces, set_bounce, upd_ctx. cbn [ctx s_ctx c_bounces set_bounces_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma bouncess_set : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "Q3'L'9'7&Q6zr2%3221&Q8+Q0%2241%8241'8'3'R0y8%211%411&>&Or3r4%332@1%511&A%714&QA%117&=%11G%64>531%C3>81p0E1pT8O1pSBQ01pSNQ21").
Proof. intros st i v.
intros Hi. unfold bouncess.
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (bounces st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite bounces_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.
Lemma sextw_sxv0 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "D'9'8'R0yR0%211&QO&R1yQ0&Q2&;r1%211z%5221%8271%:2<1&@%116%A3>31pT8C1").
Proof. intros v. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
Lemma sextw_sxv1 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "A'9'8'R0yR0%211&QO&R1yQ0&;r1%211%5241%7291&@%114%>3;31pT8@1").
Proof. intros v. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.
Lemma addiw_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "Q>'9'7&Q6zr2%3221&Q8&Q>+2+O%3221%5271%;271&Q=%114&Q2r3%221=%@241%=229%C221'8'R0yR0%211&QO&R1yQ0&R2r4%5271%3281%A21@%7261%92;1&Q:%E27D+R0%O2N1%4231%?2A1%D3A71p0F1p0O1pS<Q<1pT8Q=1").
Proof. intros v c.
intros Hv Hc. rewrite unsigned_lit by lia. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (v + c))). f_equal.
rewrite swrap32_eq'.
change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
Z.div_mod_to_equations. lia.
Qed.
End CEIL_WRAP_1.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma set_group_ai_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "N'L&C'G'9'8'6%114&Fr4r3%3221(0r2%22;1%:3841&Q0r5%23951&N&E%11;&D%12>6%54?3;1%D3H71p0;1pS8G1pS@I1pS:K1pSNM1").
Proof. intros st b gh ai.
intros Hb. unfold set_group_active_idx, put_group, del_group. rewrite Hb. cbn [s_groups set_groups].
rewrite insert_delete_eq. reflexivity.
Qed.
Lemma put_group_del : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "C'L&C&M'9'8&Nr3r2r1&Dr4%2251%746541%847653%:3>21pS8<1pSF>1pS:@1pSNB1").
Proof. intros st b mo ai. unfold put_group, del_group. cbn [s_groups set_groups]. rewrite insert_delete_eq. reflexivity. Qed.
Lemma meta_word_mod32 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "A'K&<r1%211'8'9&Q:&?r2%211+Q0%5221&H%115%:3931p0<1pSH@1").
Proof. intros mr. intros MW. rewrite <- (meta_word_last_idx mr MW). change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma sxv_inj : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "K'9'7&Q6zr2%3221&Q8&Q>+2+Q0%3221%5271%;271'8&;r4%211r3%411%63C31r5%83E16p031p0;1p0<1pS:I1pS6J1").
Proof. intros a b.
intros Ha Hb E. pose proof (sxv_mod32 a) as Ea. pose proof (sxv_mod32 b) as Eb. rewrite E in Ea. rewrite Ea in Eb.
rewrite !Z.mod_small in Eb by lia. exact Eb.
Qed.
Lemma mask_upto_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "F'9'7&Q6zr1%3221+O%5231%7231&Q8&Jr2%211%42:1&Q>+2+Q0%3221%9261%B261p0<1pSDE1").
Proof. intros k.
intros Hk. unfold mask_upto. split.
- assert (2 ^ 1 <= 2 ^ (k + 1)) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in H. lia.
- assert (2 ^ (k + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma land_mask_31 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "@'9&Q6zr1%3221'8&Q:r2+Q0%3221&Q5+O%2251%83=41p0:1pT<?1").
Proof. intros x. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lxor_range31 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "H'9'7&Q6zr2%3221&Q8&Q>+2+O%3221%5271%;271&Q9r4r3%3221%?2>1%<228%B221p081p091pS:F1pS6G1").
Proof. intros a b.
intros Ha Hb. split; [apply Z.lxor_nonneg; lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
assert (Ha' : Z.log2 a < 31) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
assert (Hb' : Z.log2 b < 31) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; assumption.
Qed.
Lemma meta_word_sc2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "G'K&<r1%211'8'9&Q5&Q?&?r2%211+5%5221+SN%8221&Q;+2&I%119%4231%@3?61p0B1pSHF1").
Proof. intros mr.
intros MW. pose proof (meta_word_sc mr MW) as E. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range mr MW) as WR.
apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, Z.shiftr_spec by lia.
destruct (Z.eq_dec n 0) as [->|NZ].
- rewrite Z.testbit_even_0. replace (Z.testbit 126 0) with false by reflexivity. apply Bool.andb_false_r.
- replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_even_succ by lia.
rewrite <- E. rewrite Z.land_spec, Z.shiftr_spec by lia.
change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia.
replace (Z.succ (n - 1) + 5) with (n - 1 + 6) by lia. reflexivity.
Qed.
Lemma span_loop_bounds : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "E'4'9'7&Q6r3&Q1r4r2r1%443521%7261&Q2&Q<%117%32:1%<261%>261pSJ@1pSLA1pS>B1pFD1").
Proof. intros F.
induction F as [|F IH]; intros; cbn [span_loop]; [lia|].
rewrite Nat2Z.inj_succ. destruct (_ <? _); [|lia]. pose proof (IH (cnt + 1) (span + size) size). lia.
Qed.
Lemma ai_byte_land : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "N'9&Q6zr2%3221'8&Q5&Q:&Q7r4&Q@&Q>+2+R0%3221+Q0%6221%;281r3+O%>221%=241+X0%@221%B215%D3I15p0F1p0G1pT8L1pT:M1").
Proof. intros w v.
intros Hw Hv. apply Z.bits_inj'. intros n Hn.
change 256 with (2^8). change 31 with (Z.ones 5).
rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
replace (2^64 - 32) with (Z.shiftl (2^59 - 1) 5) by reflexivity.
destruct (Z.ltb_spec n 5).
- rewrite Z.shiftl_spec_low by lia. replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia).
replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia). rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_l. reflexivity.
- replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !Bool.andb_false_r. reflexivity.
Qed.
Lemma le1_mod : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "H'9'8'3'R0y8%211%411&B&QOyR0r1%3221%511(2&=&Q:+X0%2271%411(5%11?%83@31%E3@:1pT>G1").
Proof. intros z.
unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.
Lemma land31_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "<'9'7&Q6z&Q5r1+O%3221%6251%7223%9221pT<;1").
Proof. intros x.
split; [apply Z.land_nonneg; right; lia|].
apply Z.ldiff_le; [lia|].
apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
destruct (Z.testbit x n), (Z.testbit 31 n); reflexivity.
Qed.
Lemma swrap32_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "F'9'7&Q6&Q=&Q>+2+O%3221%511r1%8221&Q8%1235%<231'8&R1yQ0r2%3221%53C12p071pT>E1").
Proof. intros z.
intros. rewrite swrap32_eq'.
change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
Z.div_mod_to_equations. lia.
Qed.
Lemma sraiw1_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 "Q4'9'7&Q6zr1%3221&Q8&Q>+2+O%3221%5271%;271'8'R0yR0%211&QO&R1yQ0&Q?&R2&@r2%211%42:1%8271+1%8221%;2:1%=2?1%;284%:11%D3A31p0F1pT8Q31").
Proof. intros v.
intros Hv. rewrite wz_unsigned by lia. rewrite (swrap32_small v) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
rewrite swrap32_small by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
Lemma land1_mod2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 ";'9'8&Q5r1+1%3221&Q:+2%2251%83941pS6:1").
Proof. intros a. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma even_of_land1 : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocKit_A3 ">'9'8'1&Q4r1%211&Q3&Q5+1%2251z%5221%;3:71pS6=1").
Proof. intros a.
rewrite land1_mod2, Zeven.Zeven_odd_bool, Zmod_odd. destruct (Z.odd a); reflexivity.
Qed.
End CEIL_WRAP_2.
