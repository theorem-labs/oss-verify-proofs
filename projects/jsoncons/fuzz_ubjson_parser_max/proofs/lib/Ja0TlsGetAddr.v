(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Ja0MemIsZero Ja0RegionPoisoned Ja0AsanMemset Ja0AsanMemcpy Ja0StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0TlsGetAddr () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0TlsGetAddr.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0TlsGetAddr.FPX_1.DTLS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0TlsGetAddr.FPX_1.ICPT."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4store_ok"; "4word_to_le_bytes"; "5bvmap"]; ["0M"; "0M'"; "0M1"; "6wbytes"; "7msteps"; "8ret_ok"; "9keeps_but"; ";M13"; ";MD"; "<tls_res"; ":MD"; "=getr"; "=mkst"; "=rdn"; "=v_lw"; ">keeps_cs"]; ["?mem_grows"; "@loaded_segments"; "Aadd"; "Ale"; "Alt"; "Amodulo"; "Amul"; "Apow"; "Asub"; "0a1v"; "0ctx"; "0d"; "0dtv"; "0ent"; "0fx"; "0key"]; ["0md"; "0mem0"; "0off"; "0r"; "0ra"; "0regs"; "0regs'"; "0ret"; "0rg"; "0rom"; "0s"; "0sp"; "BBV"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"]; ["0t"; "0t1"; "0th"; "0tpv"; "0tsd"; "0x"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Lemma v_lw_small : ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "I'<'8&Q3zr1%3221&Q4&Q7+2+O%3221%5271%;271'9'QNyR0%211&N&QMr2%2251%411%93612p0;1pT>H1").
Proof.
intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma zbv_mod : ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "A'<'9'QNyR0%211&QM&Q5r1&Q7+2+R0%3221%6251%82:1%92;7%>3;21pT>@1").
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. apply Z.mod_mod. lia.
Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; try change (2 ^ 4)%Z with 16%Z; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldq F D z R :=
chain_step; [reflexivity
| eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
| step_simpl; vnorm].
#[local] Ltac mlwq F D z R :=
chain_step; [reflexivity
| eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | apply bytes_le_to_Z_4; unorm; lia]
| step_simpl; vnorm; rewrite v_lw_small by lia].
#[local] Ltac mlbuq F D z R :=
chain_step; [reflexivity
| eapply step_lbu; [exact F | reflexivity | exact D | maddr z; exact R]
| step_simpl; vnorm].
#[local] Ltac peel :=
rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].
Lemma musl_tls_get_addr_run : ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "TM&?y5'QNyR0%211%5241'5y8%611%311p061'<'9&Kr:(QL+:(7%33A21%6251&QMr6%22C1%;3C41r;+4%;3I19%>231%@3H16r<+1%@3N1>%C231r9%F3N21&E%11F'8&Q3z%221J&Q2+@%22M1&Q7+2+R0%3221%:251%<291+8%=21Q5&Q4%12Q76%A231%;2:=%42Q:1%D2A1%E2B5&Q6%12:O%D2Q?1%E21<%I21@%K2H1'3%11QJ%QM11&M&Q1rCr@%QD2R51u8%645421(0&>r>%QJ2R;1%3261%52>1%R53>71rDrA%Q;21Q2%R12RB1%B4A41=%R;3D17rE&Q8%127Q8%R72RH1%H4G41C%RA3J1=rFr?%Q52Q>=%QH221%R>2RO1%O4N51J%RH3Q11D':'D&LvQ>rI+QTf\@%RL3S81RJ/01S8rHrG%8576321r1%:591C43%<3Q=31%S623S1&Q5rB%R=2Q?1%321R8%S42SE1%S=3SE61&F(2%SJ1SK(4%112%433S01%631G@%RL281%RM2@1qS>SN1%O2SO1p0Q11p0Q91p0Q@1p0QG1p0R?1p0R:1p0RA1p0RC1p0RG1p0RM1p0S;1p0S>1p0SE1p0SK1pRLT81pRJT91pS6T:1pS2T;1pT8T<1pRHT=1pS@TE1pSDT@1pQ2TA1pS<TG1").
Proof.
intros regs M rom ret d tpv md off dtv ent H10 H4 H1 Hret Hd Htp Hmd Hoff Hdtv Hent R1 R2 R3 R4.
pose proof (Z.mod_pos_bound (ent + off) (2 ^ 64) ltac:(lia)) as Hm.
eexists. split.
- stepiv (ltac:(oF' 0x125990%Z)) (ltac:(oD' 0x125990%Z)) (Z_to_bv 64 tpv) ltac:(wval).
mldq (ltac:(oF' 0x125994%Z)) (ltac:(oD' 0x125994%Z)) d R1.
mldq (ltac:(oF' 0x125998%Z)) (ltac:(oD' 0x125998%Z)) (tpv - 8)%Z R3.
mldq (ltac:(oF' 0x12599c%Z)) (ltac:(oD' 0x12599c%Z)) (d + 8)%Z R2.
stepiv (ltac:(oF' 0x1259a0%Z)) (ltac:(oD' 0x1259a0%Z)) (Z_to_bv 64 (8 * md)) ltac:(wval).
stepiv (ltac:(oF' 0x1259a4%Z)) (ltac:(oD' 0x1259a4%Z)) (Z_to_bv 64 (dtv + 8 * md)) ltac:(wval).
mldq (ltac:(oF' 0x1259a8%Z)) (ltac:(oD' 0x1259a8%Z)) (dtv + 8 * md)%Z R4.
stepiv (ltac:(oF' 0x1259ac%Z)) (ltac:(oD' 0x1259ac%Z)) (Z_to_bv 64 ((ent + off) mod 2 ^ 64)) ltac:(gres; rwH; unfold v_add; unorm; rewrite zbv_mod; f_equal; lia).
stepret (ltac:(oF' 0x1259b0%Z)) (ltac:(oD' 0x1259b0%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; reflexivity | solve_keeps_but].
Qed.
Section SE.
Local Abbreviation SEC_T_get_current_thread_run := (ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "W0&?y5'QNyR0%211%5241'5y8%611%311p061'<'9&Kr:(QL+2(7%33A21%6251&QMr6%22C1%;3C41r;+4%;3I19%>231%@3H16r<+1%@3N1>%C231r9%F3N21&E%11F&Q3+`PPP0&Q8+@%22K1%5241&Q4&Q7+R0%22N1%42G1'8+S0%=21J%3214z%@21M+L%;2Q71%=2Q01%9241&Q2&Q6+8%221Q0%42Q61%5213%K21B%A2<1%G2>Q:+U0%:2Q<1%Q021G%F241%G2BH'1&=&Q1rDrA%Q621Q5%QJ2R;1u@%746521(6%R63:21pT<R?R:';&QOr1%22RD1%QA2=Q@%Q>221%QE2?3%7221r3r2%211rH%113%RE3RH31p071pT<RO1'3%11RM%S011&M+QWY[0%RJ3S61RH/01S6u1%54Q2?21(0(2%RK2S8RA(4%11S9%43S:31%62>1%S83>81+QWY[4%S73SC1S5/01SCu4%B4Q?L21&>rB%S82SI1%3251%A2I1%SC3I61rC+RH%RK221%S?2T01u8%N4QKQ821%SB2T3QJ%=231%K2Q31%SM3Q341%R?2R>?%RA2QO1%SH2T91%Q64R3Q@19r@%SK2T<1%F2<1%Q42Q<1%T63Q<51+TH%RJ261%T12TB1%Q?4R<QI1Br?%T42TE1%O2E1%Q=2QE1%T?3QE51%S<2:1%S=2D1%S>2O1%S?2Q;1p0QM1pQ4R>1':'D&LvQ>+`[l<%TH3U41TF/01U4rGrF%756R<321rE&C%T72S3SB%TK2U<1%QF2Q<4%43821%>5=RL618%@3S981+:%U63UD1U4%U92S01%U;3UC1O%U;2S2U6%U52UFS>%U>3UF21%U>2S5TL%U@3UH1@&F%UL1UM%R?11%RB32U>1%RC33U21%531S3S<%TC271%TD2:1%TE2>1%TF2C1qS>V21%Q62V31p0Q81p0SH1p0T41p0T61p0T<1p0TE1p0TL1p0U11p0U71p0U>1p0UA1p0UH1p0UN1pT6V;1pRFV<1pT:V=1pS0V>1pT8V?1pT2V@1pS@VH1pSDVC1pQ2VD1pS<VJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 2%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 3%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 4%nat 0%nat).
Variable tpv : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 5%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 6%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 7%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 8%nat 0%nat).
Variable th : ltac:(sec_ty2 constr:(SEC_T_get_current_thread_run) 9%nat 0%nat).
Lemma get_current_thread_run : ltac:(sec_stmt2 constr:(SEC_T_get_current_thread_run) 10%nat 0%nat).
Proof.
intros H2 H4 H1 Hret Ht1 Ht2 Htp Hkey Htsd Hctx Hth Hok HC.
set (M1 := wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)).
destruct (HC M1) as (C1 & C2 & C3 & C4 & C5).
{ intros x Hx. unfold M1. pose proof (u64_range x).
destruct Hx as [Hx|Hx]; [rewrite wbytes_below; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
| rewrite wbytes_above; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
assert (Hra : ret_ok (0x82f98 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
eexists. split.
- stepiv (ltac:(oF' 0x82f8c%Z)) (ltac:(oD' 0x82f8c%Z)) (Z_to_bv 64 (t - 16)) ltac:(wval).
stepsd (ltac:(oF' 0x82f90%Z)) (ltac:(oD' 0x82f90%Z)) (Z_to_bv 64 (t - 8)) ret
ltac:(apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
change (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) with M1.
stepn (ltac:(oF' 0x82f94%Z)) (ltac:(oD' 0x82f94%Z)).
stepn (ltac:(oF' 0x7b60c%Z)) (ltac:(oD' 0x7b60c%Z)).
stepn (ltac:(oF' 0x7b610%Z)) (ltac:(oD' 0x7b610%Z)).
mlbu (ltac:(oF' 0x7b614%Z)) (ltac:(oD' 0x7b614%Z)) (0x13a560 : word) C1.
stepb_ft (ltac:(oF' 0x7b618%Z)) (ltac:(oD' 0x7b618%Z)) ltac:(cond).
mlw (ltac:(oF' 0x7b61c%Z)) (ltac:(oD' 0x7b61c%Z)) (0x13a564 : word) C2.
stepn (ltac:(oF' 0x7b620%Z)) (ltac:(oD' 0x7b620%Z)).
stepiv (ltac:(oF' 0x1275d8%Z)) (ltac:(oD' 0x1275d8%Z)) (Z_to_bv 64 tpv) ltac:(wval).
mldq (ltac:(oF' 0x1275dc%Z)) (ltac:(oD' 0x1275dc%Z)) (tpv - 88)%Z C3.
stepiv (ltac:(oF' 0x1275e0%Z)) (ltac:(oD' 0x1275e0%Z)) (Z_to_bv 64 (key * 2 ^ 32)) ltac:(gres; rwH; rewrite v_lw_small by lia; wval).
stepiv (ltac:(oF' 0x1275e4%Z)) (ltac:(oD' 0x1275e4%Z)) (Z_to_bv 64 (8 * key))
ltac:(gres; rwH; unfold v_srli; imm_norm; unorm; rewrite Z.shiftr_div_pow2 by lia;
replace (key * 2 ^ 32)%Z with (8 * key * 2 ^ 29)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
stepiv (ltac:(oF' 0x1275e8%Z)) (ltac:(oD' 0x1275e8%Z)) (Z_to_bv 64 (tsd + 8 * key)) ltac:(wval).
mldq (ltac:(oF' 0x1275ec%Z)) (ltac:(oD' 0x1275ec%Z)) (tsd + 8 * key)%Z C4.
stepret (ltac:(oF' 0x1275f0%Z)) (ltac:(oD' 0x1275f0%Z)) (0x82f98 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
stepb_ft (ltac:(oF' 0x82f98%Z)) (ltac:(oD' 0x82f98%Z)) ltac:(cond).
mldq (ltac:(oF' 0x82f9c%Z)) (ltac:(oD' 0x82f9c%Z)) (ctx + 152)%Z C5.
stepld (ltac:(oF' 0x82fa0%Z)) (ltac:(oD' 0x82fa0%Z)) ret ltac:(maddr (t - 8)%Z; unfold M1; apply rdn_wbytes_hit8; unorm; lia).
stepiv (ltac:(oF' 0x82fa4%Z)) (ltac:(oD' 0x82fa4%Z)) (Z_to_bv 64 t) ltac:(wval).
stepret (ltac:(oF' 0x82fa8%Z)) (ltac:(oD' 0x82fa8%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.
End SE.
Section DTLS.
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variable ret : word.
Variables t tpv d md F V verb dto blk rec : Z.
Hypothesis Hret : ret_ok ret.
Hypothesis Ht : (0x1000000 <= t - 144)%Z /\ (t < 2 ^ 64)%Z.
Hypothesis Htp : (0 <= tpv < 2 ^ 64)%Z.
Hypothesis Hd : (0 <= d /\ d + 16 <= 2 ^ 64)%Z.
Hypothesis Hmd : (0 <= md < 255)%Z.
Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
Hypothesis Hverb : (0 <= verb < 3)%Z.
Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 (t - 144)) 144%nat = true.
Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < t - 144 \/ t <= bv_unsigned x)%Z -> M' x = M x) ->
rdn ASEGS M' (0x132628 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 F)) /\
rdn ASEGS M' (Z_to_bv 64 (F + 137)) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x132688 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 V)) /\
rdn ASEGS M' (Z_to_bv 64 V) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 verb)) /\
rdn ASEGS M' (0x133440 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dto)) /\
rdn ASEGS M' (Z_to_bv 64 (dto + tpv)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 blk)) /\
rdn ASEGS M' (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) /\
rdn ASEGS M' (Z_to_bv 64 (blk + 16 * md + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 rec)).
Definition M13 (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
(Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret))
(Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
(Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
(Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
(Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
(Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
(Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
(Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
(Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
(Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
(Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
(Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
(Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).
Definition MD (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (M13 rg)
(Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (getr rg 12)))
(Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (getr rg 13)).
Lemma M13_out : ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "Q2&?y5'QNyR0%211%5241';&Q4&QOr1%2271&Q8vR0+T@%3221%8251&Q3%1257%<231'9'5y8%D11%311&Gr3r2%3221v@%113%;3731p0=1pT<L1pSBL1").
Proof.
intros rg x Hx. unfold M13. pose proof (u64_range x).
destruct Hx as [Hx|Hx].
- rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
Lemma MD_out : ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "Q2&?y5'QNyR0%211%5241';&Q4&QOr1%2271&Q8vR0+T@%3221%8251&Q3%1257%<231'9'5y8%D11%311&Hr3r2%3221v@%113%;3731p0=1pT<L1pSBL1").
Proof.
intros rg x Hx. unfold MD. pose proof (u64_range x). rewrite <- (M13_out rg x Hx).
destruct Hx as [Hx|Hx].
- rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
#[local] Ltac sok := first [apply (store_ok_mono _ _ M); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|];
apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 144)) _ 144%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]].
#[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
Section SE.
Local Abbreviation SEC_T_dtls_fast_run := (ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "RJ&?y5'QNyR0%211%5241'9&Kr2(QL+:(7%33;21%6251&QMvQ;%22=1%;3=41r3+;%;3C19%>231%@3B1>r4+2%@3H1>%C231vR0%>2I1%G3I31r5+4%G3O1E%J231vR3%E2Q01%N3Q031r6+1%N3Q61L%Q1231vQG%Q43Q621':'8'D&Q1&LvQ>r8+bQeL%Q:3Q@1Q8/01Q@v@vQI%8576321r1&H%119%<5;3B15%?3>51%QF25QAz%QA2QL1%QJ3QL31%QJ29Q8%QL3QN1Q6%QL2;L%QN3R01K&F(2%R51R6(4%112%433QA1%534Q41%731KD%Q1291%Q22<1%Q32?1%Q42D1qS>R<1%Q72R=1p0Q91p0Q@1p0QH1p0R01p0R61pRDRD1pS<RD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_dtls_fast_run) 0%nat 0%nat).
Variable a1v : ltac:(sec_ty2 constr:(SEC_T_dtls_fast_run) 1%nat 0%nat).
Lemma dtls_fast_run : ltac:(sec_stmt2 constr:(SEC_T_dtls_fast_run) 2%nat 0%nat).
Proof.
intros H10 H11 H2 H4 H1.
destruct (HC (M13 regs) (M13_out regs)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
destruct (HC (MD regs) (MD_out regs)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
unfold MD, M13 in *.
eexists. split.
- stepiv (ltac:(oF' 0x906bc%Z)) (ltac:(oD' 0x906bc%Z)) (Z_to_bv 64 (t - 144)) ltac:(wval).
stepsd (ltac:(oF' 0x906c0%Z)) (ltac:(oD' 0x906c0%Z)) (Z_to_bv 64 (t - 8)) ret ltac:(sok).
stepsd (ltac:(oF' 0x906c4%Z)) (ltac:(oD' 0x906c4%Z)) (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
stepsd (ltac:(oF' 0x906c8%Z)) (ltac:(oD' 0x906c8%Z)) (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
stepsd (ltac:(oF' 0x906cc%Z)) (ltac:(oD' 0x906cc%Z)) (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
stepsd (ltac:(oF' 0x906d0%Z)) (ltac:(oD' 0x906d0%Z)) (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
stepsd (ltac:(oF' 0x906d4%Z)) (ltac:(oD' 0x906d4%Z)) (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
stepsd (ltac:(oF' 0x906d8%Z)) (ltac:(oD' 0x906d8%Z)) (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
stepsd (ltac:(oF' 0x906dc%Z)) (ltac:(oD' 0x906dc%Z)) (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
stepsd (ltac:(oF' 0x906e0%Z)) (ltac:(oD' 0x906e0%Z)) (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
stepsd (ltac:(oF' 0x906e4%Z)) (ltac:(oD' 0x906e4%Z)) (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
stepsd (ltac:(oF' 0x906e8%Z)) (ltac:(oD' 0x906e8%Z)) (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
stepsd (ltac:(oF' 0x906ec%Z)) (ltac:(oD' 0x906ec%Z)) (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
stepsd (ltac:(oF' 0x906f0%Z)) (ltac:(oD' 0x906f0%Z)) (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).
stepn (ltac:(oF' 0x906f4%Z)) (ltac:(oD' 0x906f4%Z)).
stepn (ltac:(oF' 0x906f8%Z)) (ltac:(oD' 0x906f8%Z)).
mld (ltac:(oF' 0x906fc%Z)) (ltac:(oD' 0x906fc%Z)) (0x132628 : word) C1.
mlbuq (ltac:(oF' 0x90700%Z)) (ltac:(oD' 0x90700%Z)) (F + 137)%Z C2.
stepb_ft (ltac:(oF' 0x90704%Z)) (ltac:(oD' 0x90704%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x90708%Z)) (ltac:(oD' 0x90708%Z)) (Z_to_bv 64 d) ltac:(wval).
stepn (ltac:(oF' 0x9070c%Z)) (ltac:(oD' 0x9070c%Z)).
mld (ltac:(oF' 0x90710%Z)) (ltac:(oD' 0x90710%Z)) (0x132688 : word) C3.
mldq (ltac:(oF' 0x90714%Z)) (ltac:(oD' 0x90714%Z)) d C7.
stepn (ltac:(oF' 0x90718%Z)) (ltac:(oD' 0x90718%Z)).
mlwq (ltac:(oF' 0x9071c%Z)) (ltac:(oD' 0x9071c%Z)) V C4.
mld (ltac:(oF' 0x90720%Z)) (ltac:(oD' 0x90720%Z)) (0x133440 : word) C5.
stepn (ltac:(oF' 0x90724%Z)) (ltac:(oD' 0x90724%Z)).
stepiv (ltac:(oF' 0x90728%Z)) (ltac:(oD' 0x90728%Z)) (Z_to_bv 64 (dto + tpv)) ltac:(wval).
stepb_ft (ltac:(oF' 0x9072c%Z)) (ltac:(oD' 0x9072c%Z)) ltac:(cond).
mldq (ltac:(oF' 0x90730%Z)) (ltac:(oD' 0x90730%Z)) (dto + tpv)%Z C6.
stepn (ltac:(oF' 0x90734%Z)) (ltac:(oD' 0x90734%Z)).
stepfence (ltac:(oF' 0x90738%Z)) (ltac:(oD' 0x90738%Z)).
stepb_ft (ltac:(oF' 0x9073c%Z)) (ltac:(oD' 0x9073c%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x90740%Z)) (ltac:(oD' 0x90740%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x907c4%Z)) (ltac:(oD' 0x907c4%Z)) ltac:(cond).
stepsd (ltac:(oF' 0x907c8%Z)) (ltac:(oD' 0x907c8%Z)) (Z_to_bv 64 (t - 128)) (getr regs 12) ltac:(sok).
stepsd (ltac:(oF' 0x907cc%Z)) (ltac:(oD' 0x907cc%Z)) (Z_to_bv 64 (t - 120)) (getr regs 13) ltac:(sok).
stepn (ltac:(oF' 0x907d0%Z)) (ltac:(oD' 0x907d0%Z)).
stepb_tk (ltac:(oF' 0x907d4%Z)) (ltac:(oD' 0x907d4%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x90884%Z)) (ltac:(oD' 0x90884%Z)) (Z_to_bv 64 blk) ltac:(wval).
stepiv (ltac:(oF' 0x90888%Z)) (ltac:(oD' 0x90888%Z)) (Z_to_bv 64 (16 * md)) ltac:(wval).
stepiv (ltac:(oF' 0x9088c%Z)) (ltac:(oD' 0x9088c%Z)) (Z_to_bv 64 (blk + 16 * md)) ltac:(wval).
mldq (ltac:(oF' 0x90890%Z)) (ltac:(oD' 0x90890%Z)) (blk + 16 * md + 8)%Z E8.
stepb_ft (ltac:(oF' 0x90894%Z)) (ltac:(oD' 0x90894%Z)) ltac:(cond).
stepn (ltac:(oF' 0x90898%Z)) (ltac:(oD' 0x90898%Z)).
stepld (ltac:(oF' 0x9089c%Z)) (ltac:(oD' 0x9089c%Z)) ret ltac:(maddr (t - 8)%Z; slot).
stepld (ltac:(oF' 0x908a0%Z)) (ltac:(oD' 0x908a0%Z)) (getr regs 8) ltac:(maddr (t - 16)%Z; slot).
stepld (ltac:(oF' 0x908a4%Z)) (ltac:(oD' 0x908a4%Z)) (getr regs 9) ltac:(maddr (t - 24)%Z; slot).
stepld (ltac:(oF' 0x908a8%Z)) (ltac:(oD' 0x908a8%Z)) (getr regs 18) ltac:(maddr (t - 32)%Z; slot).
stepld (ltac:(oF' 0x908ac%Z)) (ltac:(oD' 0x908ac%Z)) (getr regs 19) ltac:(maddr (t - 40)%Z; slot).
stepld (ltac:(oF' 0x908b0%Z)) (ltac:(oD' 0x908b0%Z)) (getr regs 20) ltac:(maddr (t - 48)%Z; slot).
stepld (ltac:(oF' 0x908b4%Z)) (ltac:(oD' 0x908b4%Z)) (getr regs 21) ltac:(maddr (t - 56)%Z; slot).
stepld (ltac:(oF' 0x908b8%Z)) (ltac:(oD' 0x908b8%Z)) (getr regs 22) ltac:(maddr (t - 64)%Z; slot).
stepld (ltac:(oF' 0x908bc%Z)) (ltac:(oD' 0x908bc%Z)) (getr regs 23) ltac:(maddr (t - 72)%Z; slot).
stepld (ltac:(oF' 0x908c0%Z)) (ltac:(oD' 0x908c0%Z)) (getr regs 24) ltac:(maddr (t - 80)%Z; slot).
stepld (ltac:(oF' 0x908c4%Z)) (ltac:(oD' 0x908c4%Z)) (getr regs 25) ltac:(maddr (t - 88)%Z; slot).
stepld (ltac:(oF' 0x908c8%Z)) (ltac:(oD' 0x908c8%Z)) (getr regs 26) ltac:(maddr (t - 96)%Z; slot).
stepld (ltac:(oF' 0x908cc%Z)) (ltac:(oD' 0x908cc%Z)) (getr regs 27) ltac:(maddr (t - 104)%Z; slot).
stepiv (ltac:(oF' 0x908d0%Z)) (ltac:(oD' 0x908d0%Z)) (Z_to_bv 64 t) ltac:(wval).
stepret (ltac:(oF' 0x908d4%Z)) (ltac:(oD' 0x908d4%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; rwH; reflexivity|].
match goal with |- keeps_but _ _ ?rg =>
assert (KD : keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv regs rg) by solve_keeps_but end.
intros r Hr HL.
destruct (decide (r = 8%bv)) as [->|N8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|N9]; [gres; reflexivity|].
destruct (decide (r = 18%bv)) as [->|N18]; [gres; reflexivity|]. destruct (decide (r = 19%bv)) as [->|N19]; [gres; reflexivity|].
destruct (decide (r = 20%bv)) as [->|N20]; [gres; reflexivity|]. destruct (decide (r = 21%bv)) as [->|N21]; [gres; reflexivity|].
destruct (decide (r = 22%bv)) as [->|N22]; [gres; reflexivity|]. destruct (decide (r = 23%bv)) as [->|N23]; [gres; reflexivity|].
destruct (decide (r = 24%bv)) as [->|N24]; [gres; reflexivity|]. destruct (decide (r = 25%bv)) as [->|N25]; [gres; reflexivity|].
destruct (decide (r = 26%bv)) as [->|N26]; [gres; reflexivity|]. destruct (decide (r = 27%bv)) as [->|N27]; [gres; reflexivity|].
apply KD; [exact Hr|]. cbv. cbv in HL. intuition congruence.
Qed.
End SE.
End DTLS.
Section ICPT.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables s tpv d md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis Hret : ret_ok ra.
Hypothesis Hs : (0x1000000 <= s - 176)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 176)) 176%nat = true.
Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
Hypothesis Hd : (0 <= d /\ d + 16 <= 2 ^ 64)%Z.
Hypothesis Hmd : (0 <= md < 255)%Z.
Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
Hypothesis Hverb : (0 <= verb < 3)%Z.
Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
Definition tls_cells (M' : word -> option byte) : Prop :=
rdn ASEGS M' (0x13b9d8 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x134538 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x125990)) /\
rdn ASEGS M' (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) /\
rdn ASEGS M' (Z_to_bv 64 (d + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 off)) /\
rdn ASEGS M' (Z_to_bv 64 (tpv - 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dtv)) /\
rdn ASEGS M' (Z_to_bv 64 (dtv + 8 * md)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ent)) /\
rdn ASEGS M' (0x13a560 : word) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x13a564 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 48)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tb)) /\
rdn ASEGS M' (Z_to_bv 64 (th + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 te)) /\
rdn ASEGS M' (0x132628 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 F)) /\
rdn ASEGS M' (Z_to_bv 64 (F + 137)) 1%nat = Some [Z_to_bv 8 1] /\
rdn ASEGS M' (0x132688 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 V)) /\
rdn ASEGS M' (Z_to_bv 64 V) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 verb)) /\
rdn ASEGS M' (0x133440 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dto)) /\
rdn ASEGS M' (Z_to_bv 64 (dto + tpv)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 blk)) /\
rdn ASEGS M' (Z_to_bv 64 (blk + 16 * md + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 rec)).
Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) -> tls_cells M'.
Definition tls_res : Z := ((ent + off) mod 2 ^ 64)%Z.
Lemma sp_s : ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "9'9'QNyR0%211vQK&QMvQJ%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[local] Ltac oout := intros x Hx; pose proof (u64_range x);
destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
| rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
Lemma MD_grows' : ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "H'QNyR0%211'5y8%511%311p051'<&?y5%2219&Q0r4&Jr3r2r1%445321%7261pSB91pT4=1pS8D1pQ6@1").
Proof. intros. unfold MD, M13. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
#[local] Ltac sok0 := first [apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|first [apply wbytes_grows | apply MD_grows']]); apply mem_grows_refl|];
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 176)) _ 176%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]].
Section SE.
Local Abbreviation SEC_T_tls_icpt_run := (ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "S5&?y5'QNyR0%211%5241'9&Kr1(QL+:(7%33;21%6251&QMvQ;%22=1%;3=41r2+4%;3C19%>231vR3%92D1%B3D31r3+2%B3J1@%E231vQK%H3J21r4+1%H3Q01F%K231vQD%N3Q021':'5y8%Q611%311p0Q61'8'D&Q1&LvQ>r7+]YiL%Q93Q?1Q7/01Q?vQAvQI%8576321%958Q5DQ?2%<3;21%QB2Q7Q=&I%Q=2QH1%QF3QH31%QF2Q;Q2%QH3QJ1Q1%QH2Q=N%QJ3QL1M&O%12BQ@';&Q4&QO%12R3QN&Q8vQJ+U@%3221%7251&Q3%1257%;231%QF1QM%L1QN%R;3Q821p041pT<R?1&Q0%12Q1R=%Q;231%Q<2E1%Q=2H1%Q>2K1%Q?2N1%Q@2Q31qQ4QB1%QH2QC1qS>RI1%QJ2RJ1p0QL1p0R31p0R:1p0RB1pS<RO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_tls_icpt_run) 0%nat 0%nat).
Theorem tls_icpt_run : ltac:(sec_stmt2 constr:(SEC_T_tls_icpt_run) 1%nat 0%nat).
Proof.
intros H10 H4 H2 H1.
rewrite sp_s in H2.
set (M4 := wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))).
set (M6 := wbytes (wbytes M4 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x6a758 : word))) (Z_to_bv 64 (s - 32 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 d))).
set (M7 := wbytes M6 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x6a778 : word))).
assert (O4 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M4 x = mem0 x) by (unfold M4; oout).
assert (O6 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M6 x = mem0 x).
{ intros x Hx. rewrite <- (O4 x Hx). unfold M6. revert x Hx. oout. }
assert (O7 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M7 x = mem0 x).
{ intros x Hx. rewrite <- (O6 x Hx). unfold M7. revert x Hx. oout. }
destruct (HC0 M4 O4) as (A1 & A2 & _).
destruct (HC0 M6 O6) as (B1 & B2 & B3 & B4 & B5 & B6 & _).
assert (Hr1 : ret_ok (0x6a758 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hr2 : ret_ok (0x6a76c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hr3 : ret_ok (0x6a778 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hr4 : ret_ok (0x6a79c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x6a73c : word) mem0 rom) (mkst r1 (0x8078c : word) M4 rom)
/\ (getr r1 8 = Z_to_bv 64 d /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (s - 32) /\ getr r1 1 = (0x6a758 : word)
/\ keeps_but [1; 2; 8; 9; 18]%bv regs r1)).
{ unfold M4. eexists. split.
- stepiv (ltac:(oF' 0x6a73c%Z)) (ltac:(oD' 0x6a73c%Z)) (Z_to_bv 64 (s - 32)) ltac:(wval).
stepsd (ltac:(oF' 0x6a740%Z)) (ltac:(oD' 0x6a740%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(sok0).
stepsd (ltac:(oF' 0x6a744%Z)) (ltac:(oD' 0x6a744%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok0).
stepsd (ltac:(oF' 0x6a748%Z)) (ltac:(oD' 0x6a748%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok0).
stepsd (ltac:(oF' 0x6a74c%Z)) (ltac:(oD' 0x6a74c%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok0).
stepiv (ltac:(oF' 0x6a750%Z)) (ltac:(oD' 0x6a750%Z)) (Z_to_bv 64 d) ltac:(wval).
stepn (ltac:(oF' 0x6a754%Z)) (ltac:(oD' 0x6a754%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q8 & Q4 & Q2 & Q1 & K1).
destruct (tryinit_fast_run r1 M4 rom (0x6a758 : word) (s - 32) Q2 Q1 Hr1 ltac:(lia) ltac:(lia)
ltac:(unfold M4; replace (s - 32 - 16)%Z with (s - 48)%Z by lia; sok0) A1) as (r2 & RUN2 & U10 & U2 & U8 & U1 & K2).
rewrite Q8 in RUN2. change (wbytes (wbytes M4 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x6a758 : word))) (Z_to_bv 64 (s - 32 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 d))) with M6 in RUN2.
rewrite Q8 in U8.
assert (U4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q4).
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x6a758 : word) M6 rom) (mkst r3 (0x125990 : word) M6 rom)
/\ (getr r3 10 = Z_to_bv 64 d /\ getr r3 4 = Z_to_bv 64 tpv /\ getr r3 18 = Z_to_bv 64 1 /\ getr r3 8 = Z_to_bv 64 d
/\ getr r3 2 = Z_to_bv 64 (s - 32) /\ getr r3 1 = (0x6a76c : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3)).
{ eexists. split.
- stepn (ltac:(oF' 0x6a758%Z)) (ltac:(oD' 0x6a758%Z)).
mld (ltac:(oF' 0x6a75c%Z)) (ltac:(oD' 0x6a75c%Z)) (0x134538 : word) B2.
stepiv (ltac:(oF' 0x6a760%Z)) (ltac:(oD' 0x6a760%Z)) (Z_to_bv 64 1) ltac:(wval).
stepiv (ltac:(oF' 0x6a764%Z)) (ltac:(oD' 0x6a764%Z)) (Z_to_bv 64 d) ltac:(wval).
stepjr (ltac:(oF' 0x6a768%Z)) (ltac:(oD' 0x6a768%Z)) (Z_to_bv 64 0x125990) ltac:(gres; reflexivity).
vnorm. apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S3 as (r3 & RUN3 & V10 & V4 & V18 & V8 & V2 & V1 & K3).
destruct (musl_tls_get_addr_run r3 M6 rom (0x6a76c : word) d tpv md off dtv ent V10 V4 V1 Hr2 Hd ltac:(lia) ltac:(lia) Hoff Hdtv Hent B3 B4 B5 B6)
as (r4 & RUN4 & W10 & K4).
assert (W18 : getr r4 18 = Z_to_bv 64 1) by (rewrite (K4 18%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V18).
assert (W8 : getr r4 8 = Z_to_bv 64 d) by (rewrite (K4 8%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V8).
assert (W2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V2).
assert (W4 : getr r4 4 = Z_to_bv 64 tpv) by (rewrite (K4 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V4).
pose proof (Z.mod_pos_bound (ent + off) (2 ^ 64) ltac:(lia)) as Hres.
unfold tls_res. remember ((ent + off) mod 2 ^ 64)%Z as tres eqn:Htres.
assert (S5 : exists r5, msteps ASEGS (mkst r4 (0x6a76c : word) M6 rom) (mkst r5 (0x82f8c : word) M6 rom)
/\ (getr r5 9 = Z_to_bv 64 tres /\ getr r5 4 = Z_to_bv 64 tpv /\ getr r5 8 = Z_to_bv 64 d
/\ getr r5 2 = Z_to_bv 64 (s - 32) /\ getr r5 1 = (0x6a778 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r4 r5)).
{ eexists. split.
- stepiv (ltac:(oF' 0x6a76c%Z)) (ltac:(oD' 0x6a76c%Z)) (Z_to_bv 64 tres) ltac:(wval).
stepb_ft (ltac:(oF' 0x6a770%Z)) (ltac:(oD' 0x6a770%Z)) ltac:(cond).
stepn (ltac:(oF' 0x6a774%Z)) (ltac:(oD' 0x6a774%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S5 as (r5 & RUN5 & X9 & X4 & X8 & X2 & X1 & K5).
destruct (get_current_thread_run r5 M6 rom (0x6a778 : word) (s - 32) tpv key tsd ctx th X2 X4 X1 Hr3 ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
ltac:(unfold M6, M4; replace (s - 32 - 16)%Z with (s - 48)%Z by lia; sok0)) as (r6 & RUN6 & Y10 & Y2 & Y1 & K6).
{ intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x).
{ intros x Hx. rewrite (HM' x) by lia. apply O6. exact Hx. }
destruct (HC0 M' O') as (_ & _ & _ & _ & _ & _ & C7 & C8 & C9 & C10 & C11 & _). repeat split; assumption. }
change (wbytes M6 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x6a778 : word))) with M7 in RUN6.
assert (Y9 : getr r6 9 = Z_to_bv 64 tres) by (rewrite (K6 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X9).
assert (Y8 : getr r6 8 = Z_to_bv 64 d) by (rewrite (K6 8%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X8).
assert (Y4 : getr r6 4 = Z_to_bv 64 tpv) by (rewrite (K6 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X4).
destruct (HC0 M7 O7) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D12 & D13 & _).
assert (S7 : exists r7, msteps ASEGS (mkst r6 (0x6a778 : word) M7 rom) (mkst r7 (0x906bc : word) M7 rom)
/\ (getr r7 10 = Z_to_bv 64 d /\ getr r7 11 = Z_to_bv 64 tres /\ getr r7 2 = Z_to_bv 64 (s - 32) /\ getr r7 4 = Z_to_bv 64 tpv
/\ getr r7 1 = (0x6a79c : word) /\ getr r7 9 = Z_to_bv 64 tres /\ keeps_but [1; 2; 8; 9; 18]%bv r6 r7)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x6a778%Z)) (ltac:(oD' 0x6a778%Z)) ltac:(cond).
mldq (ltac:(oF' 0x6a77c%Z)) (ltac:(oD' 0x6a77c%Z)) (th + 48)%Z D12.
mldq (ltac:(oF' 0x6a780%Z)) (ltac:(oD' 0x6a780%Z)) (th + 56)%Z D13.
stepn (ltac:(oF' 0x6a784%Z)) (ltac:(oD' 0x6a784%Z)).
stepiv (ltac:(oF' 0x6a790%Z)) (ltac:(oD' 0x6a790%Z)) (Z_to_bv 64 d) ltac:(wval).
stepiv (ltac:(oF' 0x6a794%Z)) (ltac:(oD' 0x6a794%Z)) (Z_to_bv 64 tres) ltac:(wval).
stepn (ltac:(oF' 0x6a798%Z)) (ltac:(oD' 0x6a798%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S7 as (r7 & RUN7 & Z10 & Z11 & Z2 & Z4 & Z1 & Z9 & K7).
destruct (dtls_fast_run M7 rom (0x6a79c : word) (s - 32) tpv d md F V verb dto blk rec Hr4 ltac:(lia) ltac:(lia) Hd Hmd HF HV Hverb Hdto Hblk Hrec
ltac:(unfold M7, M6, M4; replace (s - 32 - 144)%Z with (s - 176)%Z by lia; sok0)
ltac:(intros M' HM'; assert (O' : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x)
by (intros x Hx; rewrite (HM' x) by lia; apply O7; exact Hx);
destruct (HC0 M' O') as (_ & _ & E3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E14 & E15 & E16 & E17 & E18 & E19 & E20);
repeat split; assumption)
r7 (Z_to_bv 64 tres) Z10 Z11 Z2 Z4 Z1) as (r8 & RUN8 & T10 & T2 & T1 & K8).
set (M8 := MD M7 (0x6a79c : word) (s - 32) r7) in RUN8.
assert (O8 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M8 x = mem0 x).
{ intros x Hx. unfold M8. rewrite MD_out by lia. apply O7. exact Hx. }
assert (T9 : getr r8 9 = Z_to_bv 64 tres) by (rewrite (K8 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Z9).
assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18)%Z ->
rdn ASEGS M8 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
{ intros k v Hk.
assert (Hk' : (8 <= k <= 32)%Z) by lia.
rewrite (rdn_ext ASEGS 8 M8 M4); [| unorm; cbn; lia |].
- unfold M4. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; repeat peel; apply rdn_wbytes_hit8; unorm; lia.
- intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. unfold M8. rewrite MD_out by lia.
unfold M7, M6. pose proof (u64_range x).
rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]. }
#[local] Ltac slv := first [left; split; reflexivity | right; left; split; reflexivity | right; right; left; split; reflexivity | right; right; right; split; reflexivity].
eexists. exists M8. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
stepiv (ltac:(oF' 0x6a79c%Z)) (ltac:(oD' 0x6a79c%Z)) (Z_to_bv 64 tres) ltac:(wval).
stepld (ltac:(oF' 0x6a7a0%Z)) (ltac:(oD' 0x6a7a0%Z)) ra ltac:(maddr (s - 8)%Z; apply SL; slv).
stepld (ltac:(oF' 0x6a7a4%Z)) (ltac:(oD' 0x6a7a4%Z)) (getr regs 8) ltac:(maddr (s - 16)%Z; apply SL; slv).
stepld (ltac:(oF' 0x6a7a8%Z)) (ltac:(oD' 0x6a7a8%Z)) (getr regs 9) ltac:(maddr (s - 24)%Z; apply SL; slv).
stepld (ltac:(oF' 0x6a7ac%Z)) (ltac:(oD' 0x6a7ac%Z)) (getr regs 18) ltac:(maddr (s - 32)%Z; apply SL; slv).
stepiv (ltac:(oF' 0x6a7b0%Z)) (ltac:(oD' 0x6a7b0%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x6a7b4%Z)) (ltac:(oD' 0x6a7b4%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; reflexivity|]. split; [gres; symmetry; apply sp_s|]. split; [gres; reflexivity|].
split.
+ assert (KB : keeps_but [1; 2; 8; 9; 18]%bv regs r8).
{ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [intros r Hr HL; apply K2; [exact Hr | cbv in HL |- *; intuition]|].
eapply keeps_but_trans; [exact K3|]. eapply keeps_but_trans; [intros r Hr HL; apply K4; [exact Hr | cbv in HL |- *; intuition]|].
eapply keeps_but_trans; [exact K5|]. eapply keeps_but_trans; [intros r Hr HL; apply K6; [exact Hr | cbv in HL |- *; intuition]|].
eapply keeps_but_trans; [exact K7|]. intros r Hr HL; apply K8; [exact Hr | cbv in HL |- *; intuition]. }
intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [gres; rewrite H1; reflexivity|].
destruct (decide (r = 2%bv)) as [->|N2]; [gres; rewrite H2; reflexivity|].
destruct (decide (r = 8%bv)) as [->|N8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|N9]; [gres; reflexivity|].
destruct (decide (r = 18%bv)) as [->|N18]; [gres; reflexivity|].
repeat (rewrite getr_other; [| intros ->; first [congruence | cbv in Hr; intuition discriminate]]).
apply KB; [exact Hr|]. cbv. intuition congruence.
+ split; [exact O8|]. unfold M8. eapply mem_grows_trans; [|apply MD_grows'].
unfold M7, M6, M4. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.
End SE.
Corollary wrap_tls_get_addr_run : ltac2:(TCodec.tc2 tcn__Ja0TlsGetAddr "S5&?y5'QNyR0%211%5241'9&Kr1(QL+:(7%33;21%6251&QMvQ;%22=1%;3=41r2+4%;3C19%>231vR3%92D1%B3D31r3+2%B3J1@%E231vQK%H3J21r4+1%H3Q01F%K231vQD%N3Q021':'5y8%Q611%311p0Q61'8'D&Q1&LvQ>r7+\ZdH%Q93Q?1Q7/01Q?vQAvQI%8576321%958Q5DQ?2%<3;21%QB2Q7Q=&I%Q=2QH1%QF3QH31%QF2Q;Q2%QH3QJ1Q1%QH2Q=N%QJ3QL1M&O%12BQ@';&Q4&QO%12R3QN&Q8vQJ+U@%3221%7251&Q3%1257%;231%QF1QM%L1QN%R;3Q821p041pT<R?1&Q0%12Q1R=%Q;231%Q<2E1%Q=2H1%Q>2K1%Q?2N1%Q@2Q31qQ4QB1%QH2QC1qS>RI1%QJ2RJ1p0QL1p0R31p0R:1p0RB1pS<RO1").
Proof.
intros regs H10 H4 H2 H1.
destruct (tls_icpt_run regs H10 H4 H2 H1) as (r' & M' & RUN & REST).
exists r', M'. split; [|exact REST].
eapply msteps_trans; [|exact RUN].
stepn (ltac:(oF' 0x62a98%Z)) (ltac:(oD' 0x62a98%Z)).
apply mst_refl.
Qed.
End ICPT.
End FPX_1.
