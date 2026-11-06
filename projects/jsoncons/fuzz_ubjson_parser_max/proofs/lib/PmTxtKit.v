(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums L5Defs L5Core L5CoreKit Js0Sums PmSrcSMemmove PmModelFacts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmTxtKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5CoreKit.L5K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1length"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4Z_to_le_bytes"; "4bytes_le_to_Z"; "5bvmap"; "0M"; "0M3"; "0R"]; ["0R3"; "6msteps"; "7CS"; "8defined"; "8ra_ok"; "8u64_at"; "8u8_at"; "8writable"; "9FPState"; "9getr"; "9mkst"; "9seg_rom"; ":mem_grows"; ";loaded_segments"; "<In"; "=add"]; ["=div"; "=le"; "=lt"; "=modulo"; "=mul"; "=of_nat"; "=pow"; "0a"; "0b"; "0bs"; "0dst"; "0fx"; "0i"; "0n"; "0n0"; "0r"]; ["0segs"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0w"]]).
Module PMTK.
Lemma bytes_le_to_Z_cons : ltac2:(TCodec.tc2 tcn__PmTxtKit "H'QBy8%211'2%112'6'9&;(0r2r1%33921%511&O&QC%12>6&Q4%:17+X0%3221%7251%@3?91pRDB1pRBE1").
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
+ rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
+ rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma Z_to_le_bytes_to_Z : ltac2:(TCodec.tc2 tcn__PmTxtKit "?'2'QBy8%211%411'6&:&1r1%2261&;%113%6231%83915pRD:1").
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b) 256) by lia. rewrite Z.add_0_l. exact IH.
Qed.
Section Generic.
Variable segs : list Segment.
Lemma u64_of_defined : ltac2:(TCodec.tc2 tcn__PmTxtKit "Q<'QByR0%211'4y8%511%311p051'9&Q1zr1%3221&Or2+8%3221&Q6+2+R0%3221%<251&Cr4r3%3321:'7'5&Q2%12B9%32B1&EvQ@r6r5%44321H%9261qS:M1%<2N1p0>1p0C1p0M1pR@Q21pLQ41").
Proof. intros M a.
intros Ha Hn D. destruct (PMCP.rdn_of_defined segs M 8%nat a Ha ltac:(cbn; lia) D) as (bs & RD & LEN).
pose proof (bytes_le_to_Z_bound bs) as HB. rewrite LEN in HB. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HB.
pose proof (bytes_le_to_Z_nonneg bs) as H0.
exists (bytes_le_to_Z bs). split; [lia|]. unfold L5.u64_at. rewrite RD. f_equal. unfold word_to_le_bytes.
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia. rewrite <- LEN. symmetry. apply Z_to_le_bytes_to_Z.
Qed.
Lemma u64_low_byte : ltac2:(TCodec.tc2 tcn__PmTxtKit "Q='QByR0%211'4y8%511%311p051'9&EvQ@r4r3r2%544321&Fr5%247164'5&Q1z%221:&Q2&Q6+2+R0%3221%52@1%:271+X0%82C1%=2:1'6&Q3r6%2216%43L1Dp061p0:1p0F1p0J1pRBQ11pS:Q21pR@Q31pLQ51").
Proof. intros M a w b.
intros W B Hw Hb. pose proof (PMF.u8_of_u64 segs M a w Hw W) as B2. unfold L5.u8_at in B, B2. rewrite B in B2. injection B2 as E.
change (bv_unsigned (Z_to_bv 8 b) = bv_unsigned (Z_to_bv 8 (w mod 256))) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 8) with 256 in E.
pose proof (Z.mod_pos_bound w 256 ltac:(lia)) as X. rewrite (Z.mod_small b) in E by lia. rewrite (Z.mod_small (w mod 256)) in E by lia. lia.
Qed.
End Generic.
Lemma short_size : ltac2:(TCodec.tc2 tcn__PmTxtKit "Q7'9'5&Q1zr2%3221&Q2&Q6+2+R0%3221%5271%;271'6&Q3r3+X0%3221&Q4%12;?%73D31%C2B6+F%E281%G231&Q0+RPPPPPPPPPP0r5%:221%?21C+TPPPPPPPPPP0%6221r4%D3Q121p0:1p0?1p0H1pRNQ51pS:Q61").
Proof. intros w n0.
intros Hw Hm Hn.
assert (E : (72057594037927936 * w) mod 2 ^ 64 = 72057594037927936 * (w mod 256)).
{ change (2 ^ 64) with (72057594037927936 * 256). rewrite Z.mul_mod_distr_l by lia. reflexivity. }
rewrite E, Hm. replace (72057594037927936 * (2 * n0)) with (n0 * 144115188075855872) by lia. apply Z.div_mul. lia.
Qed.
#[local] Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Lemma fill_run : ltac2:(TCodec.tc2 tcn__PmTxtKit "T9'H&<y5'QByR0%211%5241'4y8%611%311p061'9'6&Ir5&QA&Q5u:%211%42B1%7261r3%72C1%;3C31r6u<%:11%<2J1%?241%A3I17r7u1%@11%B2Q01%E241%G3O1=&Dr4%211&Q1z%221Ar8%4231&Q2&Or9%2215&Q6+2+QO%3221%8251&G&Mr;r:%44321;'7'5'A&Jr@r?+eUg0%QB2QN1r>&K%11>%8576431r2%QH2R4@r1%<5;3215%>3D51&L%12:4%Q62Q55+R0%O2N1%Q4281%F241&8%Q<2D=%Q72EB%Q92?1%K231%511%QC1R2rA%11R4%R?3RB31p051p0<1pR@RC1&Cr=r<%33J21'3&N&B%233N1%RG1Q1%RI2S71%RL2R41%RM2A2%RO3S721p061pRJ:1%S12Q8RK%S02S<?%S43S<21%QF241%QG2@1%QH2E1%QI2Q81%QJ2Q;1qNS<1%QM2S=1qQ2SC1%QO2SD1p0R11p0R71p0RA1p0RD1p0RH1p0RL1p0S31p0S:1pS0SG1pRLSH1pRFSI1pLSK1pQ0T11pRHT81").
Proof. intros fx R M dst n r.
intros H10 H12 H1 RA Hn Hd Hdn W.
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr R (reg 11)))) (Z.to_nat n)).
assert (LEN : length bs = Z.to_nat n) by (unfold bs; apply repeat_length).
destruct (src0_fill_spec_memset fx M (Z_to_bv 64 dst) (getr R (reg 11)) n R (Z_to_bv 64 r) Hn
ltac:(rewrite L5.unsigned_lit by lia; lia)
ltac:(replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
ltac:(pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as X; change (bv_modulus 64) with (2 ^ 64) in X; unfold AX2.two64; lia)
(L5K.ret_ok_lit r RA) H1 H10 eq_refl H12) as (R3 & MS & KO & A10).
exists R3, (wbytes M (Z_to_bv 64 dst) bs). fold bs in MS. split; [exact MS|]. split; [apply wbytes_grows|].
split. { intros a Ha Hout. apply PMCP.wbytes_out; [lia| rewrite LEN; lia| exact Ha| rewrite LEN, Z2Nat.id by lia; exact Hout]. }
split. { pose proof (PMCP.wbytes_defined M dst bs Hd ltac:(rewrite LEN; lia)) as X. rewrite LEN, Z2Nat.id in X by lia. exact X. }
split; [intros i Hi; apply (L5K.kept_ok_index R R3 i KO Hi)| exact A10].
Qed.
End PMTK.
