(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem ArtRuns JatCls JatFp JatCARSpec JatDepotA JatDepot JatAllocate3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatInvMallocFp () := ([""; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInvMallocFp."; "Stdlib.ZArith.BinInt.Z."], [["1and"; "1eq"; "1not"; "1or"; "2Z"; "0HI"; "3apart"; "4art_malloc_coarse"; "4art_malloc_fp"; "4art_malloc_fp_lin"; "0S"; "5add"; "5le"; "5lt"; "5mul"; "5pow"]; ["5sub"; "0a"; "0ab"; "0blk"; "0c"; "0c0"; "0km"; "0l2"; "0n"; "0qr"; "0qs"; "0qz"; "0ris"; "0rs"; "0rz"; "0spb"]; ["0sz"; "0t"; "0w"; "0w0"; "0x"; "0y"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition art_malloc_fp (S t spb ris qs c km ab rz n rs l2 blk : Z) (x : Z) : Prop :=
(S - 4096 <= x < S) \/ art_alloc3_fp (S - 2144) t spb ris qs c km ab rz n rs l2 blk x.
Definition art_malloc_fp_lin (S t spb qs c km w qz qr n l2 blk : Z) (x : Z) : Prop :=
let rb := spb + c * 2 ^ 32 in let shb := 2147450880 + 8192 * qs + c * 2 ^ 29 in
(S - 4096 <= x < S)
\/ (t + 208 + 80 * c <= x < t + 208 + 80 * c + 80) \/ (exists c', 1 <= c' <= 31 /\ t + 208 + 80 * c' + 4 <= x < t + 208 + 80 * c' + 16)
\/ (t + 2784 <= x < t + 2824) \/ (t + 2872 <= x < t + 2888) \/ (t + 2912 + 8 * c <= x < t + 2920 + 8 * c)
\/ (spb + 2 ^ 37 + 128 * c <= x < spb + 2 ^ 37 + 128 * c + 128)
\/ (rb + 262144 * km <= x < rb + 262144 * km + 262144) \/ (rb + 3758096384 <= x < rb + 4294967296)
\/ (rb + 16 * w <= x < rb + 16 * w + 16 * qz + n)
\/ (shb + 32768 * km <= x < shb + 32768 * km + 32768) \/ (shb + 469762048 <= x < shb + 536870912)
\/ (shb + 2 * w + 2 * qz <= x < shb + 2 * w + 2 * qz + qr)
\/ (0x20cbc8 <= x < 0x65cbe8) \/ (l2 <= x < l2 + 2 ^ 20) \/ (blk <= x < blk + 2 ^ 23).
Section SE.
Local Abbreviation SEC_T_art_malloc_fp_cases := (ltac2:(TCodec.tc2 tcn__JatInvMallocFp "R7'4'1r?&>+RPP0r=%3221%63751&;r@&?+2+Q5%3221%6251%>3?=1r<rAr>+Q0%:291%B231%>251r6+@%F221%B241%J3K;1%I245%L3M=1r;+8%M219%Q03Q131&8rFrErDrCrBr:%7>65432HQ0Q7GQ4I;1B&9rGr9r8r7%5=4<;98N732MOA1p071p0@1p0E1p0H1p0Q51p0Q>1pR:QF1pQDQG1pQHQH1pR6QI1pQ8QJ1pQ@QK1pQLQL1pQBQM1pQNQN1pQ6QO1pQ>R01pQ:R11pQFR21pQJR31pR0R41pR4R51pFR61")) (only parsing).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 0%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 1%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 2%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 3%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 5%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 6%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 7%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 8%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 9%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 10%nat 0%nat).
Variable l2 : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 11%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 12%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 13%nat 0%nat).
Variable qz : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 14%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 15%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_malloc_fp_cases) 16%nat 0%nat).
Lemma art_malloc_fp_cases : ltac:(sec_stmt2 constr:(SEC_T_art_malloc_fp_cases) 17%nat 0%nat).
Proof.
intros Espb Eris Eab Erz Ers F.
assert (Hub8 : (ab + rz) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz).
{ rewrite Eab, Espb, Erz. replace (65536 * qs + c * 2 ^ 32 + w * 16 + 16 * qz) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
assert (Hqr8 : rs / 8 = qr). { rewrite Ers, Z.mul_comm. apply Z.div_mul. lia. }
unfold art_malloc_fp, art_alloc3_fp in F. rewrite Hub8, Hqr8 in F. unfold art_ca_fp, art_refill_fp, art_pc_hdr_foot, dprivD in F.
unfold art_malloc_fp_lin. cbv zeta.
destruct F as [F|[F|[[F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|F]]|[F|[F|[F|[F|[F|[F|F]]]]]]]]].
1-4: left; lia.
1: right; left; lia.
1: { destruct F as (c' & Hc' & F). right; right; left. exists c'. split; [exact Hc'|lia]. }
1: do 3 right; left; lia.
1: do 6 right; left; lia.
1: do 7 right; left; lia.
1: do 8 right; left; lia.
1: do 10 right; left; lia.
1: do 11 right; left; lia.
1: do 4 right; left; lia.
1: do 3 right; left; lia.
1: do 9 right; left; lia.
1: do 12 right; left; lia.
1: do 3 right; left; lia.
1: do 5 right; left; lia.
1: do 13 right; left; lia.
1: do 14 right; left; lia.
1: do 15 right; lia.
Qed.
End SE.
Definition art_malloc_coarse (HI t spb qs l2 blk : Z) (x : Z) : Prop :=
HI <= x \/ (t + 208 <= x < t + 3160) \/ (spb + 2 ^ 32 <= x < spb + 2 ^ 37 + 4096)
\/ (2147450880 + 8192 * qs + 2 ^ 29 <= x < 2147450880 + 8192 * qs + 2 ^ 34)
\/ (0x20cbc8 <= x < 0x65cbe8) \/ (l2 <= x < l2 + 2 ^ 20) \/ (blk <= x < blk + 2 ^ 23).
Section SE.
Local Abbreviation SEC_T_art_mfp_coarse := (ltac2:(TCodec.tc2 tcn__JatInvMallocFp "RB'4'0&<+1r9%3221+N%5231%7231z%8216&>+XPP0r:%3221+S`PPPP0%>221%?284%@2?5r;%B2;1&;+@r>%=221r=%?241%6231%7219%K21>+2r?%E221%F23:%=221%>21:+^PPPP0%Q3221rF+TP0%C221&@rG%2214%Q:241&9rHrErDrCrBrAr@r<%9=8@765432GOM1Q3&7%17:>B9Q1O3p031p0>1p0F1p0O1p0Q91p0QD1p0Q=1p0Q?1p0QA1p0QH1p0QK1pR:R41pQ8R51pQ@R61pQBR71pQDR81pQHR91pR6R:1pQ>R;1pQ:R<1pQFR=1pR0R>1pR4R?1p<R@1pFRA1")) (only parsing).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 0%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 1%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 2%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 3%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 5%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 6%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 7%nat 0%nat).
Variable qz : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 8%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 9%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 10%nat 0%nat).
Variable l2 : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 11%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 12%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_mfp_coarse) 13%nat 0%nat).
Lemma art_mfp_coarse : ltac:(sec_stmt2 constr:(SEC_T_art_mfp_coarse) 14%nat 0%nat).
Proof.
intros Hc Hkm Hkm' Hw Hqz Hn Hqr Hch Hsh HS F.
unfold art_malloc_fp_lin in F. cbv zeta in F. unfold art_malloc_coarse.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]].
- left; lia.
- right; left; lia.
- destruct F as (c' & Hc' & F). right; left; lia.
- right; left; lia.
- right; left; lia.
- right; left; lia.
- do 2 right; left; lia.
- do 2 right; left; lia.
- do 2 right; left; lia.
- do 2 right; left; lia.
- do 3 right; left; lia.
- do 3 right; left; lia.
- do 3 right; left; lia.
- do 4 right; left; lia.
- do 5 right; left; lia.
- do 6 right; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_mfp_out_class := (ltac2:(TCodec.tc2 tcn__JatInvMallocFp "U;'4'0&<+1r:%3221+N%5231%7231r3%8271%9225%;221&2'1r4r<%33A21%511z%B214&>+XPP0r=%3221+S`PPPP0%H221%I284%J2I5r>%L2;1&;+@rA%=221r@%?241%6231%7219%Q521>+2rB%E221%F23:%=221%>21:+^PPPP0%Q=221rI+TP0%C221&@rJ%2214%QD241+`PQoooPP0%QF214+RPP0rH%Q6221%Q>3QL<1rK&?+Q5%22H1%Q2241%Q321ArM%R2221rN+Q?%92O1%R6231&6%Q;2:I%246J81rO+QoonlP0%K2G1%643N21rG+D%D2Q:1%:43179%;4J276+G%H2Q>1rQ1%?4N21>%@4Q93<;'3rQ3+Q0%O2QE1%R92Q>1%R0241%RN21Q6&=%R3235%22Q91%S3241+QoooPP0+XP0rQ2%RC221%R:241+M%Q=2R31%RG2QL1%R>241%S<21QD%R@224%?2QF1%S@231%RC2GQB+T0%RO21R4%RF231%SD21QL%RH224%G2QN1%SH231%Q0291%Q12G1&9rQ7rQ5rQ4rQ0rL%6=543Q7KQ;2QFQMQO1R5RB%SF11p091p0Q<1p0Q>1p0QC1p0QE1p0QJ1p0QO1p0R31p0R81p0RE1p0RB1p0RG1p0RJ1p0S21p0S;1p0SE1p0T01p0SI1p0SK1p0SM1p0T41p0T71p0T>1p0TC1pR:TL1pQ<TM1pQ8TN1pQ@TO1pQBU01pQDU11pQHU21pR6U31pQ>U41pQ:U51pQFU61pR0U71pR4U81p<U91pFU:1")) (only parsing).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 0%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 1%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 2%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 3%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 5%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 6%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 7%nat 0%nat).
Variable qz : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 8%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 9%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 10%nat 0%nat).
Variable l2 : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 11%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 12%nat 0%nat).
Variable c0 : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 13%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_class) 14%nat 0%nat).
Lemma art_mfp_out_class : ltac:(sec_stmt2 constr:(SEC_T_art_mfp_out_class) 15%nat 0%nat).
Proof.
intros Hc Hc0 Ne Hkm Hkm' Hw Hqz Hn Hqr Hch Hsh HS G1 Espb G4 G6 G2 At_k At_s Al_k Al_s Ab_k Ab_s Hx F.
unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_mfp_out_chunk := (ltac2:(TCodec.tc2 tcn__JatInvMallocFp "U?'4'0&<+1r;%3221+N%5231%7231z%8216&>+XPP0r<%3221+S`PPPP0%>221%?284&;+@r=%:221r7%5221%F219%G2F5+8r>%A221%K291r@%D2<1r?%F271%@231%Q121O+RPP0%Q32H1%D2A;rE%M2L1%Q7231'3%Q02H@%J21<%Q22J6%Q<221%M22?%Q>215%7231rL+TP0%Q2221&@rM%2214%QF241+`PQoooPP0%QH214'1rK%QB2I1%33QN<1rN&?+2+Q5%3221%QB251%QC21BrQ0%R5221rQ1+Q?%:291%R9231&6%QK2:J%246K81rQ2+QoonlP0%L2H1%643O21rJ+D%E2D1%:43179%;4K276+G%I2H1rQ4%?4O21>%@4Q:3<;rQ6+Q0%O2N1%RE261%R?241%RG2R?Q6%RA221%S221A&=%RD23QD%22D1%S7241+QoooPP0+XP0rQ5%S1221%RK241+M%Q?2Q>1%S52F1%RO241%QM2O1%S82RI1%S221RJ%S32CR3%SD221%S<2QFQK%S6271%SG21Q6%SI241%RA2C1&2&9rQ:rQ8rQ7rQ3rO%6=543Q6HQ92QDQKQM1R4R7%811p0:1p0Q:1p0Q<1p0QA1p0QC1p0QH1p0QM1p0R11p0R61p0RD1p0RA1p0RF1p0RI1p0S11p0S:1p0T31p0S@1p0SC1p0SJ1p0T71p0T01p0T21p0T:1p0T<1p0TC1p0TF1pR:TO1pR8U01pR2U11pQ8U21pQ@U31pQBU41pQDU51pQHU61pR6U71pQ>U81pQ:U91pQFU:1pR0U;1pR4U<1p<U=1pFU>1")) (only parsing).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 0%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 1%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 2%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 3%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 5%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 6%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 7%nat 0%nat).
Variable qz : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 8%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 9%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 10%nat 0%nat).
Variable l2 : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 11%nat 0%nat).
Variable blk : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 12%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 13%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 14%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_mfp_out_chunk) 15%nat 0%nat).
Lemma art_mfp_out_chunk : ltac:(sec_stmt2 constr:(SEC_T_art_mfp_out_chunk) 16%nat 0%nat).
Proof.
intros Hc Hkm Hkm' Hw Hwu Hqz Hn Hnr Hfit Hsz Hw0 Hold Hap HS G1 Espb G4 G6 G2 At_k At_s Al_k Al_s Ab_k Ab_s Hx F.
unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.
End SE.
Lemma art_mfp_out_cache : ltac2:(TCodec.tc2 tcn__JatInvMallocFp "U1'4'0&<+1r:%3221+N%5231%7231r3%8271+O%:231%<231&2'1r4r<%33B21%511zr;%D221%E2D2%F24D%G258r@%I271&>+XPP0rA%3221+S`PPPP0%O221&;+@%8216%922;%4221r>%6221%Q7219+2rB%@221%A23?%<221%=21E+^PPPP0%Q?221rI+TP0%B221&@rJ%2214%QF241rH&?+Q5%22B1%K241%L21;%QM219rK+Q?%82H1%R1231+`PQoooPP0rL%R4221+RPP0%Q<21B%QJ3R991rN%Q921HrO%R;221&6%Q=2CL%244M61rQ0+QoonlP0%N2?1%643Q121rQ1+VbTP0%Q221@%:43Q5A1+D%Q02Q@1rQ2%>4Q:21Q9+G%Q42QD1rQ3%B4Q>21Q='3rQ4+V@%R2221+R@%R:21QD%R5231%S621Q?&=+4%R9241%32QC1%S<251%R<27R;%S=21QF%R>29;%82QH1%SA231%B261&9rQ7rQ5rM%4=32FIMQ3Q7Q<Q>1QCQHR6%S;11p071p0K1p0Q01p0Q51p0Q:1p0Q?1p0QC1p0QK1p0QI1p0QM1p0R11p0R61p0R>1p0RF1p0RO1p0S81p0S?1p0SB1p0SD1p0SF1p0SH1p0SL1p0T31p0T91pR:TB1pQ<TC1pQ8TD1pQ@TE1pQBTF1pQDTG1pQHTH1pR6TI1pQ>TJ1pQ:TK1pQFTL1pR0TM1pR4TN1p<TO1pFU01").
Proof.
intros S HI t spb qs c km w qz qr n l2 blk c0 x Hc Hc0 Ne Hw Hqz Hn Hqr Hkm Hkm' Hch Hsh HS G6 G2 G1 Espb G4 G8 At_k At_s At_i Al_t Ab_t Hx F.
unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.
Lemma art_mfp_out_shc : ltac2:(TCodec.tc2 tcn__JatInvMallocFp "T0'4'0&<+1r9%3221+N%5231%7231z%8216&>+XPP0r:%3221+S`PPPP0%>221%?284%@2?5r;%B2;1&;rD+TP0%3221&@rE%2214%J241+`PQoooPP0%L214'1+RPP0rC%G221%43Q3=1rF&?+2+Q5%3221%D251%E21CrH%Q:221rI+Q?%:291%Q>231&6+QoonlP0%J2F1%347M21rA+D%B2A1%743165+G%E2D1%:46198%QJ2QC7&=rB+QPP0%QE21C%4231'3%QH2MF%QI2NI%Q@221%92Q51rG%QC231%R721Q8%8241&2&9rQ1rOrNrMrLrKrJ+QoooPP0+XP0%R;216%R2231+M%QD2QC1%R?291%R6241%R721R6%A=@?>=<;:Q@QBFQIR31%C11p0E1p0O1p0Q51p0Q71p0Q;1p0Q@1p0QE1p0QJ1p0R91p0R51p0R;1p0R>1p0RG1p0S21p0RK1p0RM1p0RO1p0S61p0S91pR<SB1pQ8SC1pQ@SD1pQBSE1pQDSF1pQHSG1pR6SH1pQ>SI1pQ:SJ1pQFSK1pR0SL1pR4SM1p<SN1pFSO1").
Proof.
intros S HI t spb qs c km w qz qr n l2 blk y Hc Hkm Hkm' Hw Hqz Hn Hqr HS G1 Espb G4 G6 G2 At_s Al_s Ab_s Hy Hy' Hyu F.
unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.
Lemma art_mfp_out_stack : ltac2:(TCodec.tc2 tcn__JatInvMallocFp "SM'4'0&<+1r9%3221+N%5231%7231z%8216&>+XPP0r:%3221+S`PPPP0%>221%?284%@2?5r;%B2;1&;+@r>%=221r=%?241%6231%7219%K21>+2r?%E221%F23:%=221%>21:+^PPPP0%Q3221+`PQoooPP0rF%Q6221'1rE+RPP0rD%Q2221%53Q>41rG&?+Q5%22D1%N241+TP0%Q0221rI%QE221rJ+Q?%:2L1%QI231%Q7248rK%QL221rB+D%A2Q31%Q=231rL%R2221+G%F2Q81%QB281rM%R7221rN%R921<&2&@rQ0%221KrC%R?221&=%1235%RC231%911&9rQ1rOrH%4=32@BGMQ2Q41Q;QCQ@Q>%?11p071p0B1p0E1p0K1p0Q21p0Q61p0Q;1p0QK1p0QF1p0QM1p0R11p0R:1p0RD1p0RO1p0RH1p0RJ1p0RL1p0S31p0S61pQ4S?1pQ8S@1pQ@SA1pQBSB1pQDSC1pQHSD1pR6SE1pQ>SF1pQ:SG1pQFSH1pR0SI1pR4SJ1p<SK1pFSL1").
Proof.
intros S HI t spb qs c km w qz qr n l2 blk a Hc Hkm Hkm' Hw Hqz Hn Hqr Hch Hsh G1 Espb G4 G6 G2 G8 Dl2 Dblk Ha Ns F.
unfold art_malloc_fp_lin in F. cbv zeta in F.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.
Lemma art_mfp_out_image : ltac2:(TCodec.tc2 tcn__JatInvMallocFp "RK'4'0&<+1r9%3221+N%5231%7231z%8216r8%:231r:%<251&;rC+TP0%3221&@rD%2214%D241+`PQoooPP0%F214'1&>+RPP0rB%3221%53N>1&6rF+VbTP0%?217%443B81r>%Q3241%Q42;2&=%1247%Q8231&2+RQbn8r?%Q;221+V[bo8%8231%Q?231%711&9rMrKrJrIrHrGrErAr@%:=987654L3Q8Q<Q021%C11p0=1p0F1p0K1p0L1p0O1p0Q;1p0Q61p0Q=1p0Q@1p0QI1p0QL1p0R41p0R01p0R11p0R41pQ4R=1pQ8R>1pQ@R?1pQBR@1pQDRA1pQHRB1pR6RC1pQ>RD1pQ:RE1pQFRF1pR0RG1pR4RH1p<RI1pFRJ1").
Proof.
intros S HI t spb qs c km w qz qr n l2 blk a Hc Hkm Hw Hqz Hn Hqr HS G1 Espb G4 At_i Dl Db Ha Nd F.
unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.
