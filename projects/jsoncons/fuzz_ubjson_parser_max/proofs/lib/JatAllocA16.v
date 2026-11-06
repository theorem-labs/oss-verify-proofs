(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatRzLog JatAllocA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAllocA16 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocA16."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7art_alloc_rodata"; "8art_alloc_memA1_16"; "9art_tsd"; ":getr"]; [":mkst"; ":regupd"; ";loaded_segments"; "<add"; "<div"; "<land"; "<le"; "<lt"; "<max"; "<mul"; "<pow"; "<sub"; "0ctx"; "0fx"; "0ia"; "0key"]; ["0n"; "0r"; "0raw"; "0regs"; "0rom"; "0rs"; "0rz"; "0sp"; "=BV"; "=Z_to_bv"; "=bv"; "0stk"; "0t"; "0tp"; "0tsd"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_alloc_memA1_16 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
(Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 32).
Lemma art_land_m16 : ltac2:(TCodec.tc2 tcn__JatAllocA16 "J'4'2&Fzr1%3221&G&J+2+R0%3221%5271%;271'3&Er2+_ooooooooooo@%3221&I&D+@%2261%4212%:3G61p0<1pS0I1").
Proof.
intros x Hx. change 18446744073709551600 with (Z.shiftl (Z.ones 60) 4).
change 16 with (2 ^ 4). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 4) as [L|G].
- rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
- rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
replace (i - 4 + 4) with i by lia.
destruct (Z.lt_ge_cases i 64) as [L2|G2].
+ replace ((0 <=? i - 4) && (i - 4 <? 60))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
apply Bool.andb_true_r.
+ assert (Tf : Z.testbit x i = false).
{ destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite Tf. reflexivity.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_a1_16_fn := (ltac2:(TCodec.tc2 tcn__JatAllocA16 "VD&5y5'Q:yR0%211%5241'0y8%611%311p061'4'3&?r8(Q8+1(1%33A21%6251r5%93A21r9+2%93G17%<231&Q9%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;r<+<%J3Q81H%M231+@%B2Q91%Q13Q931r=+=%Q13Q?1O%Q4231r6%I2Q@1%Q83Q@31r>+>%Q83QF1Q6%Q;231%O2QFQ9%Q>3QF21r?+?%Q>3QL1Q<%QA231%QC3QK16&F+X0%221K&G&J+R0%22Q?1%42I1+TP0%921K&C%12F3%9216'2%>2QNQ0%2218%@2R0E+Q8%>2QK1%@2H1%7241&:&BrE&KrB%221I%64541J+VbTP0%C21LrC%O221&<rG%211&9rH+RQTHu1+4%55B4321rI+QW^^H%85E215RKrJ+Qgck2z%<5I3291';&@vMrL+ZVo4%S63SB1S4/01SBrK%756521<&A+ZWR0%S<3SH1S:/01SH%43:S;1+T0%Q72K1%S62SM1%834S91+8%SD3T21SB%;331RH+9%SG3T51SE%>331R>+QA%S?2T61%A33S;1+Q0%SB2T91%D33S91+RQT@%SE2T<1%G33S71%QI2R;S6%SH2T?1%J33S31+B%T63TD1T4%M331S:+E%T93TG1T7rF%T02TG1%Q23531+F%T>3TL1T<%T42TKQM%Q63421+G%TB3U01T@%T82TOR;%Q:3421+I%TF3U41TD%T<2U3S:%Q>3421+J%TJ3U81TH+QoO%S12R:1%TB2U91%QD3641+K%U03U>1TN%QG331SG+ZWSL%U33U?1U1/01U?&=%14QNRAR<R2%R55R4631R:%R73S1QO1p0R91p0R>1p0RB1p0RI1p0RM1p0S21p0S:1p0S@1p0SD1p0SH1p0SK1p0T11p0T51p0T;1p0TB1p0TJ1p0U21p0U81p0U>1p0UF1pRHV11pR2V21pQNV31pR@V41pR6V<1pR:V71p>V81pR8V>1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_16_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_16_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_16_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_16_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_16_fn) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_16_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_16_fn) 6%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_16_fn) 7%nat 0%nat).
Lemma art_alloc_a1_16_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_a1_16_fn) 8%nat 0%nat).
Proof using Type regs M rom raw sp ia n stk.
intros H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & _ & R3) R2 Ci Cr.
zstep (ltac:(oF' 0x51be4%Z)) (ltac:(oD' 0x51be4%Z)).
zsd (ltac:(oF' 0x51be8%Z)) (ltac:(oD' 0x51be8%Z)) (sp - 128 + 120) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x51bec%Z)) (ltac:(oD' 0x51bec%Z)) (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x51bf0%Z)) (ltac:(oD' 0x51bf0%Z)) (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x51bf4%Z)) (ltac:(oD' 0x51bf4%Z)) (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x51bf8%Z)) (ltac:(oD' 0x51bf8%Z)) (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x51bfc%Z)) (ltac:(oD' 0x51bfc%Z)) (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x51c00%Z)) (ltac:(oD' 0x51c00%Z)) (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
zsd (ltac:(oF' 0x51c04%Z)) (ltac:(oD' 0x51c04%Z)) (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
zsd (ltac:(oF' 0x51c08%Z)) (ltac:(oD' 0x51c08%Z)) (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
zsd (ltac:(oF' 0x51c0c%Z)) (ltac:(oD' 0x51c0c%Z)) (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
zsd (ltac:(oF' 0x51c10%Z)) (ltac:(oD' 0x51c10%Z)) (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
zsd (ltac:(oF' 0x51c14%Z)) (ltac:(oD' 0x51c14%Z)) (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
zsd (ltac:(oF' 0x51c18%Z)) (ltac:(oD' 0x51c18%Z)) (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
zstep (ltac:(oF' 0x51c1c%Z)) (ltac:(oD' 0x51c1c%Z)). zstep (ltac:(oF' 0x51c20%Z)) (ltac:(oD' 0x51c20%Z)). zstep (ltac:(oF' 0x51c24%Z)) (ltac:(oD' 0x51c24%Z)). zstep (ltac:(oF' 0x51c28%Z)) (ltac:(oD' 0x51c28%Z)). zstep (ltac:(oF' 0x51c2c%Z)) (ltac:(oD' 0x51c2c%Z)). zstep (ltac:(oF' 0x51c30%Z)) (ltac:(oD' 0x51c30%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
assert (Ci' : cellA Mf 0x13b9d8 1 1) by (unfold Mf; unfold apart in *; recell Ci).
assert (Cr' : cellA Mf 0x1bcf62 1 0) by (unfold Mf; unfold apart in *; recell Cr).
assert (R1' : cellA Mf 0x10418 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
assert (R2' : cellA Mf 0x10498 1 4) by (unfold Mf; unfold apart in *; recell R2).
stepn (ltac:(oF' 0x51c34%Z)) (ltac:(oD' 0x51c34%Z)).
zcall (art_asan_inited_fn _ _ _ _).
zbft (ltac:(oF' 0x51c38%Z)) (ltac:(oD' 0x51c38%Z)).
stepn (ltac:(oF' 0x51c3c%Z)) (ltac:(oD' 0x51c3c%Z)).
zcall (art_rss_limit_fn _ _ _ _).
zbft (ltac:(oF' 0x51c40%Z)) (ltac:(oD' 0x51c40%Z)).
zbft (ltac:(oF' 0x51c44%Z)) (ltac:(oD' 0x51c44%Z)).
zstep (ltac:(oF' 0x51c48%Z)) (ltac:(oD' 0x51c48%Z)).
zbtk (ltac:(oF' 0x51c4c%Z)) (ltac:(oD' 0x51c4c%Z)).
zstep (ltac:(oF' 0x51c88%Z)) (ltac:(oD' 0x51c88%Z)). zstep (ltac:(oF' 0x51c8c%Z)) (ltac:(oD' 0x51c8c%Z)).
zbtk (ltac:(oF' 0x51c90%Z)) (ltac:(oD' 0x51c90%Z)).
zstep (ltac:(oF' 0x51c98%Z)) (ltac:(oD' 0x51c98%Z)). zstep (ltac:(oF' 0x51c9c%Z)) (ltac:(oD' 0x51c9c%Z)).
zbft (ltac:(oF' 0x51ca0%Z)) (ltac:(oD' 0x51ca0%Z)).
zstep (ltac:(oF' 0x51ca4%Z)) (ltac:(oD' 0x51ca4%Z)). zld (ltac:(oF' 0x51ca8%Z)) (ltac:(oD' 0x51ca8%Z)) 0x10418 R1'.
zstep (ltac:(oF' 0x51cac%Z)) (ltac:(oD' 0x51cac%Z)). zstep (ltac:(oF' 0x51cb0%Z)) (ltac:(oD' 0x51cb0%Z)). zstep (ltac:(oF' 0x51cb4%Z)) (ltac:(oD' 0x51cb4%Z)). zstep (ltac:(oF' 0x51cb8%Z)) (ltac:(oD' 0x51cb8%Z)). zstep (ltac:(oF' 0x51cbc%Z)) (ltac:(oD' 0x51cbc%Z)). zstep (ltac:(oF' 0x51cc0%Z)) (ltac:(oD' 0x51cc0%Z)).
zstep (ltac:(oF' 0x51cc4%Z)) (ltac:(oD' 0x51cc4%Z)).
zlbu (ltac:(oF' 0x51cc8%Z)) (ltac:(oD' 0x51cc8%Z)) 0x10498 R2'.
zstep (ltac:(oF' 0x51ccc%Z)) (ltac:(oD' 0x51ccc%Z)). zstep (ltac:(oF' 0x51cd0%Z)) (ltac:(oD' 0x51cd0%Z)). zstep (ltac:(oF' 0x51cd4%Z)) (ltac:(oD' 0x51cd4%Z)). zstep (ltac:(oF' 0x51cd8%Z)) (ltac:(oD' 0x51cd8%Z)).
zbft (ltac:(oF' 0x51cdc%Z)) (ltac:(oD' 0x51cdc%Z)).
zstep (ltac:(oF' 0x51ce0%Z)) (ltac:(oD' 0x51ce0%Z)). zstep (ltac:(oF' 0x51c60%Z)) (ltac:(oD' 0x51c60%Z)). zstep (ltac:(oF' 0x51c64%Z)) (ltac:(oD' 0x51c64%Z)).
zbft (ltac:(oF' 0x51c68%Z)) (ltac:(oD' 0x51c68%Z)).
zstep (ltac:(oF' 0x51c6c%Z)) (ltac:(oD' 0x51c6c%Z)). zstep (ltac:(oF' 0x51c70%Z)) (ltac:(oD' 0x51c70%Z)).
zsd (ltac:(oF' 0x51c74%Z)) (ltac:(oD' 0x51c74%Z)) (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
zsd (ltac:(oF' 0x51c78%Z)) (ltac:(oD' 0x51c78%Z)) (sp - 128 + 16) 32 ltac:(unfold Mf; rewok W).
unfold Mf, art_alloc_memA1_16. zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_alloc_a3_16_fn := (ltac2:(TCodec.tc2 tcn__JatAllocA16 "X;&5y5'Q:yR0%211%5241'0y8%611%311p061'4'3&?r>(Q8+2(1%33A21%6251&Q9r;%22C1%;3C41r?+4%;3I19%>231r6%92J1%B3J31r@+8%B3Q01@%E231+@%@2Q11%I3Q131rA+:%I3Q71G%L231&Hr<%221<%I2Q:1%Q23Q:51rB+B%Q23Q@1Q0%Q5231%Q73Q?1?rC+C%Q73QE1Q5%Q:231r=%Q52QF1%Q>3QF31rD+D%Q>3QL1Q<%QA231+RPP0%Q<2QM1%QE3QM31rE+E%QE3R31QC%QH231%QB2R3Q7%QK3R321rF+F%QK3R91QI%QN231%QH2R9M%R13R921rG+J%R13R?1QO%R4231&C+QoO%22Q01%R12RB1%R:3RB51&F%12QEF&G&J+R0%22R<1%42E1+TP0%821G%>2B2+VbTP0%;221%A22R0rI%>221'2+1rH%B221+Q8%A2RK1%C241%7241z%H217+7%J291%<231&I&DrJ%R<21RF+?%Q6221%521RF%721RG%S?3S@C1%Q22S<7%:2RJ1%SB3SCF1%Q=2:K%Q>21RM%Q:21R2&:&BrQ1&KrO%221S4%64541S5&9rQ2+Sa0%QJ261u8%55;421Q3&>rQ3rK%3621MQ>Q:R4&8%?24SArM+RH%B221%544SE1SHrQ4%E21SGrL%Q92SL7%R;221%;44SK1SNrQ5%K21SM+TH%R@271%@43T01T3';&@vMrQ9+ZW\H%TJ3U61TH/01U6rQ8rQ7%8576321&A%U03U>R8TN+ZWd4%U23U>1U0/01U>%53<41rQ6%U12UB1%833U41%U32UDR@%:32TG1+9%U;3UI1U9%U72UHQ2%>3421%U92UJN%@32TF1+;%UA3UO1U?+V@%S@2Q71%U?2V01%F3641+<%UG3V51UE%SE2QMU4%SF21R4%UE2V61%L3641+=%UM3V;1UK%UI2V:U=%Q03421%Q131TI6%UL2V=R<%Q332TD1+H%V43VB1V2%R?2SHUA%V12VB1%Q83531%V32VDQL%Q:32T81+ZhiL%V;3VG1V9/01VG&7%RH2Q9UM+ZWc8%34RBQD21%QK5QJ851QD%QM3RNQD1p0QO1p0R51p0R<1p0SL1p0RD1p0RI1p0S01p0S81p0S<1p0S@1p0SJ1p0T01p0T91p0T=1p0TA1p0TD1p0TJ1p0TM1p0U71p0U>1p0UE1p0UM1p0V51p0V;1p0VE1p0VM1p0W51pRJWB1pQJWC1pRNWD1pR0WE1pRLWF1pR>WG1pR<WH1pR4WI1pR2WJ1pQNWK1pR@WL1pR:WN1p>WO1pR8X51")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_16_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_16_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_16_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_16_fn) 3%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_16_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_16_fn) 5%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_16_fn) 6%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_16_fn) 7%nat 0%nat).
Lemma art_alloc_a3_16_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_a3_16_fn) 8%nat 0%nat).
Proof using Type regs M rom sp ia n r rs.
intros rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
pose proof TSD as (_ & _ & _ & _ & _ & R).
assert (Hrs16 : exists q16, rs = 16 * q16) by (exists ((Z.max n 8 + 15) / 16); lia). destruct Hrs16 as (q16 & Hrs16).
assert (Hrs8 : (rs + 16) mod 8 = 0) by (rewrite Hrs16; replace (16 * q16 + 16) with ((2 * q16 + 2) * 8) by lia; apply Z_mod_mult).
assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 15) 16 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 15) 16 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
zstep (ltac:(oF' 0x51d98%Z)) (ltac:(oD' 0x51d98%Z)). zstep (ltac:(oF' 0x51d9c%Z)) (ltac:(oD' 0x51d9c%Z)). zstep (ltac:(oF' 0x51da0%Z)) (ltac:(oD' 0x51da0%Z)). zstep (ltac:(oF' 0x51da4%Z)) (ltac:(oD' 0x51da4%Z)). zstep (ltac:(oF' 0x51da8%Z)) (ltac:(oD' 0x51da8%Z)).
stepn (ltac:(oF' 0x51dac%Z)) (ltac:(oD' 0x51dac%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_m16 by lia.
match goal with |- context [Z_to_bv 64 (?e / 16 * 16)] => replace (e / 16 * 16) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
zstep (ltac:(oF' 0x51db0%Z)) (ltac:(oD' 0x51db0%Z)). zstep (ltac:(oF' 0x51db4%Z)) (ltac:(oD' 0x51db4%Z)).
stepn (ltac:(oF' 0x51db8%Z)) (ltac:(oD' 0x51db8%Z)). rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
zbft (ltac:(oF' 0x51dbc%Z)) (ltac:(oD' 0x51dbc%Z)).
zstep (ltac:(oF' 0x51dc0%Z)) (ltac:(oD' 0x51dc0%Z)). zstep (ltac:(oF' 0x51dc4%Z)) (ltac:(oD' 0x51dc4%Z)). zstep (ltac:(oF' 0x51dc8%Z)) (ltac:(oD' 0x51dc8%Z)).
stepn (ltac:(oF' 0x51dcc%Z)) (ltac:(oD' 0x51dcc%Z)). rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
zstep (ltac:(oF' 0x51dd0%Z)) (ltac:(oD' 0x51dd0%Z)). zstep (ltac:(oF' 0x51dd4%Z)) (ltac:(oD' 0x51dd4%Z)). zstep (ltac:(oF' 0x51dd8%Z)) (ltac:(oD' 0x51dd8%Z)). zstep (ltac:(oF' 0x51ddc%Z)) (ltac:(oD' 0x51ddc%Z)). zstep (ltac:(oF' 0x51de0%Z)) (ltac:(oD' 0x51de0%Z)). zstep (ltac:(oF' 0x51de4%Z)) (ltac:(oD' 0x51de4%Z)).
zstep (ltac:(oF' 0x51de8%Z)) (ltac:(oD' 0x51de8%Z)).
stepn (ltac:(oF' 0x51dec%Z)) (ltac:(oD' 0x51dec%Z)). rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
zstep (ltac:(oF' 0x51df0%Z)) (ltac:(oD' 0x51df0%Z)). zstep (ltac:(oF' 0x51df4%Z)) (ltac:(oD' 0x51df4%Z)).
zbft (ltac:(oF' 0x51df8%Z)) (ltac:(oD' 0x51df8%Z)). zbft (ltac:(oF' 0x51dfc%Z)) (ltac:(oD' 0x51dfc%Z)).
zld (ltac:(oF' 0x51e00%Z)) (ltac:(oD' 0x51e00%Z)) (ia + 3616) Cmax.
zbtk (ltac:(oF' 0x51e04%Z)) (ltac:(oD' 0x51e04%Z)).
stepn (ltac:(oF' 0x51e64%Z)) (ltac:(oD' 0x51e64%Z)).
zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
zbft (ltac:(oF' 0x51e6c%Z)) (ltac:(oD' 0x51e6c%Z)) || (zstep (ltac:(oF' 0x51e68%Z)) (ltac:(oD' 0x51e68%Z)); zbft (ltac:(oF' 0x51e6c%Z)) (ltac:(oD' 0x51e6c%Z))).
zstep (ltac:(oF' 0x51e70%Z)) (ltac:(oD' 0x51e70%Z)). zstep (ltac:(oF' 0x51e74%Z)) (ltac:(oD' 0x51e74%Z)). zstep (ltac:(oF' 0x51e78%Z)) (ltac:(oD' 0x51e78%Z)). zstep (ltac:(oF' 0x51e7c%Z)) (ltac:(oD' 0x51e7c%Z)).
stepn (ltac:(oF' 0x51e80%Z)) (ltac:(oD' 0x51e80%Z)).
zret.
Qed.
End SE.
End FPX.
