(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatPoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAllocC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5cell"; "5wr"; "6msteps"; "7art_layout"; "7kHighMemBeg"; "8getr"; "8mkst"]; ["8regupd"; "9loaded_segments"; ":add"; ":div"; ":land"; ":le"; ":lt"; ":modulo"; ":mul"; ":pow"; ":sub"; "0ab"; "0fx"; "0id"; "0n"; "0regs"]; ["0rom"; "0rz"; "0sab"; ";BV"; ";Z_to_bv"; ";bv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_land_m8_48 : ltac2:(TCodec.tc2 tcn__JatAllocC "J'5'2&Ezr1%3221&F&I+2+Q@%3221%5271%;271'3&Dr2+WooooooooH%3221&H&C+8%2261%4212%:3G61p0<1pR>I1").
Proof.
intros x Hx. change 281474976710648 with (Z.shiftl (Z.ones 45) 3).
change 8 with (2 ^ 3). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 3) as [L|G].
- rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
- rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
replace (i - 3 + 3) with i by lia.
destruct (Z.lt_ge_cases i 48) as [L2|G2].
+ replace ((0 <=? i - 3) && (i - 3 <? 45))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
apply Bool.andb_true_r.
+ assert (Tf : Z.testbit x i = false).
{ destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with (m := 48); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite Tf. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_c_big_fn := (ltac2:(TCodec.tc2 tcn__JatAllocC "UN&6y5'Q5yR0%211%5241'0y8%611%311p061'5'3&>r8(Q3+:(1%33A21%6251&Q4r2%22C1%;3C41r9+8%;3I19%>231+1%92J1%B3J31r:+9%B3Q01@%E231r6%@2Q11%I3Q131r;+B%I3Q71G%L231%F2Q7L%O3Q721r<+D%O3Q=1M%Q2231&Br7%22J1%O2Q@1%Q83Q@51r=+E%Q83QF1Q6%Q;231&J%:2KQ<+@%3221%Q92QJ1%QB3QJ61r>+H%QB3R01Q@%QE231z%Q@2R11%QI3R131&E&=%221L&F+RPP0%K2F1&I+2+Q?%3221%7251&G%12CG%R73R81@'2%?2JQ0+RP0%A2Q21%4231r@%D2R11+Q8%@2?1%D241%:241r?%J2M1+Q0%F2E1%J241%@241%O2R96+X0%N281%D231&:&ArFrDrB%QN221%QF21QD%74651QE&<rG%211&9rH+QoooPP0&C%12=RO%R9231u1%75A621>';&?vLrJ+ZWl@%SB3SN1S@/01SNrI%756521?&@%SG3T5S:SE+ZXTL%SI3T51SG/01T5%53;41rE%RL2J1%SI2T:1%934SL1+;%T13T?1SO&H%12JSI%SO2T@1%?3641+<%T73TE1T5%B331RC+F%T:3TH1T8%E3317+_X_0%T=3TI1T;/01TI&8u8%S72DT7%342N1QE%Q55Q4851Q=%Q73QIO1p0Q91p0QB1p0QF1p0QO1p0R41p0R;1p0RG1p0RC1p0RI1p0RM1p0S61p0S:1p0SB1p0SM1p0T71p0T>1p0TF1p0TN1pR6U;1pQLU<1pR4U=1pQNU>1pQHU?1pR2UA1p@UB1pR0UH1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_c_big_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_c_big_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_c_big_fn) 2%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_c_big_fn) 3%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_c_big_fn) 4%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_c_big_fn) 5%nat 0%nat).
Variable id : ltac:(sec_ty2 constr:(SEC_T_art_alloc_c_big_fn) 6%nat 0%nat).
Variable sab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_c_big_fn) 7%nat 0%nat).
Lemma art_alloc_c_big_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_c_big_fn) 8%nat 0%nat).
Proof using Type regs M rom ab n rz id sab.
intros H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab.
unfold kHighMemBeg in *.
pose proof L as (G48 & Csb & _).
stepn (ltac:(oF' 0x51f90%Z)) (ltac:(oD' 0x51f90%Z)). rwH. rewrite art_zb_slli by lia.
stepn (ltac:(oF' 0x51f94%Z)) (ltac:(oD' 0x51f94%Z)). rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
stepn (ltac:(oF' 0x51f98%Z)) (ltac:(oD' 0x51f98%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
zsd (ltac:(oF' 0x51f9c%Z)) (ltac:(oD' 0x51f9c%Z)) (ab + rz - 16 + 8) id ltac:(rewok W).
zbft (ltac:(oF' 0x51fa0%Z)) (ltac:(oD' 0x51fa0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (G48' : cellA X 0x132638 8 0x13acf8) by (recell G48);
assert (Csb' : cellA X 0x13acf8 8 SB) by (recell Csb);
assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
zstep (ltac:(oF' 0x51fa4%Z)) (ltac:(oD' 0x51fa4%Z)). zld (ltac:(oF' 0x51fa8%Z)) (ltac:(oD' 0x51fa8%Z)) 0x132638 G48'. zld (ltac:(oF' 0x51fac%Z)) (ltac:(oD' 0x51fac%Z)) 0x13acf8 Csb'. unfold SB.
stepn (ltac:(oF' 0x51fb0%Z)) (ltac:(oD' 0x51fb0%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
zstep (ltac:(oF' 0x51fb4%Z)) (ltac:(oD' 0x51fb4%Z)).
zlbu (ltac:(oF' 0x51fb8%Z)) (ltac:(oD' 0x51fb8%Z)) (2147450880 + ab / 8) Csab'.
zbtk (ltac:(oF' 0x51fbc%Z)) (ltac:(oD' 0x51fbc%Z)).
zstep (ltac:(oF' 0x5207c%Z)) (ltac:(oD' 0x5207c%Z)). zstep (ltac:(oF' 0x52080%Z)) (ltac:(oD' 0x52080%Z)).
stepn (ltac:(oF' 0x52084%Z)) (ltac:(oD' 0x52084%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
zbft (ltac:(oF' 0x52088%Z)) (ltac:(oD' 0x52088%Z)).
zstep (ltac:(oF' 0x5208c%Z)) (ltac:(oD' 0x5208c%Z)). zstep (ltac:(oF' 0x52090%Z)) (ltac:(oD' 0x52090%Z)). zstep (ltac:(oF' 0x52094%Z)) (ltac:(oD' 0x52094%Z)).
stepn (ltac:(oF' 0x52098%Z)) (ltac:(oD' 0x52098%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_alloc_c_small_fn : ltac2:(TCodec.tc2 tcn__JatAllocC "UD&6y5'Q5yR0%211%5241'0y8%611%311p061'5'3&>r8(Q3+:(1%33A21%6251&Q4r2%22C1%;3C41r9+8%;3I19%>231+1%92J1%B3J31r:+9%B3Q01@%E231r6%@2Q11%I3Q131r;+B%I3Q71G%L231%F2Q7L%O3Q721r<+D%O3Q=1M%Q2231&Br7%22J1%O2Q@1%Q83Q@51r=+E%Q83QF1Q6%Q;231&J%:2KQ<+@%3221%Q92QJ1%QB3QJ61r>+H%QB3R01Q@%QE231z%Q@2R11%QI3R131&E&=%221L&F+RPP0%K2F1&I+2+Q?%3221%7251&G%12CG%R73R81@'2%?2JQ0+RP0%A2Q21%4231r@%D2QN1%B22R2%8221r?%H2K1+Q0%D2C1%H241%>241%M2R76+X0%L281%B231&:&ArFrDrB%QL221%QD21QB%74651QC&<rG%211&9rH+QoooPP0&C%12=RM%R7231u1%75A621>';&?vLrJ+ZWl@%S@3SL1S>/01SLrI%756521?&@+WooooooooH%SA2T21%339SD1+;%SI3T71SG%D2IS@%SF2T71%83531+F%SN3T<1SL%;331R:+ZXTL%T13T=1SO/01T=&8u8rE%S52Q51%RM21SM%544F1Q=%M5L:71Q5%O3QAG1p0Q11p0Q:1p0Q>1p0QG1p0QL1p0R31p0R=1p0R91p0R?1p0RC1p0RL1p0S01p0S81p0SC1p0SM1p0T41p0T<1p0TD1pR6U11pQLU21pR4U31pQNU41pQHU51pR2U71p@U81pR0U>1").
Proof.
intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
pose proof L as (G48 & Csb & _).
stepn (ltac:(oF' 0x51f90%Z)) (ltac:(oD' 0x51f90%Z)). rwH. rewrite art_zb_slli by lia.
stepn (ltac:(oF' 0x51f94%Z)) (ltac:(oD' 0x51f94%Z)). rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
stepn (ltac:(oF' 0x51f98%Z)) (ltac:(oD' 0x51f98%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
zsd (ltac:(oF' 0x51f9c%Z)) (ltac:(oD' 0x51f9c%Z)) (ab + rz - 16 + 8) id ltac:(rewok W).
zbft (ltac:(oF' 0x51fa0%Z)) (ltac:(oD' 0x51fa0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (G48' : cellA X 0x132638 8 0x13acf8) by (recell G48);
assert (Csb' : cellA X 0x13acf8 8 SB) by (recell Csb);
assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
zstep (ltac:(oF' 0x51fa4%Z)) (ltac:(oD' 0x51fa4%Z)). zld (ltac:(oF' 0x51fa8%Z)) (ltac:(oD' 0x51fa8%Z)) 0x132638 G48'. zld (ltac:(oF' 0x51fac%Z)) (ltac:(oD' 0x51fac%Z)) 0x13acf8 Csb'. unfold SB.
stepn (ltac:(oF' 0x51fb0%Z)) (ltac:(oD' 0x51fb0%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
zstep (ltac:(oF' 0x51fb4%Z)) (ltac:(oD' 0x51fb4%Z)).
zlbu (ltac:(oF' 0x51fb8%Z)) (ltac:(oD' 0x51fb8%Z)) (2147450880 + ab / 8) Csab'.
zbtk (ltac:(oF' 0x51fbc%Z)) (ltac:(oD' 0x51fbc%Z)).
zstep (ltac:(oF' 0x5207c%Z)) (ltac:(oD' 0x5207c%Z)). zstep (ltac:(oF' 0x52080%Z)) (ltac:(oD' 0x52080%Z)).
stepn (ltac:(oF' 0x52084%Z)) (ltac:(oD' 0x52084%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia. rewrite (Z.div_small n 8) by lia.
zbtk (ltac:(oF' 0x52088%Z)) (ltac:(oD' 0x52088%Z)).
zret.
Qed.
#[using="Type"] Lemma art_alloc_d1_none : ltac2:(TCodec.tc2 tcn__JatAllocC "R;&6y5'Q5yR0%211%5241'0y8%611%311p061'5'3&>r4(Q3+9(1%33A21%6251&Q4r1%22C1%;3C41r5+F%;3I19%>231&H&Cr2+8%3221%5212%>2O1%G3O81'2&Ezr3%3221&F&I+2+Q8%3221%5271%;271&G%12Q3B%Q63Q71<';&A&?vLr8+ZXTL%Q:3QF1Q8/01QFr7r6%8576321+ZXY@%Q@3QL1Q>/01QL%<5;:165%?3>51p0A1p0E1p0Q21p0Q?1pQNQL1pR2QN1p@QO1pR0R51").
Proof.
intros regs M rom n H9 H22 Hn Hn8.
zbtk (ltac:(oF' 0x5209c%Z)) (ltac:(oD' 0x5209c%Z)). apply mst_refl.
Qed.
Section SE.
Local Abbreviation SEC_T_art_alloc_d1_part_fn := (ltac2:(TCodec.tc2 tcn__JatAllocC "V0&6y5'Q5yR0%211%5241'0y8%611%311p061'5'3&>r6(Q3+9(1%33A21%6251&Q4r2%22C1%;3C41r7+D%;3I19%>231&Br4%2219%;2L1%D3L51r8+F%D3Q21B%G231&H&C+8%22;1%4212%F2Q71%O3Q771&E&=%221Q0&F+RPP0%E2I1&I+2+Q?%3221%7251&G+@%22H1z%Q?3Q@21'2%A25Q5+RP0%C2Q71%4231+1r:%G221+Q8%C2B1%G241%;241&4r;%C21Q3%QO3R01A%411r<%QB215%Q321O&<r@%211&9&ArA+QWQWH+RE%QL221u1%756521I&:rB+QoooPP0r>%R32>1r?%QK21QJ%QM21QK%R7241%QN21QM%R9281%;4B:1Q5';&?vLrD+ZXTL%RM3S91RK/01S9rC%756521C&@%S23S@Q@S0+ZXU4%S43S@1S2/01S@%53;41+:%S83SF1S6%RL2Q3H%RC2Q8RB%RE21RC%RO231%RF21RE%S12Q01%S:2SK1%?3:81+;%SB3T01S@%R;2QARK%S?2T01%D3531+<%SG3T51SE%SC2T4;%H3421+=%SK3T91SI+_oooooooO%SH2T91%M3531+>%T03T>1SN&J+R0%S02RO1%321RB%T02TA1%Q53861+?%T83TF1T6%T42TERN%Q93421%T;3TIS2T9+`PQoonooO%T82TI1%Q=3431+A%T@3TN1T>+SooooooooO%T=2TN1%QB3531%T?2U0Q8%QD32T11+ZXY@%TG3U31TE/01U3&8%14R@QKQ<Q7%R25R1631R>%R43RGQL1p0R61p0RC1p0RL1p0S01p0S41p0S:1p0SG1p0SC1p0SI1p0SO1p0T81p0T<1p0TH1p0U21pR4U?1pQNU@1pQHUA1pR2UC1p@UD1pR0UJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_part_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_part_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_part_fn) 2%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_part_fn) 3%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_part_fn) 4%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_part_fn) 5%nat 0%nat).
Lemma art_alloc_d1_part_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_d1_part_fn) 6%nat 0%nat).
Proof using Type regs M rom ab n rz.
intros H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hn8 Hprim L Cpp Wsh.
unfold kHighMemBeg in *.
pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
zbft (ltac:(oF' 0x5209c%Z)) (ltac:(oD' 0x5209c%Z)).
stepn (ltac:(oF' 0x520a0%Z)) (ltac:(oD' 0x520a0%Z)).
zcall (art_can_poison_fn _ _ _ _).
zbft (ltac:(oF' 0x520a4%Z)) (ltac:(oD' 0x520a4%Z)).
zstep (ltac:(oF' 0x520a8%Z)) (ltac:(oD' 0x520a8%Z)). zld (ltac:(oF' 0x520ac%Z)) (ltac:(oD' 0x520ac%Z)) 0x132638 G48. zld (ltac:(oF' 0x520b0%Z)) (ltac:(oD' 0x520b0%Z)) 0x13acf8 Csb. unfold SB.
zstep (ltac:(oF' 0x520b4%Z)) (ltac:(oD' 0x520b4%Z)). zstep (ltac:(oF' 0x520b8%Z)) (ltac:(oD' 0x520b8%Z)). zstep (ltac:(oF' 0x520bc%Z)) (ltac:(oD' 0x520bc%Z)). zstep (ltac:(oF' 0x520c0%Z)) (ltac:(oD' 0x520c0%Z)). zstep (ltac:(oF' 0x520c4%Z)) (ltac:(oD' 0x520c4%Z)).
zbft (ltac:(oF' 0x520c8%Z)) (ltac:(oD' 0x520c8%Z)).
zstep (ltac:(oF' 0x520cc%Z)) (ltac:(oD' 0x520cc%Z)). zld (ltac:(oF' 0x520d0%Z)) (ltac:(oD' 0x520d0%Z)) 0x132640 G50. zstep (ltac:(oF' 0x520d4%Z)) (ltac:(oD' 0x520d4%Z)). zld (ltac:(oF' 0x520d8%Z)) (ltac:(oD' 0x520d8%Z)) 0x132648 G58.
zld (ltac:(oF' 0x520dc%Z)) (ltac:(oD' 0x520dc%Z)) 0x13b9e8 Cmb. zld (ltac:(oF' 0x520e0%Z)) (ltac:(oD' 0x520e0%Z)) 0x13b9f0 Cme.
zstep (ltac:(oF' 0x520e4%Z)) (ltac:(oD' 0x520e4%Z)).
zbtk (ltac:(oF' 0x520e8%Z)) (ltac:(oD' 0x520e8%Z)).
zstep (ltac:(oF' 0x520f0%Z)) (ltac:(oD' 0x520f0%Z)). zld (ltac:(oF' 0x520f4%Z)) (ltac:(oD' 0x520f4%Z)) 0x132650 G60. zld (ltac:(oF' 0x520f8%Z)) (ltac:(oD' 0x520f8%Z)) 0x13b9e0 Che. unfold kHighMemEnd.
zstep (ltac:(oF' 0x520fc%Z)) (ltac:(oD' 0x520fc%Z)). zstep (ltac:(oF' 0x52100%Z)) (ltac:(oD' 0x52100%Z)).
zbft (ltac:(oF' 0x52104%Z)) (ltac:(oD' 0x52104%Z)). zbft (ltac:(oF' 0x52108%Z)) (ltac:(oD' 0x52108%Z)).
zstep (ltac:(oF' 0x5210c%Z)) (ltac:(oD' 0x5210c%Z)). zld (ltac:(oF' 0x52110%Z)) (ltac:(oD' 0x52110%Z)) 0x132630 G40.
zlbu (ltac:(oF' 0x52114%Z)) (ltac:(oD' 0x52114%Z)) (0x1384f8 + 85) Cpp.
stepn (ltac:(oF' 0x52118%Z)) (ltac:(oD' 0x52118%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
zstep (ltac:(oF' 0x5211c%Z)) (ltac:(oD' 0x5211c%Z)). zstep (ltac:(oF' 0x52120%Z)) (ltac:(oD' 0x52120%Z)).
stepn (ltac:(oF' 0x52124%Z)) (ltac:(oD' 0x52124%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
stepn (ltac:(oF' 0x52128%Z)) (ltac:(oD' 0x52128%Z)). rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
zsb (ltac:(oF' 0x5212c%Z)) (ltac:(oD' 0x5212c%Z)) (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
zret.
Qed.
End SE.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
