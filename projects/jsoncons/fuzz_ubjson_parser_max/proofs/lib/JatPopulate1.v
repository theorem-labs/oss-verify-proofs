(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatAllocG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatPopulate1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPopulate1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SeqExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6class_size"; "7msteps"; "8art_tsd"]; ["9art_pop_c_mem"; "9art_pop_frame"; "9art_pop_szw"; ":getr"; ":mkst"; ":regupd"; ":v_srai"; ";v_divu"; "<loaded_segments"; "=In"; ">add"; ">div"; ">land"; ">le"; ">lt"; ">modulo"]; [">mul"; ">pow"; ">sub"; "0au"; "0c"; "0ctx"; "0fx"; "0ia"; "0key"; "0m1"; "0m2"; "0mm"; "0mu"; "0need"; "0new"; "0nf"]; ["0p"; "0r"; "0raw"; "0rb"; "0regs"; "0regs'"; "0rem"; "0req"; "0rom"; "0sp"; "0spb"; "0st"; "?BV"; "?Z_to_bv"; "?bv"; "0sv"]; ["0sz"; "0t"; "0tp"; "0tsd"; "0x"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Definition art_pop_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
(sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22)).
Lemma art_land_m18 : ltac2:(TCodec.tc2 tcn__JatPopulate1 "K'7'4&Mzr1%3221&N&Q1+2+R0%3221%5271%;271'5&Lr2+_oooooooohPP0%3221&Q0&K+B%>2=1%3271%5212%;3H71p0=1pT:J1").
Proof.
intros x Hx. change 18446744073709289472 with (Z.shiftl (Z.ones 46) 18).
rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 18) as [L|G].
- rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
- rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
replace (i - 18 + 18) with i by lia.
destruct (Z.lt_ge_cases i 64) as [L2|G2].
+ replace ((0 <=? i - 18) && (i - 18 <? 46))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
apply Bool.andb_true_r.
+ assert (Tf : Z.testbit x i = false).
{ destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite Tf. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_art_class_size_facts := (ltac2:(TCodec.tc2 tcn__JatPopulate1 "J'7'4&M+1r1%3221+N%5231%7231+Q0&=r2%211%;241+RPP0%=231%?231'5&O+@%2281z%53F21%F271p0@1pR:I1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_class_size_facts) 0%nat 0%nat).
Lemma art_class_size_facts : ltac:(sec_stmt2 constr:(SEC_T_art_class_size_facts) 1%nat 0%nat).
Proof.
intros Hc.
assert (H : forall x, In x (map (fun i => Z.of_nat i) (seq 1 30)) -> 32 <= AsanTab.class_size x <= 65536 /\ AsanTab.class_size x mod 16 = 0).
{ intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [vm_compute; repeat split; discriminate|]). destruct Hx. }
apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
End SE.
Lemma art_class_size_small : ltac2:(TCodec.tc2 tcn__JatPopulate1 "C'7'4&M+1r1%3221+@%5231%7231'5&=r2%211&Q0+Q0%2214%73@41p091pR:B1").
Proof. intros c Hc. unfold AsanTab.class_size. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Definition art_pop_szw (c : Z) : word :=
v_add (v_and (v_srai (Z_to_bv 64 (c * 2 ^ 63)) 63) (v_srli (v_sll (Z_to_bv 64 512) (v_srli (Z_to_bv 64 (c + -16)) 1)) 1)) (v_sll (Z_to_bv 64 512) (v_srli (Z_to_bv 64 (c + -16)) 1)).
Lemma art_pop_szw_ok : ltac2:(TCodec.tc2 tcn__JatPopulate1 "G'7'4&M+Ar1%3221+N%5231%7231'5'QNyR0%211&Br2%211&QM&=%114%3281%;3851p0=1pR:F1").
Proof.
intros c Hc.
assert (E : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
repeat (destruct E as [->|E]; [apply bv_eq; vm_compute; reflexivity|]). subst c. apply bv_eq; vm_compute; reflexivity.
Qed.
Definition art_pop_c_mem (M : word -> option byte) (sp t st r m1 m2 sv mu : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 356308) (sp - 24) 532836) (t + 2872) (m1 + 1)) (t + 2880) (m2 + 262144)) (st + 24) (sv + 262144)) (r + 48) (mu + 262144).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_pop_a1s_fn := (ltac2:(TCodec.tc2 tcn__JatPopulate1 "W=&8y5'QNyR0%211%5241'2y8%611%311p061'7'5&Cr>(QL+1(3%33A21%6251r;%93A21r?+2%93G17%<231&QM%12H7%@3H31r@+:%@3N1>%C231%E3M16rA+;%E3Q31C%H231%J3Q21;rB+<%J3Q81H%M231%O3Q71@rC+=%O3Q=1M%Q2231%Q43Q<1ErD+>%Q43QB1Q2%Q7231%Q93QA1J&M+R0%221F&N&Q1%12Q44%32E1&J+VbTP0%2218%:21Dz%<21F+TP0%72C1%?217'4%A26F%?2G=%3221%D2QJI+@%F2K1%7231%H2@MrE+T0%D221+Q?%I2QL1%K231%O2R56+8%Q1281%B231&Q0&=rH%211rF%5221%RC3RDQH1%Q:2O3rG+Q5%Q92R<1%Q7231%Q<21B%Q@2Q55%QA2<6rI%Q<218%QA2?1+B%QB2RE1%QG2B1rJ+Q0%QF2RI1%QK231&:&Q2rQ3%221QNrO%542R01Q7&<&HrQ7rQ4%921R5%54431R6&;rQ8%R325Au8%459321<rQ9rQ2%R821F%85=315@rQ:+Q@%R<2E1%<5A319D'>&DvQ6rQ<+ZkdD%T13T=1SO/01T=rQ;%756521<&E%Q22FRN%SL2TC1%339SO1%T93TGR2T7%SO2TFN%63321+9%T=3TK1T;rQ6%T42TK1%;3531rQ5%R821QA%T82TO1%?34SO1rQ1%T;2U21%B33SH1%TH3U6QLTF%S;2Q47%T?2U61%F3431+C%TM3U;1TK%S@29QG%TD2U;1%K3531+D%U23U@1U0rQ0%TI2U@1%Q03531+E%U73UE1U5%RM1G%TN2UE1%Q53531+ZkiD%U<3UH1U:/01UH&A%14Q<QOQKQ@%QC5QB631QH%QE3R7Q=1p0QG1p0QL1p0R11p0R71p0R>1p0RE1p0RJ1p0RN1p0S21p0S41p0S61p0S<1p0S>1p0SF1p0SK1p0T21p0T41p0T91p0T>1p0TB1p0TE1p0TJ1p0TO1p0U31p0U91p0U?1p0UE1p0UK1p0V11p0V91pRLVD1pRJVE1pR8VF1pSFVG1pS@VH1pS4VI1pR:VJ1pSHVK1pR@VL1pSDVM1pS6W51pSBW01pDW11pS:W71")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 5%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 7%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 8%nat 0%nat).
Variable req : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 9%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 10%nat 0%nat).
Variable au : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 11%nat 0%nat).
Variable mu : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 12%nat 0%nat).
Variable need : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1s_fn) 13%nat 0%nat).
Lemma art_pop_a1s_fn : ltac:(sec_stmt2 constr:(SEC_T_art_pop_a1s_fn) 14%nat 0%nat).
Proof using Type regs M rom raw sp ia st c r req spb au mu need.
intros H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst Hc Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' Hmu A W Cspb Cau Cmu.
zstep (ltac:(oF' 0x56e94%Z)) (ltac:(oD' 0x56e94%Z)).
zsd (ltac:(oF' 0x56e98%Z)) (ltac:(oD' 0x56e98%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x56e9c%Z)) (ltac:(oD' 0x56e9c%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x56ea0%Z)) (ltac:(oD' 0x56ea0%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x56ea4%Z)) (ltac:(oD' 0x56ea4%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd (ltac:(oF' 0x56ea8%Z)) (ltac:(oD' 0x56ea8%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x56eac%Z)) (ltac:(oD' 0x56eac%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x56eb0%Z)) (ltac:(oD' 0x56eb0%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x56eb4%Z)) (ltac:(oD' 0x56eb4%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W).
fold (art_pop_frame M sp raw regs).
zstep (ltac:(oF' 0x56eb8%Z)) (ltac:(oD' 0x56eb8%Z)). zstep (ltac:(oF' 0x56ebc%Z)) (ltac:(oD' 0x56ebc%Z)).
assert (Cspb' : cellA (art_pop_frame M sp raw regs) (ia + 32) 8 spb) by (unfold art_pop_frame; zcell).
zld (ltac:(oF' 0x56ec0%Z)) (ltac:(oD' 0x56ec0%Z)) (ia + 32) Cspb'.
zstep (ltac:(oF' 0x56ec4%Z)) (ltac:(oD' 0x56ec4%Z)). zstep (ltac:(oF' 0x56ec8%Z)) (ltac:(oD' 0x56ec8%Z)).
zbft (ltac:(oF' 0x56ecc%Z)) (ltac:(oD' 0x56ecc%Z)). zstep (ltac:(oF' 0x56ed0%Z)) (ltac:(oD' 0x56ed0%Z)). zbft (ltac:(oF' 0x56ed4%Z)) (ltac:(oD' 0x56ed4%Z)).
zstep (ltac:(oF' 0x56ed8%Z)) (ltac:(oD' 0x56ed8%Z)).
assert (Cau' : cellA (art_pop_frame M sp raw regs) (r + 32) 8 au) by (unfold art_pop_frame; unfold apart in A; zcell).
assert (Cmu' : cellA (art_pop_frame M sp raw regs) (r + 48) 8 mu) by (unfold art_pop_frame; unfold apart in A; zcell).
zld (ltac:(oF' 0x56edc%Z)) (ltac:(oD' 0x56edc%Z)) (r + 32) Cau'. zld (ltac:(oF' 0x56ee0%Z)) (ltac:(oD' 0x56ee0%Z)) (r + 48) Cmu'.
replace (c * 2 ^ 5) with (AsanTab.class_size c) by (rewrite art_class_size_small by lia; lia).
zstep (ltac:(oF' 0x56ee4%Z)) (ltac:(oD' 0x56ee4%Z)). rewrite <- Eneed. zstep (ltac:(oF' 0x56ee8%Z)) (ltac:(oD' 0x56ee8%Z)). zstep (ltac:(oF' 0x56eec%Z)) (ltac:(oD' 0x56eec%Z)).
zbtk (ltac:(oF' 0x56ef0%Z)) (ltac:(oD' 0x56ef0%Z)).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_pop_a1b_fn := (ltac2:(TCodec.tc2 tcn__JatPopulate1 "WJ&8y5'QNyR0%211%5241'2y8%611%311p061'7'5&Cr>(QL+1(3%33A21%6251r;%93A21r?+2%93G17%<231&QM%12H7%@3H31r@+:%@3N1>%C231%E3M16rA+;%E3Q31C%H231%J3Q21;rB+<%J3Q81H%M231%O3Q71@rC+=%O3Q=1M%Q2231%Q43Q<1ErD+>%Q43QB1Q2%Q7231%Q93QA1J&M+R0%221F&N&Q1%12Q44%32E1&J+VbTP0%2218%:21Dz%<21F+TP0%72C1%?217'4%A26F%?2G=%3221+A%E21J+N%G2L1%8231%I2ANrE+T0%E221+Q?%J2QM1%L231%Q02R66+8%Q2281%C231&Q0&=rH%211rF%5221%RD3REQI1%Q;2Q03rG+Q5%Q:2R=1%Q8231%Q=21B%QA2Q65%QB2<6rI%Q=218%QB2?1+B%QC2RF1%QH2B1rJ+Q0%QG2RJ1%QL231&:&Q2rQ3%221QOrO%542R11Q7&<&HrQ7rQ4%921R6%54431R7&;rQ8%R425Au8%459321<rQ9rQ2%R921F%85=315@rQ:+Q@%R=2E1%<5A319D'>&DvQ6rQ<+ZkdD%T23T>1T0/01T>rQ;%756521<&E%Q22FRO%SM2TD1%339T01%T:3THR2T8%T02TGN%63321+9%T>3TL1T<rQ6%T52TL1%;3531rQ5%R821QA%T92U01%?34T01rQ1%T<2U31%B33SI1+?%TJ3U81TH&F+QO%SB2TE1%RC2<1%TD2U;1%5214%K3971+@%U33UA1U1%N3315%U53UCR8U3%SH2Q@C%TL2UC1%Q23431+C%U:3UH1U8%SM2ER3%U12UH1%Q73531+D%U?3UM1U=rQ0%U62UM1%Q<3531+E%UD3V21UB%S91Q3%U;2V21%QA3531+ZkiD%UI3V51UG/01V5&A%14QHR;R7QL%QO5QN631R4%R13RCQI1p0R31p0R81p0R=1p0RC1p0RJ1p0S11p0S61p0S:1p0S>1p0S@1p0SB1p0SH1p0SJ1p0T21p0T71p0T>1p0T@1p0TF1p0TK1p0TO1p0U21p0U71p0U<1p0U@1p0UF1p0UL1p0V21p0V81p0V>1p0VF1pRLW11pRJW21pR8W31pSFW41pS@W51pS4W61pR:W71pSHW81pR@W91pSDW:1pS6WB1pSBW=1pDW>1pS:WD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 5%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 7%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 8%nat 0%nat).
Variable req : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 9%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 10%nat 0%nat).
Variable au : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 11%nat 0%nat).
Variable mu : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 12%nat 0%nat).
Variable need : ltac:(sec_ty2 constr:(SEC_T_art_pop_a1b_fn) 13%nat 0%nat).
Lemma art_pop_a1b_fn : ltac:(sec_stmt2 constr:(SEC_T_art_pop_a1b_fn) 14%nat 0%nat).
Proof using Type regs M rom raw sp ia st c r req spb au mu need.
intros H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst Hc Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' Hmu A W Cspb Cau Cmu.
zstep (ltac:(oF' 0x56e94%Z)) (ltac:(oD' 0x56e94%Z)).
zsd (ltac:(oF' 0x56e98%Z)) (ltac:(oD' 0x56e98%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x56e9c%Z)) (ltac:(oD' 0x56e9c%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x56ea0%Z)) (ltac:(oD' 0x56ea0%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x56ea4%Z)) (ltac:(oD' 0x56ea4%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd (ltac:(oF' 0x56ea8%Z)) (ltac:(oD' 0x56ea8%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x56eac%Z)) (ltac:(oD' 0x56eac%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x56eb0%Z)) (ltac:(oD' 0x56eb0%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x56eb4%Z)) (ltac:(oD' 0x56eb4%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W).
fold (art_pop_frame M sp raw regs).
zstep (ltac:(oF' 0x56eb8%Z)) (ltac:(oD' 0x56eb8%Z)). zstep (ltac:(oF' 0x56ebc%Z)) (ltac:(oD' 0x56ebc%Z)).
assert (Cspb' : cellA (art_pop_frame M sp raw regs) (ia + 32) 8 spb) by (unfold art_pop_frame; zcell).
zld (ltac:(oF' 0x56ec0%Z)) (ltac:(oD' 0x56ec0%Z)) (ia + 32) Cspb'.
zstep (ltac:(oF' 0x56ec4%Z)) (ltac:(oD' 0x56ec4%Z)). zstep (ltac:(oF' 0x56ec8%Z)) (ltac:(oD' 0x56ec8%Z)).
zbft (ltac:(oF' 0x56ecc%Z)) (ltac:(oD' 0x56ecc%Z)). zstep (ltac:(oF' 0x56ed0%Z)) (ltac:(oD' 0x56ed0%Z)). zbtk (ltac:(oF' 0x56ed4%Z)) (ltac:(oD' 0x56ed4%Z)).
zstep (ltac:(oF' 0x56ef8%Z)) (ltac:(oD' 0x56ef8%Z)). zstep (ltac:(oF' 0x56efc%Z)) (ltac:(oD' 0x56efc%Z)). zstep (ltac:(oF' 0x56f00%Z)) (ltac:(oD' 0x56f00%Z)). zstep (ltac:(oF' 0x56f04%Z)) (ltac:(oD' 0x56f04%Z)). zstep (ltac:(oF' 0x56f08%Z)) (ltac:(oD' 0x56f08%Z)). zstep (ltac:(oF' 0x56f0c%Z)) (ltac:(oD' 0x56f0c%Z)).
zstep (ltac:(oF' 0x56f10%Z)) (ltac:(oD' 0x56f10%Z)). zstep (ltac:(oF' 0x56f14%Z)) (ltac:(oD' 0x56f14%Z)). zstep (ltac:(oF' 0x56f18%Z)) (ltac:(oD' 0x56f18%Z)).
fold (art_pop_szw c). rewrite (art_pop_szw_ok c Hc).
destruct (art_class_size_facts c ltac:(lia)) as [Hsz _].
assert (Cau' : cellA (art_pop_frame M sp raw regs) (r + 32) 8 au) by (unfold art_pop_frame; unfold apart in A; zcell).
assert (Cmu' : cellA (art_pop_frame M sp raw regs) (r + 48) 8 mu) by (unfold art_pop_frame; unfold apart in A; zcell).
zld (ltac:(oF' 0x56f1c%Z)) (ltac:(oD' 0x56f1c%Z)) (r + 32) Cau'. zld (ltac:(oF' 0x56f20%Z)) (ltac:(oD' 0x56f20%Z)) (r + 48) Cmu'.
zstep (ltac:(oF' 0x56f24%Z)) (ltac:(oD' 0x56f24%Z)). rewrite <- Eneed. zstep (ltac:(oF' 0x56f28%Z)) (ltac:(oD' 0x56f28%Z)). zstep (ltac:(oF' 0x56f2c%Z)) (ltac:(oD' 0x56f2c%Z)).
zbft (ltac:(oF' 0x56f30%Z)) (ltac:(oD' 0x56f30%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_pop_a2z_fn : ltac2:(TCodec.tc2 tcn__JatPopulate1 "R=&8y5'QNyR0%211%5241'2y8%611%311p061'7'5&Cr4(QL+D(3%33A21%6251&QMz%22C1%;3C41r5+:%;3I19%>231r2%92J1%B3J31&Mr3%22<1&J+TP0%22F1+VbTP0%7221&;&Hr7+Q8%92C1u4+SoooooO%7565321'>&DvQ6r9+ZkiD%Q53QA1Q3/01QAr8%756521>&E+;%Q;3QI1Q9+_oooooooooooO%Q82QI1%53;31%631Q<Q8+ZkiH%QA3QM1Q?/01QM%B5A41<I%D3K<1p0F1p0O1p0Q51p0Q91p0QA1pR@QN1pSBR01pDR11pS:R71").
Proof.
intros regs M rom ia H20 H10 Hia Hia' Crel.
zbtk (ltac:(oF' 0x56f34%Z)) (ltac:(oD' 0x56f34%Z)).
zlw (ltac:(oF' 0x570f0%Z)) (ltac:(oD' 0x570f0%Z)) (ia + 40) Crel.
stepb_tk (ltac:(oF' 0x570f4%Z)) (ltac:(oD' 0x570f4%Z)) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x571b8%Z)) (ltac:(oD' 0x571b8%Z)).
stepn (ltac:(oF' 0x571bc%Z)) (ltac:(oD' 0x571bc%Z)).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_pop_a3_fn := (ltac2:(TCodec.tc2 tcn__JatPopulate1 "U?&8y5'QNyR0%211%5241'2y8%611%311p061'7'5&Cr:(QL+8(3%33A21%6251&QMr6%22C1%;3C41r;+:%;3I19%>231r8%92J1%B3J31r<+B%B3Q01@%E231r7%@2Q11%I3Q131r=+C%I3Q71G%L231&Jr5%2291%I2Q:1%Q23Q:51r>+D%Q23Q@1Q0%Q5231%Q73Q?1?&Mz%221G+TP0%>2B1+VbTP0%6221%722E&N+T0%D2?1&Q1+2+Q?%3221%7251%@2?Er?+Q0%8271%N231%=217%F2E5r@%H217rA%Q4219%C241%A2@Q@%M261%N2M7rC%Q:271%Q;215+S`PPPP0%Q3221&;&HrJrG+QH%QC221u8rB%8576321rKrI%QI217u1%=5<421Q@'>&DvQ6rM+ZkiH%RL3S81RJ/01S8rL%756521=&E+1%S23S@1S0+ZkmD%S43S@1S2/01S@%63<41+;%S83SF1S6rFrH%R@221%S72SH1%=3751+<%S?3SM1S=+XPP0%S<2SM1%B3531+=%SD3T21SB+RnlH%SA2T21%G3531%H31RO7%I31RG=+F%SK3T91SI%SG2T8QA%M3421+bdcD%SO3T;1SM/01T;%Q95Q841Q3Q?%Q;3QHQ31p0Q=1p0QC1p0QM1p0R31p0R51p0R81p0R<1p0R?1p0RA1p0RG1p0RI1p0S21p0S41p0S91p0S=1p0SC1p0SM1p0T51p0T=1pRHTJ1pRLTK1pRJTL1pR8TM1pS8TN1pS4TO1pR@U01pSBU21pDU31pS:U91")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 2%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 3%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 4%nat 0%nat).
Variable rb : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 5%nat 0%nat).
Variable au : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 6%nat 0%nat).
Variable mu : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 7%nat 0%nat).
Variable need : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 8%nat 0%nat).
Variable mm : ltac:(sec_ty2 constr:(SEC_T_art_pop_a3_fn) 9%nat 0%nat).
Lemma art_pop_a3_fn : ltac:(sec_stmt2 constr:(SEC_T_art_pop_a3_fn) 10%nat 0%nat).
Proof using Type regs M rom ia r rb au mu need mm.
intros H8 H10 H18 H19 H20 Hia Hia' Hr Hr' Hrb Hrb' Hau Haumu Hneed Hneed' Hmm Hex Cmm Cpm.
zstep (ltac:(oF' 0x56f38%Z)) (ltac:(oD' 0x56f38%Z)). zstep (ltac:(oF' 0x56f3c%Z)) (ltac:(oD' 0x56f3c%Z)). zstep (ltac:(oF' 0x56f40%Z)) (ltac:(oD' 0x56f40%Z)). zstep (ltac:(oF' 0x56f44%Z)) (ltac:(oD' 0x56f44%Z)).
replace (Z_to_bv 64 (au + need + (2 ^ 64 - 1 - mu))) with (Z_to_bv 64 (au + need - mu - 1)) by (apply art_zb_eq; replace (au + need + (2 ^ 64 - 1 - mu)) with (au + need - mu - 1 + 1 * 2 ^ 64) by lia; rewrite Z_mod_plus_full; reflexivity).
stepn (ltac:(oF' 0x56f48%Z)) (ltac:(oD' 0x56f48%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_m18 by lia. rewrite (Z.div_small (au + need - mu - 1)) by lia. change (0 * 2 ^ 18) with 0.
zld (ltac:(oF' 0x56f4c%Z)) (ltac:(oD' 0x56f4c%Z)) (r + 56) Cmm.
zstep (ltac:(oF' 0x56f50%Z)) (ltac:(oD' 0x56f50%Z)). zstep (ltac:(oF' 0x56f54%Z)) (ltac:(oD' 0x56f54%Z)). zstep (ltac:(oF' 0x56f58%Z)) (ltac:(oD' 0x56f58%Z)). zstep (ltac:(oF' 0x56f5c%Z)) (ltac:(oD' 0x56f5c%Z)). zstep (ltac:(oF' 0x56f60%Z)) (ltac:(oD' 0x56f60%Z)). zstep (ltac:(oF' 0x56f64%Z)) (ltac:(oD' 0x56f64%Z)).
zbft (ltac:(oF' 0x56f68%Z)) (ltac:(oD' 0x56f68%Z)).
zlbu (ltac:(oF' 0x56f6c%Z)) (ltac:(oD' 0x56f6c%Z)) (ia + 56) Cpm.
zstep (ltac:(oF' 0x56f70%Z)) (ltac:(oD' 0x56f70%Z)).
zbtk (ltac:(oF' 0x56f74%Z)) (ltac:(oD' 0x56f74%Z)).
zstep (ltac:(oF' 0x56f9c%Z)) (ltac:(oD' 0x56f9c%Z)). zstep (ltac:(oF' 0x56fa0%Z)) (ltac:(oD' 0x56fa0%Z)). zstep (ltac:(oF' 0x56fa4%Z)) (ltac:(oD' 0x56fa4%Z)). zstep (ltac:(oF' 0x56fa8%Z)) (ltac:(oD' 0x56fa8%Z)). zstep (ltac:(oF' 0x56fac%Z)) (ltac:(oD' 0x56fac%Z)).
stepn (ltac:(oF' 0x56fb0%Z)) (ltac:(oD' 0x56fb0%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_pop_a_run : ltac2:(TCodec.tc2 tcn__JatPopulate1 "Z<&8y5'QNyR0%211%5241'2y8%611%311p061'7'5&Cr?(QL+1(3%33A21%6251r<%93A21r@+2%93G17%<231&QM%12H7%@3H31rA+:%@3N1>%C231%E3M16rB+;%E3Q31C%H231%J3Q21;rC+<%J3Q81H%M231%O3Q71@rD+=%O3Q=1M%Q2231%Q43Q<1ErE+>%Q43QB1Q2%Q7231%Q93QA1J&M+R0%221F&N&Q1%12Q44%32E1&J+VbTP0%2218%:21Dz%<21F+TP0%72C1%?217'4%A26F%?2G=%3221%D2QJI+N%F2K1%7231%H2@MrF+T0%D221+Q?%I2QL1%K231%O2R56+8%Q1281%B231&Q0&=rI%211rG%5221%RC3RDQH1%Q:2O3rH+Q5%Q92R<1%Q7231%Q<21B%Q@2Q55%QA2<6rJ%Q<218%QA2?1+B%QB2RE1%QG2B1%QH2Q=CrL%QC281%QD215+S`PPPP0%QM221&:&Q2rQ5%221R0rQ1%542R21Q9&<&HrQ9rQ6%921R7%54431R8&;rQ:+Q0%R6261u8%55:421=rQ;rQ4%R;216%95>315ArQ<+Q@%R?2F1%=5B319ErQ=+QH%RC2C1rQ0%B5G42>1rQ>%RG2C5u1%F5K321RErQ?+Q8%RL2C1u4+SoooooO%L5Q15321'6'>&DvQ6rQB+ZkdD%TD3U01TB/01U0rQArQ@%8576321r1+bdcD%TK3U71TI/01U7&A%148JF<%?5>6318%A3QD81%U328TN+ZkmD%U33U?1U1/01U?%U83U@41%U82=TM%R12Q3SO%TM2UD1%U<3UD31%U:3UHS3U8%U=2B1%U12UHQJ%U@3UH21+9%U?3UM1U=%UB2G1%U62UMQF%UE3UM21%UE2JTNrQ8%T:2U=R2%S<2QO1%T9231%T:21R:%U>2V51%UM3V571%UM2Q2U1+XPP0%UB2V91%V13V931%V12Q6U0+RnlH%UF2V=1%V53V=31%V33VAS7V1%V62Q;1%UJ2VA>%V93VA21+C%V83VF1V6%V;2Q@1%V=3VE1=+D%V<3VJ1V:%V?2QD1%VA3VI1E+E%V@3VN1V>%VC2QH1%T71RK%V82VO1%VG3VO31+F%VF3W41VD%VI2QN1%V=2W4RI%VL3W421%W71W8&I(0+3%VN3W<1VL+4%W03W>1VN+G%W23W@1W0+H%W43WB1W2+I%W63WD1W4+J%W83WF1W6+K%W:3WH1W8(1%11B%A3C31%B3D61%C3E91%D3F<1%E3G?1%F3HB1%G3IE1%I3JRK1r3r2%WI221rQD%WK213%WM3X531p071pT:Q21%V62Q41%V72Q:1%V82QA1%V92QF1%V:2QK1%V;2R01%V<2R51%V=2R:1%V>2RC1%V?2RI1%V@2RN1%VA2S31%VB2S91qS<XD1%SM2XE1p0SO1p0T61p0T;1p0TA1p0TF1p0TK1p0U21p0U91p0U@1p0UF1p0UH1p0UL1p0V01p0V21p0V41p0V:1p0V<1p0VD1p0VI1p0W01p0W21p0W71p0W<1p0W@1p0WC1p0WH1p0WM1p0X11p0X71p0X=1p0XC1p0XI1p0XO1p0Y71pRHYB1pRLYC1pRJYD1pR8YE1pSFYF1pS@YG1pS4YH1pR:YI1pSHYJ1pR@YK1pSDYL1pS6Z41pSBYO1pDZ01pS:Z61").
Proof.
intros regs M rom raw sp ia st c r req spb au mu need mm H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst Hc Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed'
Hmm Hex A W Cspb Cau Cmu Cmm Cpm Crel.
set (MF := art_pop_frame M sp raw regs).
assert (TF : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= sp - 64 \/ sp <= a) -> cellA M a k v -> cellA MF a k v).
{ intros a k v Ha Hak O C. unfold MF, art_pop_frame. do 8 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
assert (Cmm' : cellA MF (r + 56) 8 mm) by (apply TF; [lia|cbn; lia|unfold apart in A; cbn; lia|exact Cmm]).
assert (Cpm' : cellA MF (ia + 56) 1 0) by (apply TF; [lia|cbn; lia|cbn; lia|exact Cpm]).
assert (Crel' : cellA MF (ia + 40) 4 0xffffffff) by (apply TF; [lia|cbn; lia|cbn; lia|exact Crel]).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x56e94 : word) M rom) (mkst r1 (0x56f34 : word) MF rom)
/\ getr r1 2 = Z_to_bv 64 (sp - 64) /\ getr r1 8 = Z_to_bv 64 r /\ getr r1 9 = Z_to_bv 64 st /\ getr r1 10 = Z_to_bv 64 ia
/\ getr r1 18 = Z_to_bv 64 (spb + c * 2 ^ 32) /\ getr r1 19 = Z_to_bv 64 (au + need) /\ getr r1 20 = Z_to_bv 64 mu /\ getr r1 21 = Z_to_bv 64 (AsanTab.class_size c)
/\ (forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr r1 x = getr regs x)).
{ destruct (Z_le_gt_dec c 16) as [Hs|Hb].
- eexists. split; [exact (art_pop_a1s_fn regs M rom raw sp ia st c r req spb au mu need H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst ltac:(lia) Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' ltac:(lia) A W Cspb Cau Cmu)|].
repeat (split; [kept_solve|]). intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; kept_solve.
- eexists. split; [exact (art_pop_a1b_fn regs M rom raw sp ia st c r req spb au mu need H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst ltac:(lia) Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' ltac:(lia) A W Cspb Cau Cmu)|].
repeat (split; [kept_solve|]). intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; kept_solve. }
destruct S1 as (r1 & RUN1 & A2 & A8 & A9 & A10 & A18 & A19 & A20 & A21 & K1).
assert (S2 : exists r2, msteps ASEGS (mkst r1 (0x56f34 : word) MF rom) (mkst r2 (0x56f38 : word) MF rom)
/\ getr r2 2 = Z_to_bv 64 (sp - 64) /\ getr r2 8 = Z_to_bv 64 r /\ getr r2 9 = Z_to_bv 64 st /\ getr r2 10 = Z_to_bv 64 ia
/\ getr r2 18 = Z_to_bv 64 (spb + c * 2 ^ 32) /\ getr r2 19 = Z_to_bv 64 (au + need) /\ getr r2 20 = Z_to_bv 64 mu /\ getr r2 21 = Z_to_bv 64 (AsanTab.class_size c)
/\ (forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr r1 x)).
{ destruct (Z.eq_dec mu 0) as [Ez|Nz].
- subst mu. eexists. split; [exact (art_pop_a2z_fn r1 MF rom ia A20 A10 Hia Hia' Crel')|].
repeat (split; [kept_solve|]). intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; kept_solve.
- exists r1. split.
{ zbft (ltac:(oF' 0x56f34%Z)) (ltac:(oD' 0x56f34%Z)). apply mst_refl. }
repeat (split; [assumption|]). intros; reflexivity. }
destruct S2 as (r2 & RUN2 & B2 & B8 & B9 & B10 & B18 & B19 & B20 & B21 & K2).
pose proof (art_pop_a3_fn r2 MF rom ia r (spb + c * 2 ^ 32) au mu need mm B8 B10 B18 B19 B20 Hia Hia' Hr Hr' ltac:(lia) ltac:(lia) Hau Haumu Hneed Hneed' Hmm Hex Cmm' Cpm') as RUN3.
eexists. split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3. }
split; [gres; reflexivity|]. repeat (split; [kept_solve|]).
intros x Hx. rewrite <- (K1 x Hx), <- (K2 x Hx). cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; kept_solve.
Qed.
#[using="Type"] Lemma art_pop_b_fn : ltac2:(TCodec.tc2 tcn__JatPopulate1 "RK&8y5'QNyR0%211%5241'2y8%611%311p061'7'5&Cr4(QL+:(3%33A21%6251&QMr1%22C1%;3C41r5+D%;3I19%>231r2%92J1%B3J31r6+C%B3Q01@%E231+XPP0%@2Q11%I3Q131'4&Nz%221K&Q1+2+R0%3221%72Q01%9261'>&H&DvQ6r8+ZkmD%Q73QC1Q5/01QCr7%756521J&E+1%Q=3QK1Q;+Zkn@%Q?3QK1Q=/01QK%63<41%Q=2QNQ9%832Q@1+;%QE3R31QC%;331Q1+<%QH3R61QF+WJ%QE2R61%@3531+>%QM3R;1QK%C331<+_X_0%R03R<1QN/01R<%O5N41IQB%Q23Q1I1p0Q41p0Q?1p0QG1p0QO1pS2R<1pSBR>1pDR?1pS:RE1").
Proof.
intros regs M rom p H10 H20 H19 Hp.
zbft (ltac:(oF' 0x56fb4%Z)) (ltac:(oD' 0x56fb4%Z)). zstep (ltac:(oF' 0x56fb8%Z)) (ltac:(oD' 0x56fb8%Z)). zbft (ltac:(oF' 0x56fbc%Z)) (ltac:(oD' 0x56fbc%Z)).
zstep (ltac:(oF' 0x56fc0%Z)) (ltac:(oD' 0x56fc0%Z)). zstep (ltac:(oF' 0x56fc4%Z)) (ltac:(oD' 0x56fc4%Z)). zstep (ltac:(oF' 0x56fc8%Z)) (ltac:(oD' 0x56fc8%Z)).
stepn (ltac:(oF' 0x56fcc%Z)) (ltac:(oD' 0x56fcc%Z)).
zret.
Qed.
#[using="Type"] Lemma art_zb_divu : ltac2:(TCodec.tc2 tcn__JatPopulate1 "Q2'7'4&Mzr2%3221&N&Q1+2+R0%3221%5271%;271%72:9%=213'5'QNyR0%211&G&QMr4%2251r3%4271%6231&K%1264%82;1%>3;41p0@1p0C1pT<Q01pT:Q11").
Proof. intros x y Hx Hy. unfold v_divu. rewrite !art_u_lit by lia. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_art_pop_c_fn := (ltac2:(TCodec.tc2 tcn__JatPopulate1 "ZJ&8y5'QNyR0%211%5241'2y8%611%311p061'7'5&CrF(QL+2(3%33A21%6251&QMrC%22C1%;3C41rG+4%;3I19%>231%@3H16rH+8%@3N1>%C231r=%>2O1%G3O31rI+9%G3Q51E%J231r?%E2Q61%N3Q631rJ+B%N3Q<1L%Q1231r>%L2Q=1%Q53Q=31rK+C%Q53QC1Q3%Q8231+XPP0%Q32QD1%Q<3QD31rL+E%Q<3QJ1Q:%Q?231%QA3QI1DrM+F%QA3QO1Q?%QD231rD%Q?2R01%QH3R031&M+Q0%221E&N&Q1+R0%22QK1%42C1&J+VbTP0%2219%;21B'4z%>21QF%<2QG9%4221+TP0%B21QJ%;2QD>%A21>&O+H%?2QA1%321QO%RB3RC1<%J2AQD+T0%D2Q?1+Q?%J2RC1%L231%Q02CQC%N2QDK%F221+RPP0%Q42QG1%I2Q31%Q62QBQI%O2QCQF%Q42RMQ7%Q9221&Q2%Q32QBQJrN%3221&Q0rO%22R31%Q921R;%S;3S<51rQ0%QA2R71%Q92E1%QF2Q9QM%QG2Q:8%QE29@%Q=221%QG2R1QD%Q?251rQ;%QM2Q<1rQ<%QG21Q>%QM21QJ&<&HrQDrQB%K21R4%54431R5&?rQErQArQ@rQ?rQ>%66594321&:%Q52<R>+QWY[0%342R@1SH%Q82:RA+RH%Q:2A1%743RD1SLrQF%Q=21RFrQC%Q;2T0F%RB221%=44RJ1T2rQG%QC21RL+TH%RG271%B43RO1T7rQH%QH21S1+RiH%RL2<1+@%H44S521rQI%QN21S7%S12Q5RC%L42S91TArQJ%R221S;%O41S<Q9RB%S62H;%S72Q<RI%Q242;1TG%S92E>%Q441=Q?RG%S;2MRM%Q641TKQ<RIrR0%S>2?C%QF4QE21BrR1%SA2HS3%QI4QH21U1rR2%QK4QJ1KS1&;rR3rQL%SH21Mu8%55R0421QIrR4rQM+Rj0%SN221%:5R5416QNrR5%T12:SC%=5R8219R1rR6+Q@%T52>1%A5R<31=Q=rR7%T82<T?%D5R?21@Q6rR8rQN%T<21Q?%H5RC31DQ>'>&DvQ6rR:+Zkn@%VA3VM1V?/01VMrR9%756521<&E+1%VG3W51VE+ZlQ8%VI3W51VG/01W5%63<41%VG2W8G%832VJ1%U02QMR1%VJ2W;1%;33V91+:%W23W@1W0%VN2W?QE%?3421+;%W63WD1W4rQO%W32WD1%D3531+<%W;3WI1W9%W72WHQ3%H3421+=%W?3WM1W=%K331A%W<2WMRD%M32V=1+D%WD3X21WBrQK%UH21V?%TG21R2%WC2X41%Q43751+ZbjH%WK3X71WI/01X7&@%19Q;QIR=RCGS<SBT09%QB5QA631QG%QD3T8Q<1p0QF1p0QK1p0QO1p0R41p0R81p0R>1p0RE1p0RH1p0RL1p0S01p0S31p0S61p0S:1p0S>1p0SC1p0SJ1p0T01p0T71p0T<1p0TA1p0TI1p0U01p0U41p0U71p0U81p0U91p0U<1p0U@1p0UB1p0UF1p0V01p0V41p0V;1p0V71p0V;1p0V?1p0VE1p0VG1p0VM1p0W01p0W31p0W91p0W>1p0WD1p0WH1p0X01p0X61p0X>1p0XF1p0XN1p0Y61p0Y<1pT0YI1pRFYJ1pRDYK1pS>YL1pRNYM1pS0YN1pRJYO1pR8Z01pT2Z11pS8Z21pS4Z31pSHZ41pR@Z51pT4Z61pR<Z71pT8Z81pRBZ91pT6Z:1pSDZ;1pSBZ=1pDZ>1pS:ZD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 3%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 4%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 5%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 6%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 7%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 8%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 9%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 10%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 11%nat 0%nat).
Variable rb : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 12%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 13%nat 0%nat).
Variable au : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 14%nat 0%nat).
Variable mu : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 15%nat 0%nat).
Variable nf : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 16%nat 0%nat).
Variable new : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 17%nat 0%nat).
Variable rem : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 18%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 19%nat 0%nat).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 20%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_pop_c_fn) 21%nat 0%nat).
Lemma art_pop_c_fn : ltac:(sec_stmt2 constr:(SEC_T_art_pop_c_fn) 22%nat 0%nat).
Proof using Type regs M rom sp tp key tsd ctx t ia st r rb sz au mu nf new rem m1 m2 sv.
intros H2 H4 H8 H9 H18 H19 H21 H22 Hsp Hsp' IMG Hia Hst Hst' Hst8 Hr Hr' Hrb Hsz Hau Haumu Hmu Ediv Hrem Hnew Hnf
Hm1 Hm2 Hsv Ht Ht' W TSD A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 Wt Wst Wr C1 C2 Csv Cmu Cau Cnf.
stepn (ltac:(oF' 0x56fd0%Z)) (ltac:(oD' 0x56fd0%Z)).
zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
change (U (356308 : bv 64)%bv) with 356308.
match goal with |- msteps _ (mkst _ _ ?X _) _ => set (MT := X) end.
assert (TT : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> apart (sp - 32) 32 a (Z.of_nat k) -> cellA M a k v -> cellA MT a k v).
{ intros a k v Ha Hak O C. unfold MT. unfold apart in O. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
assert (WT : forall a k, wrA M a k -> wrA MT a k) by (intros a k Hw; unfold MT; do 2 apply wr_Wn; exact Hw).
assert (C1' : cellA MT (t + 2872) 8 m1) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C1]).
assert (C2' : cellA MT (t + 2880) 8 m2) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C2]).
zld (ltac:(oF' 0x56fd4%Z)) (ltac:(oD' 0x56fd4%Z)) (t + 2872) C1'. zld (ltac:(oF' 0x56fd8%Z)) (ltac:(oD' 0x56fd8%Z)) (t + 2880) C2'.
zstep (ltac:(oF' 0x56fdc%Z)) (ltac:(oD' 0x56fdc%Z)). zstep (ltac:(oF' 0x56fe0%Z)) (ltac:(oD' 0x56fe0%Z)).
zsd (ltac:(oF' 0x56fe4%Z)) (ltac:(oD' 0x56fe4%Z)) (t + 2872) (m1 + 1) ltac:(eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
zsd (ltac:(oF' 0x56fe8%Z)) (ltac:(oD' 0x56fe8%Z)) (t + 2880) (m2 + 262144) ltac:(apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
zstep (ltac:(oF' 0x56fec%Z)) (ltac:(oD' 0x56fec%Z)). zstep (ltac:(oF' 0x56ff0%Z)) (ltac:(oD' 0x56ff0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csv' : cellA X (st + 24) 8 sv)
by (unfold apart in A8; do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]); apply TT; [lia|cbn; lia|unfold apart in A6 |- *; cbn; lia|exact Csv]) end.
zamoadd_d (ltac:(oF' 0x56ff4%Z)) (ltac:(oD' 0x56ff4%Z)) (st + 24) sv 262144 Csv' ltac:(do 2 apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wst)); lia).
match goal with |- msteps _ (mkst _ _ ?X _) _ => set (MS := X) end.
assert (TS : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> r <= a -> a + Z.of_nat k <= r + 128 -> cellA M a k v -> cellA MS a k v).
{ intros a k v Ha Hak Hlo Hhi C. unfold MS. unfold apart in A7, A9, A10. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). apply TT; [lia|lia|unfold apart; lia|exact C]. }
assert (Cmu' : cellA MS (r + 48) 8 mu) by (apply TS; [lia|cbn; lia|lia|cbn; lia|exact Cmu]).
assert (Cau' : cellA MS (r + 32) 8 au) by (apply TS; [lia|cbn; lia|lia|cbn; lia|exact Cau]).
zld (ltac:(oF' 0x56ff8%Z)) (ltac:(oD' 0x56ff8%Z)) (r + 48) Cmu'. zld (ltac:(oF' 0x56ffc%Z)) (ltac:(oD' 0x56ffc%Z)) (r + 32) Cau'.
zstep (ltac:(oF' 0x57000%Z)) (ltac:(oD' 0x57000%Z)).
zsd (ltac:(oF' 0x57004%Z)) (ltac:(oD' 0x57004%Z)) (r + 48) (mu + 262144) ltac:(unfold MS; do 3 apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wr)); lia).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cnf' : cellA X (r + 16) 8 nf)
by (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]; apply TS; [lia|cbn; lia|lia|cbn; lia|exact Cnf]) end.
zld (ltac:(oF' 0x57008%Z)) (ltac:(oD' 0x57008%Z)) (r + 16) Cnf'.
zstep (ltac:(oF' 0x5700c%Z)) (ltac:(oD' 0x5700c%Z)).
stepn (ltac:(oF' 0x57010%Z)) (ltac:(oD' 0x57010%Z)); [rewrite H21, art_u_lit by lia; lia|]. rwH. rewrite art_zb_divu by lia. replace ((mu + 262144 - au) / sz) with new by (apply (Z.div_unique_pos _ _ new rem); lia).
zstep (ltac:(oF' 0x57014%Z)) (ltac:(oD' 0x57014%Z)). zstep (ltac:(oF' 0x57018%Z)) (ltac:(oD' 0x57018%Z)). zstep (ltac:(oF' 0x5701c%Z)) (ltac:(oD' 0x5701c%Z)). zstep (ltac:(oF' 0x57020%Z)) (ltac:(oD' 0x57020%Z)).
stepn (ltac:(oF' 0x57024%Z)) (ltac:(oD' 0x57024%Z)).
unfold art_pop_c_mem. subst MS MT. zret.
Qed.
End SE.
End FPX.
