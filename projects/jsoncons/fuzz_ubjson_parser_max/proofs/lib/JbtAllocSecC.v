(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtPoison JbtSecAlloc JbtAllocC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocSecC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7getr"]; ["7mkst"; "7regupd"; "8loaded_segments"; "9add"; "9div"; "9le"; "9lt"; "9modulo"; "9mul"; "9pow"; "9sub"; "0ab"; "0fx"; "0ia"; "0id"; "0n"]; ["0nd"; "0q"; "0regs"; "0regs'"; "0rom"; "0rz"; "0spb"; ":BV"; ":Z_to_bv"; ":bv"; "0tb"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_csec_range := (ltac2:(TCodec.tc2 tcn__JbtAllocSecC "SJ&8y5'Q9yR0%211%5241'0y8%611%311p061'7'3&?r6(Q7+B(1%33A21%6251&Q8r2%22C1%;3C41r7+F%;3I19%>231r4%92J1%B3J31&Ezr5%3221&F&C+TP0%22H1&I+2+R0%3221%8251'2%>2=O+Q@%8271%=2Q21%5241+Q5%<2;1%@2L1%B216'6r9r8%F221%F227%L214%6231&<&Br=r;+Q0%N221u8%756521='4'>&@vLr@+ZXd@%QL3R81QJ/01R8r?r>%8576321r1+ZXf<%R33R?1R1/01R?%=5<4176%?3G61%RD1RE&5+:%R:3RH1R8%R>34:1%411+;%R>3RL1R<%RB38R91%811r3%RD2R51rC%RF213%RH3S031p061p0;1pRHA1%QL2C1qR8S41%Q52S51p0Q71p0Q@1p0QH1p0R11p0QN1p0R51p0R?1p0RD1p0RL1pR>S91pQHS:1pQLS;1pR:S=1pDS>1pR6SD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec_range) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec_range) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec_range) 2%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec_range) 3%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec_range) 4%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec_range) 5%nat 0%nat).
Lemma art_alloc_csec_range : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_csec_range) 6%nat 0%nat).
Proof using Type regs M rom ia ab spb.
intros H18 H22 Hia Hia' Hab Hspb Hspb' OUT Cspb.
destruct OUT as [LO|HI].
- eexists. split.
+ zld (ltac:(oF' 0x52290%Z)) (ltac:(oD' 0x52290%Z)) (ia + 32) Cspb. zbtk (ltac:(oF' 0x52294%Z)) (ltac:(oD' 0x52294%Z)). apply mst_refl.
+ intros; kept_solve.
- eexists. split.
+ zld (ltac:(oF' 0x52290%Z)) (ltac:(oD' 0x52290%Z)) (ia + 32) Cspb. zbft (ltac:(oF' 0x52294%Z)) (ltac:(oD' 0x52294%Z)).
zstep (ltac:(oF' 0x52298%Z)) (ltac:(oD' 0x52298%Z)). zstep (ltac:(oF' 0x5229c%Z)) (ltac:(oD' 0x5229c%Z)). zstep (ltac:(oF' 0x522a0%Z)) (ltac:(oD' 0x522a0%Z)).
zbtk (ltac:(oF' 0x522a4%Z)) (ltac:(oD' 0x522a4%Z)). apply mst_refl.
+ intros; kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_alloc_csec1 := (ltac2:(TCodec.tc2 tcn__JbtAllocSecC "YF&8y5'Q9yR0%211%5241'0y8%611%311p061'7'3&?r;(Q7+:(1%33A21%6251&Q8r4%22C1%;3C41r<+8%;3I19%>231z%92J1%B3J31r=+9%B3Q01@%E231r8%@2Q11%I3Q131r>+B%I3Q71G%L231r:%G2Q81%Q03Q831r?+D%Q03Q>1N%Q3231&Cr9%22Q51%Q02QA1%Q93QA51r@+E%Q93QG1Q7%Q<231&J%:2Q3A+@%3221%Q:2QK1%QC3QK61rA+F%QC3R11QA%QF231%Q@2R1N%QI3R121rB+H%QI3R71QG%QL231%QN3R61Q=rC+I%QN3R<1QL%R1231%N2Q2Q@%O21Q:%QM2R>1%R63R>41&E%12QHD&F+TP0%Q62A1&I+2+R0%3221%7251+XP0%;21H%Q>2DQB%Q?213+Q@%:291%>231&GrD%221@%RK3RL1R;'2%F2Q=N+RP0%H2Q01%4231rE%K2RE1+Q8%H2G1%L241%:241rF%R3217%Q221Q:%Q32RJ9+Q0%Q02O1%Q42<1%B241&H+1%R32H1%32Q81%Q:21B%52Q:K%Q>2D1%J231%Q@2S7N+Q5%Q=2Q<1%RE2I1%QB21Q5'6rL%QE21G%RJ2H6%QI213%5231&=&BrQ0rMrK%S2221%RJ21RH%74651RI&<rQ1rO%S821Q2u8rH%65=5321rQ2%S=2>R4%95@215R9rQ3%S72AR;%SA21S6%=5D319J&;%SD2>=%S<21S:%SF2:Q@%442S<1QI%SH2<I%S@21S>%SA2>RE%SK21S@%943SA1TD'4'>&@vLrQ8+ZXc0%U53UA1U3/01UArQ7rQ6%8576321r1+_YU@%U<3UH1U:/01UH&:rQ4%T>21Q2%T621U7%44Q7;1Q:%B5A961;%D3QD;1%UE3V3R8UC%UH2<1+ZXiH%UH3V41UF/01V4%UM3V541%UM2AUH%UG2V8=%V03V821+;%UO3V=1UM%V22F1%UL2V=QC%V53V=21+<%V43VB1V2%V72K1+WJ%V22VC1%V;3VC31%V;2OUN%RN2T3R1%V62VG1%V?3VG31%V?2Q3TJ&D%U=2OQN+7%U?221%421V8%S721V9%V?2W01%VH3W081%W31W4&5%VK32Q>Q3%211r2%VN351V@%511r3%W1381VK%811%W33:VJQ1%:11r5%W63=1O%=11r6%W93@1UC%@11r7%W<3C1U;%C11%W=2V8VGrQ@%W?21VI%WA3WI31p051p091p0=1p0A1p0D1p0H1p0L1pRHQ01%TN2Q21%TO2Q<1%U02QA1%U12QH1%U22QN1%U32R21%U42R91qR8X81%S02X91p0S21p0S81p0S>1p0SC1p0SG1p0SO1p0T81p0T?1p0TD1p0TF1p0TO1p0U51p0U91p0U@1p0UF1p0UK1p0V11p0V41p0V=1p0V@1p0VI1p0VO1p0W61p0WA1p0WK1p0X31p0X;1p0XC1pR>Y01pR4Y11pR2Y21pQNY31pR<Y41pR0Y51pQHY61pQLY71pR:Y91pDY:1pR6Y@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 2%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 3%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 5%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 6%nat 0%nat).
Variable id : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 7%nat 0%nat).
Variable nd : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 8%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 9%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_alloc_csec1) 10%nat 0%nat).
Lemma art_alloc_csec1 : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_csec1) 11%nat 0%nat).
Proof using Type regs M rom ia ab n rz id nd q spb.
intros H10 H8 H9 H18 H20 H21 H22 H24 H25 Hia Hia' Hab Hab' Hab4 Hrz Hn Hnd Hid Hq Hspb Hspb' OUT W Cspb Cpg Cnd A1 A2.
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x52260 : word) M rom) (mkst r1 (0x52290 : word) (Wn 8 M (ab + rz - 8) id) rom)
/\ (forall x : reg, x <> 10%bv -> getr r1 x = getr regs x)).
{ eexists. split.
- stepn (ltac:(oF' 0x52260%Z)) (ltac:(oD' 0x52260%Z)). rwH. rewrite art_zb_slli by lia.
stepn (ltac:(oF' 0x52264%Z)) (ltac:(oD' 0x52264%Z)). rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
stepn (ltac:(oF' 0x52268%Z)) (ltac:(oD' 0x52268%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
zsd (ltac:(oF' 0x5226c%Z)) (ltac:(oD' 0x5226c%Z)) (ab + rz - 16 + 8) id ltac:(rewok W).
zbtk (ltac:(oF' 0x52270%Z)) (ltac:(oD' 0x52270%Z)). replace (ab + rz - 16 + 8) with (ab + rz - 8) by lia. apply mst_refl.
- intros; kept_solve. }
destruct S1 as (r1 & RUN1 & K1).
set (M1 := Wn 8 M (ab + rz - 8) id) in *.
assert (Cspb1 : cellA M1 (ia + 32) 8 spb) by (unfold M1; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in *; cbn; lia|exact Cspb]).
assert (Cpg1 : cellA M1 (ia + 64) 8 4096) by (unfold M1; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in *; cbn; lia|exact Cpg]).
assert (Cnd1 : cellA M1 (ab - 4096 + 16) 8 nd) by (unfold M1; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in *; cbn; lia|exact Cnd]).
destruct (art_alloc_csec_range r1 M1 rom ia ab spb ltac:(rewrite K1 by discriminate; exact H18) ltac:(rewrite K1 by discriminate; exact H22)
Hia Hia' ltac:(lia) Hspb Hspb' OUT Cspb1) as (r2 & RUN2 & K2).
assert (KK : forall x : reg, x <> 10%bv -> x <> 11%bv -> getr r2 x = getr regs x).
{ intros x N10 N11. rewrite K2 by assumption. apply K1. exact N10. }
assert (Q18 : getr r2 18 = Z_to_bv 64 ab) by (rewrite KK by discriminate; exact H18).
assert (Q20 : getr r2 20 = Z_to_bv 64 (ab + rz)) by (rewrite KK by discriminate; exact H20).
assert (Q22 : getr r2 22 = Z_to_bv 64 ia) by (rewrite KK by discriminate; exact H22).
assert (Q25 : getr r2 25 = Z_to_bv 64 (ab + rz + n)) by (rewrite KK by discriminate; exact H25).
assert (E4096 : Z.land 4095 ab = 0).
{ rewrite Z.land_comm. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. exact Hab4. }
assert (Erup : Z.land (nd + 4095) (2 ^ 64 - 2 ^ 12) = 4096 * q).
{ rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
assert (E : (nd + 4095) mod 4096 = nd + 4095 - 4096 * q). { symmetry. apply (Z.mod_unique_pos _ _ q); lia. }
rewrite E. lia. }
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x522cc : word) M1 rom) (mkst r3 (0x7a4b0 : word) M1 rom)
/\ getr r3 1 = (0x52338 : bv 64)%bv /\ getr r3 10 = Z_to_bv 64 ab /\ getr r3 11 = Z_to_bv 64 rz /\ getr r3 12 = Z_to_bv 64 250
/\ getr r3 8 = Z_to_bv 64 (4096 * q) /\ getr r3 22 = Z_to_bv 64 ((ab + rz + n + 7) / 8 * 8)
/\ (forall x : reg, x <> 1%bv -> x <> 8%bv -> x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 22%bv -> x <> 25%bv -> getr r3 x = getr r2 x)).
{ eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- zld (ltac:(oF' 0x522cc%Z)) (ltac:(oD' 0x522cc%Z)) (ia + 64) Cpg1.
zstep (ltac:(oF' 0x522d0%Z)) (ltac:(oD' 0x522d0%Z)).
stepn (ltac:(oF' 0x522d4%Z)) (ltac:(oD' 0x522d4%Z)). rwH. rewrite art_zb_and by lia. rewrite E4096.
zbft (ltac:(oF' 0x522d8%Z)) (ltac:(oD' 0x522d8%Z)).
stepn (ltac:(oF' 0x522dc%Z)) (ltac:(oD' 0x522dc%Z)). rwH.
zbft (ltac:(oF' 0x522e0%Z)) (ltac:(oD' 0x522e0%Z)).
zstep (ltac:(oF' 0x522e4%Z)) (ltac:(oD' 0x522e4%Z)).
zld (ltac:(oF' 0x522e8%Z)) (ltac:(oD' 0x522e8%Z)) (ab - 4096 + 16) Cnd1.
zstep (ltac:(oF' 0x522ec%Z)) (ltac:(oD' 0x522ec%Z)).
zstep (ltac:(oF' 0x522f0%Z)) (ltac:(oD' 0x522f0%Z)).
stepn (ltac:(oF' 0x522f4%Z)) (ltac:(oD' 0x522f4%Z)). rwH. rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite Erup.
stepn (ltac:(oF' 0x522f8%Z)) (ltac:(oD' 0x522f8%Z)).
zstep (ltac:(oF' 0x52320%Z)) (ltac:(oD' 0x52320%Z)).
stepn (ltac:(oF' 0x52324%Z)) (ltac:(oD' 0x52324%Z)). rwH. unfold v_andi. rewrite (art_u_lit (ab + rz + n + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
zstep (ltac:(oF' 0x52328%Z)) (ltac:(oD' 0x52328%Z)). replace (ab + rz - ab) with rz by lia.
zstep (ltac:(oF' 0x5232c%Z)) (ltac:(oD' 0x5232c%Z)). zstep (ltac:(oF' 0x52330%Z)) (ltac:(oD' 0x52330%Z)).
stepn (ltac:(oF' 0x52334%Z)) (ltac:(oD' 0x52334%Z)).
apply mst_refl.
- gres. apply bv_eq. reflexivity.
- kept_solve. - kept_solve. - kept_solve. - kept_solve. - kept_solve.
- intros; kept_solve. }
destruct S3 as (r3 & RUN3 & X1 & X10 & X11 & X12 & X8 & X22 & K3).
exists r3. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; try assumption.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- intros x N1 N8 N10 N11 N12 N22 N25. rewrite K3 by assumption. apply KK; assumption.
Qed.
End SE.
#[using="Type"] Lemma art_alloc_csec2 : ltac2:(TCodec.tc2 tcn__JbtAllocSecC "S<&8y5'Q9yR0%211%5241'0y8%611%311p061'7'3&?r6(Q7+B(1%33A21%6251&Q8r3%22C1%;3C41r7+F%;3I19%>231%@3H16r8+8%@3N1>%C231&H+TP0%221>%@2Q11%I3Q151&Ez%221J&C%928L%22>1%62D1&Fr9%>2=G%7221&I+2+Q?%3221%8251'>&B&@vLr=+ZXiH%Q=3QI1Q;/01QIr<r;%8576321&A+1%QD3R21QB+ZXj<%QF3R21QD/01R2%63=41+:%QJ3R81QH%QF2R7L%:3421+;%QN3R<1QL&Jr:%Q?2Q>QC%Q8221%421Q4%QO2R@1%C3971+<%R73RE1R5+WJ%R42RE1%H3531+_YU@%R<3RH1R:/01RH%Q55Q441ON%Q83Q7N1p0Q:1p0QD1p0QI1p0QJ1p0QN1p0R81p0R>1pR4RK1pRFRL1pQHRM1pR:RO1pDS01pR6S61").
Proof.
intros regs M rom ab tb q H18 H22 H8 Hab Htb Hle Hhi.
zstep (ltac:(oF' 0x52338%Z)) (ltac:(oD' 0x52338%Z)). zstep (ltac:(oF' 0x5233c%Z)) (ltac:(oD' 0x5233c%Z)). zstep (ltac:(oF' 0x52340%Z)) (ltac:(oD' 0x52340%Z)). zstep (ltac:(oF' 0x52344%Z)) (ltac:(oD' 0x52344%Z)).
stepn (ltac:(oF' 0x52348%Z)) (ltac:(oD' 0x52348%Z)).
replace (ab - tb + 4096 * q) with (ab + 4096 * q - tb) by lia.
zret.
Qed.
#[using="Type"] Lemma art_alloc_csec3 : ltac2:(TCodec.tc2 tcn__JbtAllocSecC "S<&8y5'Q9yR0%211%5241'0y8%611%311p061'7'3&?r6(Q7+9(1%33A21%6251&Q8r2%22C1%;3C41r7+D%;3I19%>231&Cr4%2219%;2L1%D3L51&Ezr5%3221&F%:2H9&I+2+Q?%3221%6251'2+8%=21F+Q8%9281%<2I1%6241'>&B&@vLr<+ZXj<%Q:3QF1Q8/01QFr;r:%8576321&A+1%QA3QO1Q?+ZXk<%QC3QO1QA/01QO%63=41+:%QG3R51QEr9%Q<21Q@%QE2R61%<3641+;%QM3R;1QK&H&Dr8%221Q3%421Q4%QN2R?1%E3971+<%R63RD1R4%R22RCQD%I3421+F%R:3RH1R8%L3318+_YU@%R=3RI1R;/01RI%Q95Q841Q3Q2%Q<3Q;Q21p0Q>1p0QM1p0QG1p0QO1p0R41p0R>1pR<RK1pR0RL1pQHRM1pR:RO1pDS01pR6S61").
Proof.
intros regs M rom ab n rz H9 H20 Hab Hab' Hrz Hn.
zstep (ltac:(oF' 0x5234c%Z)) (ltac:(oD' 0x5234c%Z)). zstep (ltac:(oF' 0x52350%Z)) (ltac:(oD' 0x52350%Z)).
stepn (ltac:(oF' 0x52354%Z)) (ltac:(oD' 0x52354%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
assert (8 <= n / 8 * 8). { pose proof (Z.div_le_mono 8 n 8 ltac:(lia) ltac:(lia)) as D. change (8 / 8) with 1 in D. lia. }
pose proof (Z.mul_div_le n 8 ltac:(lia)).
zbft (ltac:(oF' 0x52358%Z)) (ltac:(oD' 0x52358%Z)).
zstep (ltac:(oF' 0x5235c%Z)) (ltac:(oD' 0x5235c%Z)). zstep (ltac:(oF' 0x52360%Z)) (ltac:(oD' 0x52360%Z)). zstep (ltac:(oF' 0x52364%Z)) (ltac:(oD' 0x52364%Z)).
stepn (ltac:(oF' 0x52368%Z)) (ltac:(oD' 0x52368%Z)).
zret.
Qed.
End FPX.
