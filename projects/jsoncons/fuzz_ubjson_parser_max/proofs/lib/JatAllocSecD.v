(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatPoison JatAllocC JatAllocD JatAllocV.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAllocSecD () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocSecD.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocV."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6msteps"; "7art_d2_kept"; "7art_d2_large_mem"]; ["8art_d1_addr"; "8art_d1_kept"; "8art_d1_mem"; "9art_tsd"; ":SB"; ":art_layout"; ":kHighMemBeg"; ";getr"; ";mkst"; "<loaded_segments"; "=add"; "=div"; "=le"; "=lt"; "=modulo"; "=mul"]; ["=pow"; "=sub"; "0ab"; "0ctx"; "0fx"; "0key"; "0mb"; "0mc"; "0ml"; "0mr"; "0n"; "0nd"; "0r"; "0regs"; "0regs'"; "0rom"]; ["0rz"; "0sp"; ">BV"; ">Z_to_bv"; ">bv"; "0t"; "0tp"; "0tsd"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_d1_any := (ltac2:(TCodec.tc2 tcn__JatAllocSecD "TF&8y5'QDyR0%211%5241'0y8%611%311p061'7'3&Gr6(QB+9(1%33A21%6251&QCr2%22C1%;3C41r7+D%;3I19%>231&Jr4%2219%;2L1%D3L51r8+F%D3Q21B%G231&O&K+8%22;1%4212%F2Q71%O3Q771&L+TP0%221Q0&Mr5%E2I1%F21Q4&Q0+2+Q?%3221%8251'6%M2HQ;%N21Q2&D%=221&F%B21M%7231'2+@%F21Q:+RP0%H2Q<1%5231r9%K2Q01+Q8%F2E1%K241%;241&Er=%211&;&Ir>+QWQWH+RE%QH221u1+1%8576321&5&Nr<%221QDz%RA3RB21%611&<r@&@%13A8E%44C31=p061'4'=&HvQ4rB+ZXTL%RL3S81RJ/01S8rA%756521>r1+ZXY@%S23S>1S0/01S>&Br?%2481Q8Q4%?5>741F%A3Q791%SF1SG&A%11;r3%S?21S7rD%SA21S9%SC3SK31p061pRJ91%R22;1qRNSN1%O2SO1p0Q11p0Q?1p0QI1p0QM1p0R41p0R;1p0RD1p0RN1p0S21p0S>1p0SH1pS2T51pRFT61pR6T71pS0T91pDT:1pRLT@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_any) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_any) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_any) 2%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_any) 3%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_any) 4%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d1_any) 5%nat 0%nat).
Lemma art_alloc_d1_any : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_d1_any) 6%nat 0%nat).
Proof using Type regs M rom ab n rz.
intros H9 H20 H22 Hab Hab' MEM Hrz Hn L Cpp Wsh.
unfold art_d1_mem, art_d1_addr in *.
destruct (Z.eqb_spec (n mod 8) 0) as [E|NE].
- exists regs. split; [|intros r _; reflexivity].
apply (art_alloc_d1_none regs M rom n H9 H22 ltac:(lia) E).
- specialize (Wsh NE). unfold SB, kHighMemBeg in MEM.
pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
pose proof (Z.mul_div_le n 8 ltac:(lia)) as D1. pose proof (Z.mul_succ_div_gt n 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as D3. pose proof (Z.div_mod n 8 ltac:(lia)) as D4.
assert (D5 : n / 8 * 8 <> n) by lia.
destruct MEM as [LO|HI].
+ eexists. split.
* zbft (ltac:(oF' 0x5209c%Z)) (ltac:(oD' 0x5209c%Z)).
stepn (ltac:(oF' 0x520a0%Z)) (ltac:(oD' 0x520a0%Z)).
zcall (art_can_poison_fn _ _ _ _).
zbft (ltac:(oF' 0x520a4%Z)) (ltac:(oD' 0x520a4%Z)).
zstep (ltac:(oF' 0x520a8%Z)) (ltac:(oD' 0x520a8%Z)). zld (ltac:(oF' 0x520ac%Z)) (ltac:(oD' 0x520ac%Z)) 0x132638 G48. zld (ltac:(oF' 0x520b0%Z)) (ltac:(oD' 0x520b0%Z)) 0x13acf8 Csb. unfold SB.
zstep (ltac:(oF' 0x520b4%Z)) (ltac:(oD' 0x520b4%Z)). zstep (ltac:(oF' 0x520b8%Z)) (ltac:(oD' 0x520b8%Z)). zstep (ltac:(oF' 0x520bc%Z)) (ltac:(oD' 0x520bc%Z)). zstep (ltac:(oF' 0x520c0%Z)) (ltac:(oD' 0x520c0%Z)). zstep (ltac:(oF' 0x520c4%Z)) (ltac:(oD' 0x520c4%Z)).
zbtk (ltac:(oF' 0x520c8%Z)) (ltac:(oD' 0x520c8%Z)).
zstep (ltac:(oF' 0x5210c%Z)) (ltac:(oD' 0x5210c%Z)). zld (ltac:(oF' 0x52110%Z)) (ltac:(oD' 0x52110%Z)) 0x132630 G40.
zlbu (ltac:(oF' 0x52114%Z)) (ltac:(oD' 0x52114%Z)) (0x1384f8 + 85) Cpp.
stepn (ltac:(oF' 0x52118%Z)) (ltac:(oD' 0x52118%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
zstep (ltac:(oF' 0x5211c%Z)) (ltac:(oD' 0x5211c%Z)). zstep (ltac:(oF' 0x52120%Z)) (ltac:(oD' 0x52120%Z)).
stepn (ltac:(oF' 0x52124%Z)) (ltac:(oD' 0x52124%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
stepn (ltac:(oF' 0x52128%Z)) (ltac:(oD' 0x52128%Z)). rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
zsb (ltac:(oF' 0x5212c%Z)) (ltac:(oD' 0x5212c%Z)) (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
apply mst_refl.
* intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
+ eexists. split.
* zbft (ltac:(oF' 0x5209c%Z)) (ltac:(oD' 0x5209c%Z)).
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
apply mst_refl.
* intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
Definition art_d2_large_mem (M : word -> option byte) (sp t n nd mc mb mr ml : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x52134) (sp - 24) 0x82164) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (nd - n)))
(t + 2800 + 104) (ml + 1).
Definition art_d2_kept (r : reg) : Prop :=
r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.
Section SE.
Local Abbreviation SEC_T_art_alloc_d2_large_fn := (ltac2:(TCodec.tc2 tcn__JatAllocSecD "Y0&8y5'QDyR0%211%5241'0y8%611%311p061'7'3&GrA(QB+2(1%33A21%6251&QCr>%22C1%;3C41rB+4%;3I19%>231r:%92J1%B3J31rC+9%B3Q01@%E231%G3O1=rD+C%G3Q51E%J231%L3Q41BrE+D%L3Q:1J%O231&J%12Q0I%K2Q<1%Q43Q<41&L+Q0%221D&M+T0%92B1&Q0+R0%22Q91%6241+VbTP0%?21:%<21D+TP0%>21K%?2GL'2+RPP0%?21J+Q8%>2QE1%B2M1%6241zrH%M21Q1%J231%H22C%<221r@%N271%L22G%@221&<&IrQ0&Q1rN%221Q5%64541Q6&CrQ1rJrIrGrF%66543F21%Q?2Q23%QD2HQ3%Q>21Q9'6%QG28Q6%QD21Q3%QE2Q;:%4221&:rQ3%E21QH+QWY[0+8%543QK21rQ4%J21QMrO+RH%M221%;44R117rQ5%Q021R3&O%12;7%R;2Q21%A44R71=rQ6%Q621R9+TH%R@2Q71%F43R<1BrQ7%Q;21R>+U0+Rg@%RF2Q=1+S@%M45421&;rQ:%RK2H6u8%45QG321QDrQ;%RO2QH:%S021Q1%85QK315QHrQ<%S32QF>+@%S5221%=5R041:QMrQ=rQ2%S921D+S8%S;221%C5R651@R3rQ>%S>2QBI%R:4R921HrQ?%SA2:QB+1%J5R=32G1&ErQ@%211rQA+QWQWH+Q<%SJ221u4%Q35RF521S;rQB+QD%SO271+UN%Q85RK4261'4'=&HvQ4rQE+ZXY@%U63UB1U4/01UBrQDrQC%8576321r1+QTc]@%U=3UI1U;/01UI&?rQ9rQ8%39:G2OQ41R2R7R=%A5@851:%C3S@:1%UE3V3Q5UC%UH2;1+ZXf4%UH3V41UF/01V4%UM3V541+:%UL3V:1UJ%UO2B1%U02Q9QC%UJ2V;1%V33V;31+;%V23V@1V0%V52H1%UO2V@Q6%V83V@21+<%V73VE1V5%V:2M1%V42VETJ%V=3VE21%VH1VI&>%11Q2r3r2%VB221rQG%VD213%VF3VN31p071pRJ:1%U42<1%U52B1%U62H1%U72O1%U82Q61qRNW51%QL2W61p0QN1p0R41p0R;1p0R?1p0RD1p0RH1p0RO1p0S51p0S:1p0S@1p0SH1p0SN1p0T51p0T<1p0TC1p0TI1p0TL1p0TN1p0U61p0U>1p0U?1p0U@1p0UA1p0UF1p0UM1p0V51p0V71p0V:1p0V>1p0VF1p0VJ1p0W31p0W91p0W?1p0WG1pRBX41pRDX51pR>X61pR@X71pS<X81pR8X91pS@X:1pR<X;1pS>X<1pS2X=1pRHX>1pRFX?1pR6X@1pS4XA1pS0XC1pDXD1pRLXJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 3%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 5%nat 0%nat).
Variable nd : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 6%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 7%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 8%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 9%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 10%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 11%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 12%nat 0%nat).
Variable mc : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 13%nat 0%nat).
Variable mb : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 14%nat 0%nat).
Variable mr : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 15%nat 0%nat).
Variable ml : ltac:(sec_ty2 constr:(SEC_T_art_alloc_d2_large_fn) 16%nat 0%nat).
Lemma art_alloc_d2_large_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_d2_large_fn) 17%nat 0%nat).
Proof using Type regs M rom sp ab n nd rz tp key tsd ctx t mc mb mr ml.
intros H2 H4 H9 H19 H20 Hsp Hsp' IMG Hn Hnd Hnd' Hub Hmc Hmb Hmr Hml
W TSD Ht Ht' Timg A1 A2 A3 A4 A5 Cmc Cmb Cmr Cml Wts Ccf L Cmax Cfb.
pose proof TSD as (_ & _ & _ & _ & _ & R).
pose proof L as (G48 & Csb & G50 & Cmb0 & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
unfold art_d2_large_mem.
eexists. split; [|split; [|split; [|split; [|split]]]].
- stepn (ltac:(oF' 0x52130%Z)) (ltac:(oD' 0x52130%Z)).
zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
assert (Wts' : wrA X (t + 2800) 112) by (repeat apply wr_Wn; exact Wts) end.
zld (ltac:(oF' 0x52134%Z)) (ltac:(oD' 0x52134%Z)) (t + 2800 + 16) Cmr'.
zld (ltac:(oF' 0x52138%Z)) (ltac:(oD' 0x52138%Z)) (t + 2800) Cmc'.
zld (ltac:(oF' 0x5213c%Z)) (ltac:(oD' 0x5213c%Z)) (t + 2800 + 8) Cmb'.
zstep (ltac:(oF' 0x52140%Z)) (ltac:(oD' 0x52140%Z)). zstep (ltac:(oF' 0x52144%Z)) (ltac:(oD' 0x52144%Z)). zstep (ltac:(oF' 0x52148%Z)) (ltac:(oD' 0x52148%Z)). zstep (ltac:(oF' 0x5214c%Z)) (ltac:(oD' 0x5214c%Z)). zstep (ltac:(oF' 0x52150%Z)) (ltac:(oD' 0x52150%Z)). zstep (ltac:(oF' 0x52154%Z)) (ltac:(oD' 0x52154%Z)).
zsd (ltac:(oF' 0x52158%Z)) (ltac:(oD' 0x52158%Z)) (t + 2800) (mc + 1) ltac:(rewok Wts').
zsd (ltac:(oF' 0x5215c%Z)) (ltac:(oD' 0x5215c%Z)) (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
zsd (ltac:(oF' 0x52160%Z)) (ltac:(oD' 0x52160%Z)) (t + 2800 + 16) (mr + (nd - n)) ltac:(rewok Wts').
zbft (ltac:(oF' 0x52164%Z)) (ltac:(oD' 0x52164%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cml' : cellA X (t + 2800 + 104) 8 ml) by (unfold apart in *; recell Cml) end.
zld (ltac:(oF' 0x52168%Z)) (ltac:(oD' 0x52168%Z)) (t + 2800 + 104) Cml'.
zstep (ltac:(oF' 0x5216c%Z)) (ltac:(oD' 0x5216c%Z)).
zsd (ltac:(oF' 0x52170%Z)) (ltac:(oD' 0x52170%Z)) (t + 2800 + 104) (ml + 1) ltac:(rewok Wts').
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
assert (G40' : cellA X 0x132630 8 0x1384f8) by (unfold apart in *; recell G40);
assert (Cmax' : cellA X (0x1384f8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
assert (G68' : cellA X 0x132658 8 0x134648) by (unfold apart in *; recell G68);
assert (Crm' : cellA X 0x134648 8 0x124db0) by (unfold apart in *; recell Crm);
assert (Cfb' : cellA X (0x1384f8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
zld (ltac:(oF' 0x52174%Z)) (ltac:(oD' 0x52174%Z)) (sp + 8) Ccf'.
zbtk (ltac:(oF' 0x52178%Z)) (ltac:(oD' 0x52178%Z)).
zstep (ltac:(oF' 0x52290%Z)) (ltac:(oD' 0x52290%Z)). zld (ltac:(oF' 0x52294%Z)) (ltac:(oD' 0x52294%Z)) 0x132630 G40'.
zlw (ltac:(oF' 0x52298%Z)) (ltac:(oD' 0x52298%Z)) (0x1384f8 + 44) Cmax'.
zbft (ltac:(oF' 0x5229c%Z)) (ltac:(oD' 0x5229c%Z)).
zstep (ltac:(oF' 0x522a0%Z)) (ltac:(oD' 0x522a0%Z)).
zbft (ltac:(oF' 0x522a4%Z)) (ltac:(oD' 0x522a4%Z)).
zstep (ltac:(oF' 0x522a8%Z)) (ltac:(oD' 0x522a8%Z)).
zstep (ltac:(oF' 0x522ac%Z)) (ltac:(oD' 0x522ac%Z)). zld (ltac:(oF' 0x522b0%Z)) (ltac:(oD' 0x522b0%Z)) 0x132658 G68'. zld (ltac:(oF' 0x522b4%Z)) (ltac:(oD' 0x522b4%Z)) 0x134648 Crm'.
zlw (ltac:(oF' 0x522b8%Z)) (ltac:(oD' 0x522b8%Z)) (0x1384f8 + 52) Cfb'.
zstep (ltac:(oF' 0x522bc%Z)) (ltac:(oD' 0x522bc%Z)).
stepjr (ltac:(oF' 0x522c0%Z)) (ltac:(oD' 0x522c0%Z)) (0x124db0 : bv 64)%bv ltac:(gres; bveq).
apply mst_refl.
- gres. apply bv_eq. reflexivity.
- kept_solve.
- kept_solve.
- kept_solve.
- intros r Hr. unfold art_d2_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
End SE.
End FPX.
