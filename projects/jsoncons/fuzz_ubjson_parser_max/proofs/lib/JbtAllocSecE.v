(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtAllocE.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocSecE () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_layout"; "9getr"; "9mkst"]; ["9regupd"; ":loaded_segments"; ";add"; ";land"; ";le"; ";lt"; ";modulo"; ";pow"; ";sub"; "0ab"; "0b1"; "0fx"; "0loff"; "0n"; "0raw0"; "0regs"]; ["0rom"; "0rz"; "0s0v"; "0s0x"; "0s10v"; "0s11v"; "0s1v"; "0s2v"; "0s3v"; "0s4v"; "0s5v"; "0s6v"; "0s7v"; "0s8v"; "0s9v"; "0sp"]; ["<BV"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0tp"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_e32_sec_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocSecE "\A&5y5'QByR0%211%5241'0y8%611%311p061'4'3&>rH(Q@+2(1%33A21%6251&QArD%22C1%;3C41rI+4%;3I19%>231r@%92J1%B3J31rJ+8%B3Q01@%E231r?%@2Q11%I3Q131'2&Dz%221=&E&G+R0%22M1%42B1%9261rL+9%Q33QA1Q1%Q6231rF%Q12QB1%Q:3QB31rM+B%Q:3QH1Q8%Q=231%Q72QHQ=%Q@3QH21rN+D%Q@3QN1Q>%QC231&BrG%22Q;1%Q@2R11%QI3R151rO+E%QI3R71QG%QL231&H%:2Q<QM+@%3221%QJ2R;1%R33R;61+Q0%Q:21Q1+T0%B2L1%Q:21Q7+Vb\P0%E216%Q@21J%QA23K%H2CQ2+Q?%Q@2R;1%QB231&FrQ0%221C%RD3RE1QH+1%QK214+Q8%QI2RD1%QK271%R0241%R02QOQ1+X0%QO2Q31%R4231+TP0%Q;2>1%R321R0%R72R6@rQ2rQ1%Q@221%QA21RI%R921R6&<rQ9%211&9&ArQ<+QVdP0u8rQ3%6554321rQ=rQ5rQ4%R0221u4%<5;521RK&8rQ6%R5217rQ:rQ8%R8221%R021QN%745SB1QOrQ?rQ;%R=21I%R521R3%R?21Q?u1%K5J621:&:rQ@%RD2L>%R<21R:%44O31R;rQArQ>%R@21R:%84Q331R;&=rQB%211rQC+QiiX0%Q:5Q921Q6SI%S12>9%RI21RG%RJ2<RD+U0%Q243RJ21%RM2:RG%Q44@RL13rQF+SH%S:2<1&QCrQD%22U;1%QH5QG64QD1rQG+S@%SA251%QL5QK31QHQJrQHrQE+S8%SF221%R15R041QMQOrQI+S0%SJ2B1%R55R431R1R3rQJ+RH%SN2?1%R95R831R5R7rQK+R@%T22?1%R=5R<31R9R;rQL+R8%T62>1%RA5R@31R=R?rQM%T92=TN%RD5RC21R@RBrQN+QH%T=2=1%RH5RG31RDRFrQO+Q@%TA2=1%RL5RK31RHRJrR0%TD2<SB%RO5RN21RKRMrR1%TG2<T8%S25S121RNS0rR2+H%TK2<1%S65S531S2S4%UG2T>E+RP0%UI2G1%UK231%T52FTF%VG3VH1UKrR5%RB4S=1>TIrR6+RPjH+\hkdfgWVVmUeI%SB5SA32S>1';&?vKrR8+ZY\D%W03W<1VN/01W<rR7%756521<&@%W53WCTCW3%2381ArR4%UF21U5%W42WE1%634W71%W62WGQE%832VJ1%W82WIQK%:32V;1+:%W@3WN1W>rR3%V021Q:%W>2WO1%@3641+;%WF3X41WD%WB2X3Q<%D3421+<%WJ3X81WH%WF2X7W2%H3421+=%WN3X<1WL%V=2>V2%WK2X<1%M3531%WM2X>RD%O32VI1+C%X53XC1X3%X12XBRL%Q33421%X32XDS3%Q532VI1%X52XFS9%Q732VB1+F%X=3XK1X;%X92XJSD%Q;3421+G%XA3XO1X?%X=2XNS<%Q?3421%XD3Y2R8XB%X@2Y1SG%QB3321+I%XH3Y61XF%XD2Y5T9%QF3421+J%XL3Y:1XJ%XH2Y9T?%QJ3421+K%Y03Y>1XN%XL2Y=TH%QN3421&7+?%W:2QC1&C+WC%22S31%64U7R741%W?2QHW=%84U921Y:%WJ2QKXK%:4V1213%;4V21QMRE%WD2R8XN+ZY_8%>4V5321%WG2R;WE%@4V721SI%WI2R=S8%B4V921S:%WK2R?WE%D4V;21R6%RL5RKFS31S1%RN3V@RF1p0S01p0S51p0S81p0S;1p0S@1p0SE1p0SI1p0SM1p0T21p0T71p0T;1p0T@1p0TE1p0TJ1p0TO1p0U51p0U:1p0UB1p0UE1p0UK1p0UO1p0V31p0V81p0V>1p0VF1p0VO1p0W61p0W>1p0WB1p0WH1p0WJ1p0X11p0WO1p0X41p0X;1p0X@1p0XE1p0XG1p0XK1p0XO1p0Y21p0Y=1p0YG1p0YN1p0Z61p0ZA1p0ZI1p0[11pR<[>1pR:[?1pRN[@1pRL[A1pRJ[B1pRH[C1pRF[D1pRD[E1pRB[F1pR@[G1pR>[H1pR6[I1pR8[J1pQJ[K1pS:[L1pQF[M1pR4[N1pQL[O1pQD\01pS0\11pQN\91pR2\41p>\51pR0\;1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 4%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 6%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 7%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 8%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 9%nat 0%nat).
Variable loff : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 10%nat 0%nat).
Variable s0x : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 11%nat 0%nat).
Variable s0v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 12%nat 0%nat).
Variable s1v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 13%nat 0%nat).
Variable s2v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 14%nat 0%nat).
Variable s3v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 15%nat 0%nat).
Variable s4v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 16%nat 0%nat).
Variable s5v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 17%nat 0%nat).
Variable s6v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 18%nat 0%nat).
Variable s7v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 19%nat 0%nat).
Variable s8v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 20%nat 0%nat).
Variable s9v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 21%nat 0%nat).
Variable s10v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 22%nat 0%nat).
Variable s11v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_sec_fn) 23%nat 0%nat).
Lemma art_alloc_e32_sec_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_e32_sec_fn) 24%nat 0%nat).
Proof using Type regs M rom raw0 sp ab n rz b1 tp loff s0x s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v.
intros H2 H4 H8 Hs0x H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
intros Hrz Hrz16 Wab Cmag. unfold kHighMemBeg in *.
pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
stepn (ltac:(oF' 0x52594%Z)) (ltac:(oD' 0x52594%Z)).
zcall (art_lsan_off_fn _ _ _ _ tp loff).
zlbu (ltac:(oF' 0x52598%Z)) (ltac:(oD' 0x52598%Z)) (ab + rz - 16 + 1) Cb1.
zstep (ltac:(oF' 0x5259c%Z)) (ltac:(oD' 0x5259c%Z)). zstep (ltac:(oF' 0x525a0%Z)) (ltac:(oD' 0x525a0%Z)).
stepn (ltac:(oF' 0x525a4%Z)) (ltac:(oD' 0x525a4%Z)). rwH. rewrite art_zb_andi by lia.
stepn (ltac:(oF' 0x525a8%Z)) (ltac:(oD' 0x525a8%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
zstep (ltac:(oF' 0x525ac%Z)) (ltac:(oD' 0x525ac%Z)).
zsb (ltac:(oF' 0x525b0%Z)) (ltac:(oD' 0x525b0%Z)) (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
stepfence (ltac:(oF' 0x525b4%Z)) (ltac:(oD' 0x525b4%Z)).
zsb (ltac:(oF' 0x525b8%Z)) (ltac:(oD' 0x525b8%Z)) (ab + rz - 16) 2 ltac:(rewok Wh).
zbft (ltac:(oF' 0x525bc%Z)) (ltac:(oD' 0x525bc%Z)).
zstep (ltac:(oF' 0x525c0%Z)) (ltac:(oD' 0x525c0%Z)).
zbft (ltac:(oF' 0x525c4%Z)) (ltac:(oD' 0x525c4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmag' : cellA X 0x10358 8 0xcc6e96b9cc6e96b9) by (recell Cmag) end.
zstep (ltac:(oF' 0x525c8%Z)) (ltac:(oD' 0x525c8%Z)). zld (ltac:(oF' 0x525cc%Z)) (ltac:(oD' 0x525cc%Z)) 0x10358 Cmag'.
zsd (ltac:(oF' 0x525d0%Z)) (ltac:(oD' 0x525d0%Z)) (ab + 8) (ab + rz - 16) ltac:(rewok Wab).
stepfence (ltac:(oF' 0x525d4%Z)) (ltac:(oD' 0x525d4%Z)).
zsd (ltac:(oF' 0x525d8%Z)) (ltac:(oD' 0x525d8%Z)) ab 0xcc6e96b9cc6e96b9 ltac:(rewok Wab).
zstep (ltac:(oF' 0x525dc%Z)) (ltac:(oD' 0x525dc%Z)). zstep (ltac:(oF' 0x525e0%Z)) (ltac:(oD' 0x525e0%Z)).
stepn (ltac:(oF' 0x525e4%Z)) (ltac:(oD' 0x525e4%Z)).
zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
zstep (ltac:(oF' 0x525e8%Z)) (ltac:(oD' 0x525e8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (C120 : cellA X (sp + 120) 8 (U raw0)) by (recell F120);
assert (C112 : cellA X (sp + 112) 8 s0v) by (recell F112);
assert (C104 : cellA X (sp + 104) 8 s1v) by (recell F104);
assert (C96 : cellA X (sp + 96) 8 s2v) by (recell F96);
assert (C88 : cellA X (sp + 88) 8 s3v) by (recell F88);
assert (C80 : cellA X (sp + 80) 8 s4v) by (recell F80);
assert (C72 : cellA X (sp + 72) 8 s5v) by (recell F72);
assert (C64 : cellA X (sp + 64) 8 s6v) by (recell F64);
assert (C56 : cellA X (sp + 56) 8 s7v) by (recell F56);
assert (C48 : cellA X (sp + 48) 8 s8v) by (recell F48);
assert (C40 : cellA X (sp + 40) 8 s9v) by (recell F40);
assert (C32 : cellA X (sp + 32) 8 s10v) by (recell F32);
assert (C24 : cellA X (sp + 24) 8 s11v) by (recell F24); idtac end.
zld (ltac:(oF' 0x525ec%Z)) (ltac:(oD' 0x525ec%Z)) (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x525f0%Z)) (ltac:(oD' 0x525f0%Z)) (sp + 112) C112.
zld (ltac:(oF' 0x525f4%Z)) (ltac:(oD' 0x525f4%Z)) (sp + 104) C104.
zld (ltac:(oF' 0x525f8%Z)) (ltac:(oD' 0x525f8%Z)) (sp + 96) C96.
zld (ltac:(oF' 0x525fc%Z)) (ltac:(oD' 0x525fc%Z)) (sp + 88) C88.
zld (ltac:(oF' 0x52600%Z)) (ltac:(oD' 0x52600%Z)) (sp + 80) C80.
zld (ltac:(oF' 0x52604%Z)) (ltac:(oD' 0x52604%Z)) (sp + 72) C72.
zld (ltac:(oF' 0x52608%Z)) (ltac:(oD' 0x52608%Z)) (sp + 64) C64.
zld (ltac:(oF' 0x5260c%Z)) (ltac:(oD' 0x5260c%Z)) (sp + 56) C56.
zld (ltac:(oF' 0x52610%Z)) (ltac:(oD' 0x52610%Z)) (sp + 48) C48.
zld (ltac:(oF' 0x52614%Z)) (ltac:(oD' 0x52614%Z)) (sp + 40) C40.
zld (ltac:(oF' 0x52618%Z)) (ltac:(oD' 0x52618%Z)) (sp + 32) C32.
zld (ltac:(oF' 0x5261c%Z)) (ltac:(oD' 0x5261c%Z)) (sp + 24) C24.
zstep (ltac:(oF' 0x52620%Z)) (ltac:(oD' 0x52620%Z)).
stepret (ltac:(oF' 0x52624%Z)) (ltac:(oD' 0x52624%Z)) raw0 ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
End FPX.
