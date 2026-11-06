(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtRzLog JbtAllocA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocSecA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7art_tsd"; "8getr"; "8mkst"; "8regupd"]; ["9loaded_segments"; ":add"; ":div"; ":le"; ":lt"; ":max"; ":mul"; ":pow"; ":sub"; "0ctx"; "0fx"; "0ia"; "0key"; "0n"; "0r"; "0regs"]; ["0rom"; "0rs"; "0rz"; "0sp"; ";BV"; ";Z_to_bv"; ";bv"; "0t"; "0tp"; "0tsd"]]).
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
Local Abbreviation SEC_T_art_alloc_a3_sec_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocSecA "X:&5y5'Q6yR0%211%5241'0y8%611%311p061'4'3&=r>(Q4+2(1%33A21%6251&Q5r;%22C1%;3C41r?+4%;3I19%>231r6%92J1%B3J31r@+8%B3Q01@%E231%?2Q03%H3Q021rA+:%H3Q61F%K231&Er<%221;%H2Q91%Q13Q951rB+B%Q13Q?1O%Q4231%Q63Q>1?rC+C%Q63QD1Q4%Q9231r=%Q42QE1%Q=3QE31rD+D%Q=3QK1Q;%Q@231+RPP0%Q;2QL1%QD3QL31rE+E%QD3R21QB%QG231%QA2R2Q6%QJ3R221rF+F%QJ3R81QH%QM231%QG2R8M%R03R821rG+J%R03R>1QN%R3231&A+QoO%22Q01%R02RA1%R93RA51&C+@%221G&D&G+R0%22R<1%42F1+TP0%921H%?2C2+Vb\P0%<221%B22<rI%?221'2+1rH%C221+Q7%A2RK1%C241%7241z%I217+7%K291%<231&F&BrJ%R=21RF%Q6217%421RH%621RI%S>3S?B1%Q12S;6%92Q51%SA3SBE1%Q=29J%Q62R11&:&@rQ1&HrO%221Q>%64541Q?&9rQ2+Sa0%QI261u8+Q8%QC2SM1%75=6431&<rQ3rK%3621MQ>Q:R5&8%A24QMrM+RH%D221%544R11SHrQ4%G21R3rL%Q92SL7%R<221%;44R71SNrQ5%M21R9+TH%RA271%@43R<1T3';&>vJrQ9+ZXS8%TJ3U61TH/01U6rQ8rQ7%8576321&?%U03U>R8TN+ZXZD%U23U>1U0/01U>%53<41rQ6%U12UB1%833U41%U32UDR9%:32TG1+9%U;3UI1U9%U72UHQ2%>3421%U92UJN%@32TG1+;%UA3UO1U?+V@%SA2Q71%U?2V01%F3641+<%UG3V51UE%SF2QOR5%SG21R6%UE2V61%L3641+=%UM3V;1UK%O331U:%Q031TI5%UK2V<R=%Q232TD1+H%V33VA1V1%R@2SGUC%V02VA1%Q73531%V22VCQK%Q932T81+Zi`<%V:3VF1V8/01VF&7%RI2Q8UL+ZXYH%34RCQC21%QJ5QI851QC%QL3ROQC1p0QN1p0R41p0R;1p0SK1p0RC1p0RH1p0S11p0S91p0S<1p0S@1p0SI1p0SO1p0T81p0T<1p0T@1p0TC1p0TI1p0TM1p0U71p0U>1p0UE1p0UM1p0V51p0V;1p0VE1p0VL1p0W41pR@WA1pQDWB1pRDWC1pQJWD1pRBWE1pR6WF1pR4WG1pQNWH1pQLWI1pQHWJ1pR8WK1pR2WM1p>WN1pR0X41")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_sec_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_sec_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_sec_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_sec_fn) 3%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_sec_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_sec_fn) 5%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_sec_fn) 6%nat 0%nat).
Lemma art_alloc_a3_sec_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_a3_sec_fn) 7%nat 0%nat).
Proof using Type regs M rom sp ia n r.
intros rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hsec W Cmax TSD Ht A1 A2 A3.
pose proof TSD as (_ & _ & _ & _ & _ & R).
assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
assert (Hrshi : rs <= n + 7 \/ rs = 8). { subst rs. pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
zstep (ltac:(oF' 0x52068%Z)) (ltac:(oD' 0x52068%Z)). zstep (ltac:(oF' 0x5206c%Z)) (ltac:(oD' 0x5206c%Z)). zstep (ltac:(oF' 0x52070%Z)) (ltac:(oD' 0x52070%Z)). zstep (ltac:(oF' 0x52074%Z)) (ltac:(oD' 0x52074%Z)). zstep (ltac:(oF' 0x52078%Z)) (ltac:(oD' 0x52078%Z)).
stepn (ltac:(oF' 0x5207c%Z)) (ltac:(oD' 0x5207c%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
zstep (ltac:(oF' 0x52080%Z)) (ltac:(oD' 0x52080%Z)). zstep (ltac:(oF' 0x52084%Z)) (ltac:(oD' 0x52084%Z)).
stepn (ltac:(oF' 0x52088%Z)) (ltac:(oD' 0x52088%Z)). rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
zbft (ltac:(oF' 0x5208c%Z)) (ltac:(oD' 0x5208c%Z)).
zstep (ltac:(oF' 0x52090%Z)) (ltac:(oD' 0x52090%Z)). zstep (ltac:(oF' 0x52094%Z)) (ltac:(oD' 0x52094%Z)). zstep (ltac:(oF' 0x52098%Z)) (ltac:(oD' 0x52098%Z)).
stepn (ltac:(oF' 0x5209c%Z)) (ltac:(oD' 0x5209c%Z)). rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
zstep (ltac:(oF' 0x520a0%Z)) (ltac:(oD' 0x520a0%Z)). zstep (ltac:(oF' 0x520a4%Z)) (ltac:(oD' 0x520a4%Z)). zstep (ltac:(oF' 0x520a8%Z)) (ltac:(oD' 0x520a8%Z)). zstep (ltac:(oF' 0x520ac%Z)) (ltac:(oD' 0x520ac%Z)). zstep (ltac:(oF' 0x520b0%Z)) (ltac:(oD' 0x520b0%Z)). zstep (ltac:(oF' 0x520b4%Z)) (ltac:(oD' 0x520b4%Z)).
zstep (ltac:(oF' 0x520b8%Z)) (ltac:(oD' 0x520b8%Z)).
stepn (ltac:(oF' 0x520bc%Z)) (ltac:(oD' 0x520bc%Z)). rwH. rewrite art_zb_and by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small rz) by lia.
zstep (ltac:(oF' 0x520c0%Z)) (ltac:(oD' 0x520c0%Z)). zstep (ltac:(oF' 0x520c4%Z)) (ltac:(oD' 0x520c4%Z)).
zbft (ltac:(oF' 0x520c8%Z)) (ltac:(oD' 0x520c8%Z)). zbft (ltac:(oF' 0x520cc%Z)) (ltac:(oD' 0x520cc%Z)).
zld (ltac:(oF' 0x520d0%Z)) (ltac:(oD' 0x520d0%Z)) (ia + 3616) Cmax.
zbtk (ltac:(oF' 0x520d4%Z)) (ltac:(oD' 0x520d4%Z)).
stepn (ltac:(oF' 0x52134%Z)) (ltac:(oD' 0x52134%Z)).
zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
zbft (ltac:(oF' 0x5213c%Z)) (ltac:(oD' 0x5213c%Z)) || (zstep (ltac:(oF' 0x52138%Z)) (ltac:(oD' 0x52138%Z)); zbft (ltac:(oF' 0x5213c%Z)) (ltac:(oD' 0x5213c%Z))).
zstep (ltac:(oF' 0x52140%Z)) (ltac:(oD' 0x52140%Z)). zstep (ltac:(oF' 0x52144%Z)) (ltac:(oD' 0x52144%Z)). zstep (ltac:(oF' 0x52148%Z)) (ltac:(oD' 0x52148%Z)). zstep (ltac:(oF' 0x5214c%Z)) (ltac:(oD' 0x5214c%Z)).
stepn (ltac:(oF' 0x52150%Z)) (ltac:(oD' 0x52150%Z)).
zret.
Qed.
End SE.
End FPX.
