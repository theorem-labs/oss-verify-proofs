(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatRzLog.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAllocA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRzLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6rz_log"; "7msteps"; "8art_alloc_memA1"]; ["8art_alloc_rodata"; "9art_tsd"; ":art_rz_rodata"; ";getr"; ";mkst"; ";regupd"; ";v_sllw"; "<loaded_segments"; "=add"; "=div"; "=le"; "=lt"; "=max"; "=mul"; "=pow"; "=sub"]; ["0ctx"; "0fx"; "0ia"; "0k"; "0key"; "0n"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0rs"; "0rz"; "0sp"; ">BV"; ">Z_to_bv"]; [">bv"; "0stk"; "0t"; "0tp"; "0tsd"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_alloc_rodata (M : word -> option byte) : Prop :=
cellA M 0x10418 8 0x218a392cd3d5dbf /\ cellA M 0x10494 1 3 /\ cellA M 0x10358 8 0xcc6e96b9cc6e96b9.
Definition art_alloc_memA1 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
(Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 16).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_a1_fn := (ltac2:(TCodec.tc2 tcn__JatAllocA "V@&7y5'Q@yR0%211%5241'0y8%611%311p061'6'3&Cr8(Q>+1(1%33A21%6251r5%93A21r9+2%93G17%<231&Q?%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;r<+<%J3Q81H%M231+8%B2Q91%Q13Q931r=+=%Q13Q?1O%Q4231r6%I2Q@1%Q83Q@31r>+>%Q83QF1Q6%Q;231%O2QFQ9%Q>3QF21r?+?%Q>3QL1Q<%QA231%QC3QK16&J+X0%221K&K&N+R0%22Q?1%42I1+TP0%921K&H%12F3%9216'2%>2QNQ0%2218%@2R0E+Q8%>2QK1%@2H1%7241&<&GrE&OrB%221I%64541J+VbTP0%C21LrC%O221&@rG%211&;rH+QW^^Hu1%45A321RGrI+Qgck2z%85E3251'>&DvQ1rK+ZVo4%S23S>1S0/01S>rJ%756521<&E+ZWR0%S83SD1S6/01SD%43:S71+T0%Q32J1%S22SI1%834S51%S?3SMRCS=%:321RC+9%SB3T01S@%=331R9+QA%S:2T11%@33S61+@%S=2T41%C33S41+RQT@%S@2T71%F33S21%QD2R6S1%SC2T:1%I33RN1+B%T13T?1SO%L331S5+E%T43TB1T2%SJ2TAQM%Q03421+F%T83TF1T6rF%SO2TF1%Q53531+G%T=3TK1T;rD%T42TK1%Q:3531+I%TB3U01T@+7%T92U01%Q?3531+J%TG3U51TE+QoO%RN2@1%T?2U61%QE3641+K%TM3U;1TK%QH331SD+ZWSL%U03U<1TN/01U<&?%14QORAR>R3%R65R5631R;%R83RNR01p0R:1p0R?1p0RE1p0RI1p0RN1p0S61p0S<1p0S@1p0SD1p0SG1p0SM1p0T11p0T71p0T>1p0TF1p0TN1p0U41p0U:1p0UB1pS4UM1pR<UN1pR6UO1pRLV01pR@V81pRFV31pBV41pRBV:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_fn) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_fn) 6%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a1_fn) 7%nat 0%nat).
Lemma art_alloc_a1_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_a1_fn) 8%nat 0%nat).
Proof using Type regs M rom raw sp ia n stk.
intros H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & R2 & R3) Ci Cr.
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
assert (R2' : cellA Mf 0x10494 1 3) by (unfold Mf; unfold apart in *; recell R2).
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
zlbu (ltac:(oF' 0x51cc8%Z)) (ltac:(oD' 0x51cc8%Z)) 0x10494 R2'.
zstep (ltac:(oF' 0x51ccc%Z)) (ltac:(oD' 0x51ccc%Z)). zstep (ltac:(oF' 0x51cd0%Z)) (ltac:(oD' 0x51cd0%Z)). zstep (ltac:(oF' 0x51cd4%Z)) (ltac:(oD' 0x51cd4%Z)). zstep (ltac:(oF' 0x51cd8%Z)) (ltac:(oD' 0x51cd8%Z)).
zbtk (ltac:(oF' 0x51cdc%Z)) (ltac:(oD' 0x51cdc%Z)).
zstep (ltac:(oF' 0x51c5c%Z)) (ltac:(oD' 0x51c5c%Z)). zstep (ltac:(oF' 0x51c60%Z)) (ltac:(oD' 0x51c60%Z)). zstep (ltac:(oF' 0x51c64%Z)) (ltac:(oD' 0x51c64%Z)).
zbft (ltac:(oF' 0x51c68%Z)) (ltac:(oD' 0x51c68%Z)).
zstep (ltac:(oF' 0x51c6c%Z)) (ltac:(oD' 0x51c6c%Z)). zstep (ltac:(oF' 0x51c70%Z)) (ltac:(oD' 0x51c70%Z)).
zsd (ltac:(oF' 0x51c74%Z)) (ltac:(oD' 0x51c74%Z)) (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
zsd (ltac:(oF' 0x51c78%Z)) (ltac:(oD' 0x51c78%Z)) (sp - 128 + 16) 16 ltac:(unfold Mf; rewok W).
unfold Mf, art_alloc_memA1. zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_alloc_ladder := (ltac2:(TCodec.tc2 tcn__JatAllocA "RL&7y5'Q@yR0%211%5241'0y8%611%311p061'6'3&Cr4(Q>+:(1%33A21%6251&Q?+QA%22C1%;3C41r5+E%;3I19%>231r2%92J1%B3J31'2&J+1r3%3221&K&N+2+Q8%3221%5271%;271'4'>&G&DvQ1r8+ZWSL%Q33Q?1Q1/01Q?r7r6%8576321r1+ZWZ@%Q:3QF1Q8/01QF%=5<4176%@3?61+C%Q?3QM1Q=%QB281&=%11Q9%Q>2QO1%QG3QO41%R21R3&5%QJ32?QD%211%QL34Q<:%411%QM2QLQ8r;%QO21Q:%R13R931p051p081pR><1%QB2>1%QC2F1qRDR>1%Q92R?1p0Q;1p0QH1p0R01pR<R=1pRFR?1pBR@1pRBRF1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_ladder) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_ladder) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_ladder) 2%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_ladder) 3%nat 0%nat).
Lemma art_alloc_ladder : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_ladder) 4%nat 0%nat).
Proof using Type regs M rom n.
intros H10 H21 Hn.
unfold AsanTab.rz_log.
destruct (Z.le_gt_cases n 48) as [C0|C0'].
{ eexists. split; [|split]; [ zbft (ltac:(oF' 0x51c7c%Z)) (ltac:(oD' 0x51c7c%Z)); zstep (ltac:(oF' 0x51c80%Z)) (ltac:(oD' 0x51c80%Z)); stepn (ltac:(oF' 0x51c84%Z)) (ltac:(oD' 0x51c84%Z)); apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
destruct (Z.le_gt_cases n 96) as [C1|C1'].
{ eexists. split; [|split]; [ zbtk (ltac:(oF' 0x51c7c%Z)) (ltac:(oD' 0x51c7c%Z)); zstep (ltac:(oF' 0x51ce4%Z)) (ltac:(oD' 0x51ce4%Z)); zbft (ltac:(oF' 0x51ce8%Z)) (ltac:(oD' 0x51ce8%Z)); zstep (ltac:(oF' 0x51cec%Z)) (ltac:(oD' 0x51cec%Z)); stepn (ltac:(oF' 0x51cf0%Z)) (ltac:(oD' 0x51cf0%Z)); apply mst_refl
| gres; zif; reflexivity | intros; kept_solve ]. }
destruct (Z.le_gt_cases n 448) as [C2|C2'].
{ eexists. split; [|split]; [ zbtk (ltac:(oF' 0x51c7c%Z)) (ltac:(oD' 0x51c7c%Z)); zstep (ltac:(oF' 0x51ce4%Z)) (ltac:(oD' 0x51ce4%Z)); zbtk (ltac:(oF' 0x51ce8%Z)) (ltac:(oD' 0x51ce8%Z)); zstep (ltac:(oF' 0x51cf4%Z)) (ltac:(oD' 0x51cf4%Z)); zbft (ltac:(oF' 0x51cf8%Z)) (ltac:(oD' 0x51cf8%Z)); zstep (ltac:(oF' 0x51cfc%Z)) (ltac:(oD' 0x51cfc%Z));
stepn (ltac:(oF' 0x51d00%Z)) (ltac:(oD' 0x51d00%Z)); apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
destruct (Z.le_gt_cases n 3968) as [C3|C3'].
{ eexists. split; [|split]; [ zbtk (ltac:(oF' 0x51c7c%Z)) (ltac:(oD' 0x51c7c%Z)); zstep (ltac:(oF' 0x51ce4%Z)) (ltac:(oD' 0x51ce4%Z)); zbtk (ltac:(oF' 0x51ce8%Z)) (ltac:(oD' 0x51ce8%Z)); zstep (ltac:(oF' 0x51cf4%Z)) (ltac:(oD' 0x51cf4%Z)); zbtk (ltac:(oF' 0x51cf8%Z)) (ltac:(oD' 0x51cf8%Z));
zstep (ltac:(oF' 0x51d04%Z)) (ltac:(oD' 0x51d04%Z)); zstep (ltac:(oF' 0x51d08%Z)) (ltac:(oD' 0x51d08%Z)); zbft (ltac:(oF' 0x51d0c%Z)) (ltac:(oD' 0x51d0c%Z)); zstep (ltac:(oF' 0x51d10%Z)) (ltac:(oD' 0x51d10%Z)); stepn (ltac:(oF' 0x51d14%Z)) (ltac:(oD' 0x51d14%Z)); apply mst_refl
| gres; zif; reflexivity | intros; kept_solve ]. }
destruct (Z.le_gt_cases n 16128) as [C4|C4'].
{ eexists. split; [|split]; [ zbtk (ltac:(oF' 0x51c7c%Z)) (ltac:(oD' 0x51c7c%Z)); zstep (ltac:(oF' 0x51ce4%Z)) (ltac:(oD' 0x51ce4%Z)); zbtk (ltac:(oF' 0x51ce8%Z)) (ltac:(oD' 0x51ce8%Z)); zstep (ltac:(oF' 0x51cf4%Z)) (ltac:(oD' 0x51cf4%Z)); zbtk (ltac:(oF' 0x51cf8%Z)) (ltac:(oD' 0x51cf8%Z));
zstep (ltac:(oF' 0x51d04%Z)) (ltac:(oD' 0x51d04%Z)); zstep (ltac:(oF' 0x51d08%Z)) (ltac:(oD' 0x51d08%Z)); zbtk (ltac:(oF' 0x51d0c%Z)) (ltac:(oD' 0x51d0c%Z)); zstep (ltac:(oF' 0x51d18%Z)) (ltac:(oD' 0x51d18%Z)); zstep (ltac:(oF' 0x51d1c%Z)) (ltac:(oD' 0x51d1c%Z)); zbft (ltac:(oF' 0x51d20%Z)) (ltac:(oD' 0x51d20%Z));
zstep (ltac:(oF' 0x51d24%Z)) (ltac:(oD' 0x51d24%Z)); stepn (ltac:(oF' 0x51d28%Z)) (ltac:(oD' 0x51d28%Z)); apply mst_refl
| gres; zif; reflexivity | intros; kept_solve ]. }
destruct (Z.le_gt_cases n 32256) as [C5|C5'].
{ eexists. split; [|split]; [ zbtk (ltac:(oF' 0x51c7c%Z)) (ltac:(oD' 0x51c7c%Z)); zstep (ltac:(oF' 0x51ce4%Z)) (ltac:(oD' 0x51ce4%Z)); zbtk (ltac:(oF' 0x51ce8%Z)) (ltac:(oD' 0x51ce8%Z)); zstep (ltac:(oF' 0x51cf4%Z)) (ltac:(oD' 0x51cf4%Z)); zbtk (ltac:(oF' 0x51cf8%Z)) (ltac:(oD' 0x51cf8%Z));
zstep (ltac:(oF' 0x51d04%Z)) (ltac:(oD' 0x51d04%Z)); zstep (ltac:(oF' 0x51d08%Z)) (ltac:(oD' 0x51d08%Z)); zbtk (ltac:(oF' 0x51d0c%Z)) (ltac:(oD' 0x51d0c%Z)); zstep (ltac:(oF' 0x51d18%Z)) (ltac:(oD' 0x51d18%Z)); zstep (ltac:(oF' 0x51d1c%Z)) (ltac:(oD' 0x51d1c%Z)); zbtk (ltac:(oF' 0x51d20%Z)) (ltac:(oD' 0x51d20%Z));
zstep (ltac:(oF' 0x51d2c%Z)) (ltac:(oD' 0x51d2c%Z)); zstep (ltac:(oF' 0x51d30%Z)) (ltac:(oD' 0x51d30%Z)); zbft (ltac:(oF' 0x51d34%Z)) (ltac:(oD' 0x51d34%Z)); zstep (ltac:(oF' 0x51d38%Z)) (ltac:(oD' 0x51d38%Z)); stepn (ltac:(oF' 0x51d3c%Z)) (ltac:(oD' 0x51d3c%Z)); apply mst_refl
| gres; zif; reflexivity | intros; kept_solve ]. }
eexists. split; [|split]; [ zbtk (ltac:(oF' 0x51c7c%Z)) (ltac:(oD' 0x51c7c%Z)); zstep (ltac:(oF' 0x51ce4%Z)) (ltac:(oD' 0x51ce4%Z)); zbtk (ltac:(oF' 0x51ce8%Z)) (ltac:(oD' 0x51ce8%Z)); zstep (ltac:(oF' 0x51cf4%Z)) (ltac:(oD' 0x51cf4%Z)); zbtk (ltac:(oF' 0x51cf8%Z)) (ltac:(oD' 0x51cf8%Z));
zstep (ltac:(oF' 0x51d04%Z)) (ltac:(oD' 0x51d04%Z)); zstep (ltac:(oF' 0x51d08%Z)) (ltac:(oD' 0x51d08%Z)); zbtk (ltac:(oF' 0x51d0c%Z)) (ltac:(oD' 0x51d0c%Z)); zstep (ltac:(oF' 0x51d18%Z)) (ltac:(oD' 0x51d18%Z)); zstep (ltac:(oF' 0x51d1c%Z)) (ltac:(oD' 0x51d1c%Z)); zbtk (ltac:(oF' 0x51d20%Z)) (ltac:(oD' 0x51d20%Z));
zstep (ltac:(oF' 0x51d2c%Z)) (ltac:(oD' 0x51d2c%Z)); zstep (ltac:(oF' 0x51d30%Z)) (ltac:(oD' 0x51d30%Z)); zbtk (ltac:(oF' 0x51d34%Z)) (ltac:(oD' 0x51d34%Z)); zstep (ltac:(oF' 0x51d40%Z)) (ltac:(oD' 0x51d40%Z)); zstep (ltac:(oF' 0x51d44%Z)) (ltac:(oD' 0x51d44%Z)); zstep (ltac:(oF' 0x51d48%Z)) (ltac:(oD' 0x51d48%Z));
zstep (ltac:(oF' 0x51d4c%Z)) (ltac:(oD' 0x51d4c%Z)); apply mst_refl
| gres | intros; kept_solve ].
destruct (Z.le_gt_cases n 64512) as [C6|C6']; zif; vals_lit; reflexivity.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_alloc_a2_fn := (ltac2:(TCodec.tc2 tcn__JatAllocA "TE&7y5'Q@yR0%211%5241'0y8%611%311p061'6'3&Cr5(Q>+2(1%33A21%6251&Q?r2%22C1%;3C41r6+J%;3I19%>231&H+QoO%2291%;2L1%D3L51&J+@r4%3221&K&N+R0%22H1%42K1+TP0%:21M%@2D2+VbTP0%=221&<&Gr:&Or8%221B%64541C%J29Dr9%G221&Br<%211&;r=+Sa8%Q32>1u2%55A421Or>r;+Sa:%Q9221+RP0%;5G5271'>&DvQ1r@+ZWZ@%QN3R:1QL/01R:r?%756521>&E+1%R43RB1R2+ZW[L%R63RB1R4/01RB%63<41%R42REK%832R71+9%R<3RJ1R:z%R92RJ1%=3531+:%RA3RO1R?+7%R>2RO1%B3531+;%RF3S41RD%E3314+<%RI3S71RG%RE2S65%I3421+=%RM3S;1RK%RI2S:Q7%M3421+>%S13S?1RO%Q03314+D%S43SB1S2+RPP0%S12SB1%Q53531+H%S93SG1S7+QooO%S62SG1%Q:3531&9u8+8%R=2R21+ZW[8%544QB21%64513Q>%QJ5QI8Q=1R1%QL3RDQD1p0QN1p0R51p0R<1p0R@1p0RD1p0RL1p0S01p0S31p0S91p0S>1p0SH1pR6T51pRLT61pRFT81pBT91pRBT?1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a2_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a2_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a2_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a2_fn) 3%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a2_fn) 4%nat 0%nat).
Lemma art_alloc_a2_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_a2_fn) 5%nat 0%nat).
Proof using Type regs M rom sp ia.
intros H2 H26 Hsp Hsp' Hia Hia' W IMG RO Cmin Cmax.
zlh (ltac:(oF' 0x51d50%Z)) (ltac:(oD' 0x51d50%Z)) (ia + 3624) Cmin.
stepfence (ltac:(oF' 0x51d54%Z)) (ltac:(oD' 0x51d54%Z)).
zstep (ltac:(oF' 0x51d58%Z)) (ltac:(oD' 0x51d58%Z)). zstep (ltac:(oF' 0x51d5c%Z)) (ltac:(oD' 0x51d5c%Z)). zstep (ltac:(oF' 0x51d60%Z)) (ltac:(oD' 0x51d60%Z)).
stepn (ltac:(oF' 0x51d64%Z)) (ltac:(oD' 0x51d64%Z)).
zcall (art_rz2log_16_fn _ _ _ sp _).
zstep (ltac:(oF' 0x51d68%Z)) (ltac:(oD' 0x51d68%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmax' : cellA X (ia + 3626) 2 2048) by (unfold apart in *; recell Cmax) end.
zlh (ltac:(oF' 0x51d6c%Z)) (ltac:(oD' 0x51d6c%Z)) (ia + 3626) Cmax'.
stepfence (ltac:(oF' 0x51d70%Z)) (ltac:(oD' 0x51d70%Z)).
zstep (ltac:(oF' 0x51d74%Z)) (ltac:(oD' 0x51d74%Z)).
stepn (ltac:(oF' 0x51d78%Z)) (ltac:(oD' 0x51d78%Z)).
zcall (art_rz2log_2048_fn _ _ _ sp _).
{ destruct RO as (R1 & R2 & R3). unfold art_rz_rodata. repeat split; recell R1 || recell R2 || recell R3. }
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_alloc_clamp := (ltac2:(TCodec.tc2 tcn__JatAllocA "SN&7y5'Q@yR0%211%5241'0y8%611%311p061'6'3&Cr5(Q>+9(1%33A21%6251&Q?z%22C1%;3C41r6+:%;3I19%>231+7%92J1%B3J31r7+C%B3Q01@%E231r3%@2Q11%I3Q131r8+E%I3Q71G%L231%F2Q7L%O3Q721'2&J+1%221G&K&N+2+Q8%3221%52M1%:271&=%11I%Q=3Q>Q11'4'>&G&DvQ1r<+ZW[L%QB3QN1Q@/01QNr;r:%8576321r1+ZW\H%QI3R51QG/01R5%=5<4176%@3?61%QO26QB&Lr9+8%3221%QM2R>1%R63R>61+;%R53RC1R3%R82?1%R22RC7%R;3RC21%R;2BQG%R52RFQC%R>3RF21%RI1RJ&5%RA32GR3%211r2%RD351<%511%RF37QOR1%711r4%RH2RG1r@%RJ213%RL3S431p061p091p0=1pS<A1%R12C1%R22G1%R32M1%R42Q51qRDS<1%QH2S=1p0QJ1p0QN1p0R:1p0RA1p0RI1p0S11pR>S>1pR<S?1pRFSA1pBSB1pRBSH1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_clamp) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_clamp) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_clamp) 2%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_clamp) 3%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_alloc_clamp) 4%nat 0%nat).
Lemma art_alloc_clamp : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_clamp) 5%nat 0%nat).
Proof using Type regs M rom n r.
intros H9 H10 H19 H21 Hn Hr.
pose proof (AsanTab.rz_log_range n) as Rr. rewrite <- Hr in Rr.
assert (CASES : r = 0 \/ (0 < r < 7) \/ r = 7) by lia.
assert (Rlo : 0 < r -> 49 <= n).
{ intros Hp. destruct (Z.le_gt_cases n 48) as [L|G]; [exfalso|lia]. subst r. unfold AsanTab.rz_log in Hp.
replace (n <=? 48) with true in Hp by (symmetry; apply Z.leb_le; lia). lia. }
assert (R7 : r = 7 -> 64513 <= n).
{ intros Hp. destruct (Z.le_gt_cases n 64512) as [L|G]; [exfalso|lia]. subst r. unfold AsanTab.rz_log in Hp.
repeat (lazymatch type of Hp with context [if ?c then _ else _] => destruct c eqn:?; [lia|] end).
repeat match goal with H : (_ <=? _) = false |- _ => apply Z.leb_gt in H; revert H end. lia. }
destruct CASES as [R0 | [RM | RS]].
- destruct (Z.le_gt_cases n 8) as [S|B].
+ eexists. split; [|split; [|split; [|split]]];
[ zbft (ltac:(oF' 0x51d7c%Z)) (ltac:(oD' 0x51d7c%Z)); zstep (ltac:(oF' 0x51d80%Z)) (ltac:(oD' 0x51d80%Z)); zbft (ltac:(oF' 0x51d84%Z)) (ltac:(oD' 0x51d84%Z)); zstep (ltac:(oF' 0x51d88%Z)) (ltac:(oD' 0x51d88%Z)); zstep (ltac:(oF' 0x51d8c%Z)) (ltac:(oD' 0x51d8c%Z)); zbft (ltac:(oF' 0x51d90%Z)) (ltac:(oD' 0x51d90%Z)); zstep (ltac:(oF' 0x51d94%Z)) (ltac:(oD' 0x51d94%Z)); apply mst_refl
| gres; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
+ eexists. split; [|split; [|split; [|split]]];
[ zbft (ltac:(oF' 0x51d7c%Z)) (ltac:(oD' 0x51d7c%Z)); zstep (ltac:(oF' 0x51d80%Z)) (ltac:(oD' 0x51d80%Z)); zbft (ltac:(oF' 0x51d84%Z)) (ltac:(oD' 0x51d84%Z)); zstep (ltac:(oF' 0x51d88%Z)) (ltac:(oD' 0x51d88%Z)); zstep (ltac:(oF' 0x51d8c%Z)) (ltac:(oD' 0x51d8c%Z)); zbtk (ltac:(oF' 0x51d90%Z)) (ltac:(oD' 0x51d90%Z)); apply mst_refl
| gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
- specialize (Rlo ltac:(lia)).
eexists. split; [|split; [|split; [|split]]];
[ zbtk (ltac:(oF' 0x51d7c%Z)) (ltac:(oD' 0x51d7c%Z)); zbtk (ltac:(oF' 0x51e28%Z)) (ltac:(oD' 0x51e28%Z)); zstep (ltac:(oF' 0x51d88%Z)) (ltac:(oD' 0x51d88%Z)); zstep (ltac:(oF' 0x51d8c%Z)) (ltac:(oD' 0x51d8c%Z)); zbtk (ltac:(oF' 0x51d90%Z)) (ltac:(oD' 0x51d90%Z)); apply mst_refl
| gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; reflexivity | intros; kept_solve ].
- specialize (R7 RS).
eexists. split; [|split; [|split; [|split]]];
[ zbtk (ltac:(oF' 0x51d7c%Z)) (ltac:(oD' 0x51d7c%Z)); zbft (ltac:(oF' 0x51e28%Z)) (ltac:(oD' 0x51e28%Z)); zstep (ltac:(oF' 0x51e2c%Z)) (ltac:(oD' 0x51e2c%Z)); zstep (ltac:(oF' 0x51e30%Z)) (ltac:(oD' 0x51e30%Z)); zstep (ltac:(oF' 0x51e34%Z)) (ltac:(oD' 0x51e34%Z)); zbft (ltac:(oF' 0x51e38%Z)) (ltac:(oD' 0x51e38%Z));
stepn (ltac:(oF' 0x51e3c%Z)) (ltac:(oD' 0x51e3c%Z)); apply mst_refl
| gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
Qed.
End SE.
#[using="Type"] Lemma art_zb_sllw_small : ltac2:(TCodec.tc2 tcn__JatAllocA "Q7'6&Jzr2%3221'2&K+Q0%2251%4251&Mr4&N+2r3%3221%6251+O%6251%=231'3'Q@yR0%211&F&Q?r5%2251%326A%5221%B2AC%E251%72:1%=3:41p0?1p0J1p0Q01pR8Q51pS<Q61").
Proof.
intros x k Hx Hk Hxk. unfold v_sllw.
assert (Hx' : x < 2 ^ 31). { pose proof (Z.pow_pos_nonneg 2 k). nia. }
rewrite !art_u_lit by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
pose proof (Z.pow_pos_nonneg 2 k). rewrite Z.mod_small by nia. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_alloc_a3_fn := (ltac2:(TCodec.tc2 tcn__JatAllocA "X7&7y5'Q@yR0%211%5241'0y8%611%311p061'6'3&Cr>(Q>+2(1%33A21%6251&Q?r;%22C1%;3C41r?+4%;3I19%>231r6%92J1%B3J31r@+8%B3Q01@%E231%?2Q03%H3Q021rA+:%H3Q61F%K231&Lr<%221;%H2Q91%Q13Q951rB+B%Q13Q?1O%Q4231%Q63Q>1?rC+C%Q63QD1Q4%Q9231r=%Q42QE1%Q=3QE31rD+D%Q=3QK1Q;%Q@231+RPP0%Q;2QL1%QD3QL31rE+E%QD3R21QB%QG231%QA2R2Q6%QJ3R221rF+F%QJ3R81QH%QM231%QG2R8M%R03R821rG+J%R03R>1QN%R3231&H+QoO%22Q01%R02RA1%R93RA51&J+@%221G&K&N+R0%22R<1%42F1+TP0%921H%?2C2+VbTP0%<221%B22<rI%?221'2+1rH%C221+Q8%A2RK1%C241%7241z%I217+7%K291%<231&M&IrJ%R=21RF%Q6217%421RH%621RI%S>3S?B1%Q12S;6%92Q51%SA3SBE1%Q=29J%Q921R1&<&GrQ1&OrO%221Q>%64541Q?&;rQ2+Sa0%QI261u8%55;421Q1&ArQ3rK%3621KQ<Q8R3&:%?24QKrM+RH%B221%544QO1SFrQ4%E21R1rL%Q72SJ7%R:221%;44R51SLrQ5%K21R7+TH%R?271%@43R:1T1'>&DvQ1rQ9+ZW\H%TH3U41TF/01U4rQ8rQ7%8576321&E%TN3U<R6TL+ZWd4%U03U<1TN/01U<%53<41rQ6%TO2U@1%833U21%U12UBR>%:32TE1+9%U93UG1U7%U52UFQ2%>3421%U72UHN%@32TE1+;%U?3UM1U=+V@%S?2Q71%U=2UN1%F3641+<%UE3V31UC%SD2QMR3%UB2V31%K3531+=%UJ3V81UH%N331U7%O31TF5%UH2V9R:%Q132TA1+H%V03V>1UN%R=2SDU@%UM2V>1%Q63531%UO2V@QJ%Q832T51+ZhiL%V73VC1V5/01VC&9%RF2Q7UI+ZWc8%34R@QB21%QI5QH851QB%QK3RLQB1p0QM1p0R31p0R:1p0SH1p0RB1p0RG1p0RN1p0S61p0S91p0S=1p0SF1p0SL1p0T51p0T91p0T=1p0T@1p0TF1p0TJ1p0U41p0U;1p0UB1p0UJ1p0V21p0V81p0VB1p0VI1p0W11pS6W>1pR2W?1pS:W@1pR:WA1pS8WB1pRJWC1pRHWD1pR>WE1pR<WF1pR6WG1pRLWH1pRFWJ1pBWK1pRBX11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_fn) 3%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_fn) 5%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_alloc_a3_fn) 6%nat 0%nat).
Lemma art_alloc_a3_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_a3_fn) 7%nat 0%nat).
Proof using Type regs M rom sp ia n r.
intros rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
pose proof TSD as (_ & _ & _ & _ & _ & R).
assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
zstep (ltac:(oF' 0x51d98%Z)) (ltac:(oD' 0x51d98%Z)). zstep (ltac:(oF' 0x51d9c%Z)) (ltac:(oD' 0x51d9c%Z)). zstep (ltac:(oF' 0x51da0%Z)) (ltac:(oD' 0x51da0%Z)). zstep (ltac:(oF' 0x51da4%Z)) (ltac:(oD' 0x51da4%Z)). zstep (ltac:(oF' 0x51da8%Z)) (ltac:(oD' 0x51da8%Z)).
stepn (ltac:(oF' 0x51dac%Z)) (ltac:(oD' 0x51dac%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
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
