(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp JbtFree1 JbtCellEx JbtRecycle4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle5R () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5R."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5R.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "5cell"; "5wr"; "6msteps"; "7ret_ok"]; ["8art_agree"; ":art_rcy_tail_mem"; "9art_rcy_head_mem"; ";getr"; ";mkst"; "<mem_grows"; "=loaded_segments"; ">In"; "?add"; "?le"; "?lt"; "?mul"; "?pow"; "?sub"; "0b"; "0cnt"]; ["0fx"; "0g18"; "0g19"; "0g20"; "0g8"; "0g9"; "0gb"; "0gbytes"; "0gfirst"; "0k"; "0mn"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"]; ["0sp"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0tmp"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_rcy_head_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
(sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 80) 0) (sp - 72) 0) (sp - 64) 0) (sp - 56) 0) (0x1396b0 + 152) 257.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_rcy_head := (ltac2:(TCodec.tc2 tcn__JbtRecycle5R "WI&:y5'QCyR0%211%5241'2y8%611%311p061'9'7&Cr9(QA+1(5%33A21%6251r6%93A21r:+2%93G17%<231&QB%12H7%@3H31r;+:%@3N1>%C231+QWUe@%82O1%G3O31r<+;%G3Q51E%J231r7%?2Q61%N3Q631&I&H+Vb\P0+R@%3221%521Q2&J&L+R0%22M1%42O1&=&Fr>&M%12M<%54431=r?+TH%B2M1+4%:49421%F2QAQ4&K+`P0%221Q0%J21Q8+QI%E2Q@1%G2Q41'6z%Q021?r=%L2A1%5231%Q4253%O24L%8221&<rEu4+X0%45O3H21rF+UH%Q=2QH1u8r@%:5Q55321rG+U0%QC2QN1rB%?5Q:4271rH+U8%QH2R31rA%D5Q?42<1'8'>&DvQ0rK+Z_Y4%RN3S:1RL/01S:rJrI%8576321r1+Z_a0%S53SA1S3/01SA&B%148JE<%?5>6318%A3R281%S=28S2%R22NR=%S22SI1%SA3SI31%SA2<RO%SC3SK1RM%SC2>RJ%S72SNQ:%SF3SN21+>%SE3T31SC%SH2C1%S<2T3QL%SK3T321+?%SJ3T81SH%SM2H1%SO3T715+@%SN3T<1SL%T12L1%SE2T<QL%T43T<21+5%T33TA1T1%T62Q11rC%SK2TB1%T:3TB31%TE1TF&G(0+3%T<3TJ1T:%T=3TKRMT;+8%T?3TM1T=+9%TA3TO1T?+<%TC3U11TA+=%TE3U31TC+B%TG3U51TE+C%TI3U71TG+D%TK3U91TI+E%TM3U;1TK+F%TO3U=1TM+G%U13U?1TO+H%U33UA1U1+I%U53UC1U3+J%U73UE1U5+K%U93UG1U7(1%11Q3%Q23Q431%Q33Q561%Q43Q691%Q53Q7<1%Q63Q8?1%Q73Q9B1%Q83Q:E1%Q93Q;H1%Q:3Q<K1%Q;3Q=N1%Q<3Q>Q11%Q=3Q?Q41%Q>3Q@Q71%Q?3QAQ:1%Q@3QBQ=1%QA3QCQ?1%QB3QDUI1%QD3QERJ1r3r2%V2221rM%V4213%V63V>31p071pRHQM1%T<2QO1%T=2R61%T>2R<1%T?2RA1%T@2RG1%TA2RK1%TB2RN1%TC2S31qRNVH1%SG2VI1p0SI1p0SO1p0T51p0T<1p0TB1p0TF1p0TM1p0U11p0U61p0U81p0U>1p0UE1p0UK1p0V21p0V:1p0VB1p0VJ1pRBW51pR@W61pR0W71pRFW81pS2W91pRJWA1pS0W<1pHW=1pRLWC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 4%nat 0%nat).
Variable mn : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 5%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 6%nat 0%nat).
Variable gbytes : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 7%nat 0%nat).
Variable gfirst : ltac:(sec_ty2 constr:(SEC_T_art_rcy_head) 8%nat 0%nat).
Lemma art_rcy_head : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_head) 9%nat 0%nat).
Proof using Type regs M rom raw sp mn cnt gbytes gfirst.
intros H1 H2 H10 H11 Hsp Hsp' W Wlk Hcnt Hmerge Hgb Hmn Hgf Clk Cgb Ccnt Cgf.
eexists. split.
{ zstep (ltac:(oF' 0x53d24%Z)) (ltac:(oD' 0x53d24%Z)).
zsd (ltac:(oF' 0x53d28%Z)) (ltac:(oD' 0x53d28%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x53d2c%Z)) (ltac:(oD' 0x53d2c%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x53d30%Z)) (ltac:(oD' 0x53d30%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x53d34%Z)) (ltac:(oD' 0x53d34%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x53d38%Z)) (ltac:(oD' 0x53d38%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x53d3c%Z)) (ltac:(oD' 0x53d3c%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x53d40%Z)) (ltac:(oD' 0x53d40%Z)) (sp - 80) 0 ltac:(rewok W). zsd (ltac:(oF' 0x53d44%Z)) (ltac:(oD' 0x53d44%Z)) (sp - 72) 0 ltac:(rewok W).
zsd (ltac:(oF' 0x53d48%Z)) (ltac:(oD' 0x53d48%Z)) (sp - 64) 0 ltac:(rewok W). zsd (ltac:(oF' 0x53d4c%Z)) (ltac:(oD' 0x53d4c%Z)) (sp - 56) 0 ltac:(rewok W).
zstep (ltac:(oF' 0x53d50%Z)) (ltac:(oD' 0x53d50%Z)). zstep (ltac:(oF' 0x53d54%Z)) (ltac:(oD' 0x53d54%Z)).
stepn (ltac:(oF' 0x53d58%Z)) (ltac:(oD' 0x53d58%Z)). rwH. zclosed (0x1396b0 + 152).
zstep (ltac:(oF' 0x53d5c%Z)) (ltac:(oD' 0x53d5c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x1396b0 + 152) 4 256) by zcell; assert (Wlk' : wokA X (0x1396b0 + 152) 4) by zwok end.
zcas6 (ltac:(oF' 0x53d60%Z)) (ltac:(oD' 0x53d60%Z)) (ltac:(oF' 0x53d64%Z)) (ltac:(oD' 0x53d64%Z)) (ltac:(oF' 0x53d68%Z)) (ltac:(oD' 0x53d68%Z)) (ltac:(oF' 0x53d6c%Z)) (ltac:(oD' 0x53d6c%Z)) (ltac:(oF' 0x53d70%Z)) (ltac:(oD' 0x53d70%Z)) (ltac:(oF' 0x53d74%Z)) (ltac:(oD' 0x53d74%Z)) (0x1396b0 + 152) 256 257 1 257 Clk' Wlk'.
zbft (ltac:(oF' 0x53d78%Z)) (ltac:(oD' 0x53d78%Z)).
stepn (ltac:(oF' 0x53d7c%Z)) (ltac:(oD' 0x53d7c%Z)). rwH. zclosed 0.
zbft (ltac:(oF' 0x53d80%Z)) (ltac:(oD' 0x53d80%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb' : cellA X (0x1396b0 + 184) 8 gbytes) by zcell; assert (Ccnt' : cellA X (0x1396b0 + 160) 8 cnt) by zcell;
assert (Cgf' : cellA X (0x1396b0 + 168) 8 gfirst) by zcell;
assert (T0 : cellA X (sp - 80) 8 0) by zcell; assert (T16 : cellA X (sp - 64) 8 0) by zcell end.
zld (ltac:(oF' 0x53d84%Z)) (ltac:(oD' 0x53d84%Z)) (0x1396b0 + 184) Cgb'.
zld (ltac:(oF' 0x53d88%Z)) (ltac:(oD' 0x53d88%Z)) (0x1396b0 + 160) Ccnt'.
zstep (ltac:(oF' 0x53d8c%Z)) (ltac:(oD' 0x53d8c%Z)).
zbft (ltac:(oF' 0x53d90%Z)) (ltac:(oD' 0x53d90%Z)).
zbft (ltac:(oF' 0x53d94%Z)) (ltac:(oD' 0x53d94%Z)).
stepn (ltac:(oF' 0x53d98%Z)) (ltac:(oD' 0x53d98%Z)). zcl4.
zstep (ltac:(oF' 0x53d9c%Z)) (ltac:(oD' 0x53d9c%Z)). zstep (ltac:(oF' 0x53da0%Z)) (ltac:(oD' 0x53da0%Z)). zstep (ltac:(oF' 0x53da4%Z)) (ltac:(oD' 0x53da4%Z)).
zbtk (ltac:(oF' 0x53da8%Z)) (ltac:(oD' 0x53da8%Z)).
zld (ltac:(oF' 0x53de0%Z)) (ltac:(oD' 0x53de0%Z)) (sp - 80) T0.
zld (ltac:(oF' 0x53de4%Z)) (ltac:(oD' 0x53de4%Z)) (sp - 64) T16.
zld (ltac:(oF' 0x53de8%Z)) (ltac:(oD' 0x53de8%Z)) (0x1396b0 + 184) Cgb'.
zbft (ltac:(oF' 0x53dec%Z)) (ltac:(oD' 0x53dec%Z)).
zld (ltac:(oF' 0x53df0%Z)) (ltac:(oD' 0x53df0%Z)) (0x1396b0 + 168) Cgf'.
stepn (ltac:(oF' 0x53df4%Z)) (ltac:(oD' 0x53df4%Z)).
unfold art_rcy_head_mem. apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; exact H10|]. split; [gres; exact H11|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rcy_pop := (forall regs (M rom : word -> option byte) (tmp k plast gc b next size gbytes glast tbytes tfirst : Z), getr regs 10 = Z_to_bv 64 0x1396b0 -> getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 plast -> getr regs 16 = Z_to_bv 64 gc -> getr regs 5 = Z_to_bv 64 b ->
getr regs 2 = Z_to_bv 64 tmp ->
0x693000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x693000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 0 <= k < 2 ^ 63 -> 1 <= gc < 2 ^ 64 ->
0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= gbytes < 2 ^ 64 -> 0 <= tbytes < 2 ^ 64 ->
(k <> 0 -> 0x693000 <= plast /\ plast + 8 < 2 ^ 64 /\ apart plast 8 b 8192 /\ apart plast 8 tmp 32 /\ wrA M plast 8) ->
wrA M tmp 32 -> wrA M (0x1396b0 + 160) 32 -> wrA M b 8 ->
cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (0x1396b0 + 184) 8 gbytes -> cellA M (0x1396b0 + 176) 8 glast -> cellA M (tmp + 24) 8 tbytes -> cellA M (tmp + 8) 8 tfirst ->
exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x53e20 : word) M rom) (mkst regs' (0x53e1c : word) M' rom)
/\ getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 15 = Z_to_bv 64 b /\ getr regs' 5 = Z_to_bv 64 next /\ getr regs' 7 = Z_to_bv 64 (gbytes - size) /\ getr regs' 16 = Z_to_bv 64 (gc - 1) /\ getr regs' 6 = Z_to_bv 64 b
/\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
/\ mem_grows M M' /\ art_agree [(0x1396b0 + 160, 32); (b, 8); (tmp, 32); (plast, if k =? 0 then 0 else 8)] M M'
/\ cellA M' (0x1396b0 + 168) 8 next /\ cellA M' (0x1396b0 + 160) 8 (gc - 1) /\ cellA M' (0x1396b0 + 184) 8 (gbytes - size) /\ cellA M' b 8 0
/\ (next = 0 -> cellA M' (0x1396b0 + 176) 8 0) /\ (next <> 0 -> cellA M' (0x1396b0 + 176) 8 glast)
/\ (k = 0 -> cellA M' (tmp + 8) 8 b) /\ (k <> 0 -> cellA M' (tmp + 8) 8 tfirst /\ cellA M' plast 8 b)
/\ cellA M' (tmp + 24) 8 (tbytes + size)) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 2%nat 0%nat).
Variable tmp : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 3%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 4%nat 0%nat).
Variable plast : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 5%nat 0%nat).
Variable gc : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 6%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 7%nat 0%nat).
Variable next : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 8%nat 0%nat).
Variable size : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 9%nat 0%nat).
Variable gbytes : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 10%nat 0%nat).
Variable glast : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 11%nat 0%nat).
Variable tbytes : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 12%nat 0%nat).
Variable tfirst : ltac:(sec_ty2 constr:(SEC_T_art_rcy_pop) 13%nat 0%nat).
Lemma art_rcy_pop : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_pop) 14%nat 0%nat).
Proof using Type regs M rom tmp k plast gc b next size gbytes glast tbytes tfirst.
intros H10 H14 H15 H16 H5 H2 Htmp Htmp' Hb Hb' Atb Hk Hgc Hnext Hsize Hgb Htb Hpl Wt Wq Wb
Cnext Csize Cgb Cgl Ctb Ctf.
unfold apart in Atb.
destruct (Z.eq_dec next 0) as [N0|N1]; destruct (Z.eq_dec k 0) as [K0|K1].
- rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
{ zbft (ltac:(oF' 0x53e20%Z)) (ltac:(oD' 0x53e20%Z)).
zld (ltac:(oF' 0x53e24%Z)) (ltac:(oD' 0x53e24%Z)) b Cnext.
zsd (ltac:(oF' 0x53e28%Z)) (ltac:(oD' 0x53e28%Z)) (0x1396b0 + 168) next ltac:(rewok Wq).
zbft (ltac:(oF' 0x53e2c%Z)) (ltac:(oD' 0x53e2c%Z)).
zsd (ltac:(oF' 0x53e30%Z)) (ltac:(oD' 0x53e30%Z)) (0x1396b0 + 176) 0 ltac:(rewok Wq).
zstep (ltac:(oF' 0x53e34%Z)) (ltac:(oD' 0x53e34%Z)).
zsd (ltac:(oF' 0x53e38%Z)) (ltac:(oD' 0x53e38%Z)) (0x1396b0 + 160) (gc + -1) ltac:(rewok Wq).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x1396b0 + 184) 8 gbytes) by zcell end.
zld (ltac:(oF' 0x53e3c%Z)) (ltac:(oD' 0x53e3c%Z)) (b + 8) Csize'.
zld (ltac:(oF' 0x53e40%Z)) (ltac:(oD' 0x53e40%Z)) (0x1396b0 + 184) Cgb'.
zstep (ltac:(oF' 0x53e44%Z)) (ltac:(oD' 0x53e44%Z)).
zsd (ltac:(oF' 0x53e48%Z)) (ltac:(oD' 0x53e48%Z)) (0x1396b0 + 184) (gbytes - size) ltac:(rewok Wq).
zstep (ltac:(oF' 0x53e4c%Z)) (ltac:(oD' 0x53e4c%Z)).
zsd (ltac:(oF' 0x53e50%Z)) (ltac:(oD' 0x53e50%Z)) b 0 ltac:(rewok Wb).
zbft (ltac:(oF' 0x53e54%Z)) (ltac:(oD' 0x53e54%Z)).
stepn (ltac:(oF' 0x53e58%Z)) (ltac:(oD' 0x53e58%Z)).
zsd (ltac:(oF' 0x53e6c%Z)) (ltac:(oD' 0x53e6c%Z)) (tmp + 8) b ltac:(rewok Wt).
stepn (ltac:(oF' 0x53e70%Z)) (ltac:(oD' 0x53e70%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
zld (ltac:(oF' 0x53dfc%Z)) (ltac:(oD' 0x53dfc%Z)) (b + 8) Csize2.
zld (ltac:(oF' 0x53e00%Z)) (ltac:(oD' 0x53e00%Z)) (tmp + 24) Ctb'.
zstep (ltac:(oF' 0x53e04%Z)) (ltac:(oD' 0x53e04%Z)).
zsd (ltac:(oF' 0x53e08%Z)) (ltac:(oD' 0x53e08%Z)) (tmp + 24) (tbytes + size) ltac:(rewok Wt).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x1396b0 + 184) 8 (gbytes - size)) by zcell end.
zld (ltac:(oF' 0x53e0c%Z)) (ltac:(oD' 0x53e0c%Z)) (0x1396b0 + 184) Cgb2.
zstep (ltac:(oF' 0x53e10%Z)) (ltac:(oD' 0x53e10%Z)). zstep (ltac:(oF' 0x53e14%Z)) (ltac:(oD' 0x53e14%Z)). zstep (ltac:(oF' 0x53e18%Z)) (ltac:(oD' 0x53e18%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
- destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
{ zbft (ltac:(oF' 0x53e20%Z)) (ltac:(oD' 0x53e20%Z)).
zld (ltac:(oF' 0x53e24%Z)) (ltac:(oD' 0x53e24%Z)) b Cnext.
zsd (ltac:(oF' 0x53e28%Z)) (ltac:(oD' 0x53e28%Z)) (0x1396b0 + 168) next ltac:(rewok Wq).
zbft (ltac:(oF' 0x53e2c%Z)) (ltac:(oD' 0x53e2c%Z)).
zsd (ltac:(oF' 0x53e30%Z)) (ltac:(oD' 0x53e30%Z)) (0x1396b0 + 176) 0 ltac:(rewok Wq).
zstep (ltac:(oF' 0x53e34%Z)) (ltac:(oD' 0x53e34%Z)).
zsd (ltac:(oF' 0x53e38%Z)) (ltac:(oD' 0x53e38%Z)) (0x1396b0 + 160) (gc + -1) ltac:(rewok Wq).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x1396b0 + 184) 8 gbytes) by zcell end.
zld (ltac:(oF' 0x53e3c%Z)) (ltac:(oD' 0x53e3c%Z)) (b + 8) Csize'.
zld (ltac:(oF' 0x53e40%Z)) (ltac:(oD' 0x53e40%Z)) (0x1396b0 + 184) Cgb'.
zstep (ltac:(oF' 0x53e44%Z)) (ltac:(oD' 0x53e44%Z)).
zsd (ltac:(oF' 0x53e48%Z)) (ltac:(oD' 0x53e48%Z)) (0x1396b0 + 184) (gbytes - size) ltac:(rewok Wq).
zstep (ltac:(oF' 0x53e4c%Z)) (ltac:(oD' 0x53e4c%Z)).
zsd (ltac:(oF' 0x53e50%Z)) (ltac:(oD' 0x53e50%Z)) b 0 ltac:(rewok Wb).
zbtk (ltac:(oF' 0x53e54%Z)) (ltac:(oD' 0x53e54%Z)).
zsd (ltac:(oF' 0x53df8%Z)) (ltac:(oD' 0x53df8%Z)) plast b ltac:(rewok Wpl).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
zld (ltac:(oF' 0x53dfc%Z)) (ltac:(oD' 0x53dfc%Z)) (b + 8) Csize2.
zld (ltac:(oF' 0x53e00%Z)) (ltac:(oD' 0x53e00%Z)) (tmp + 24) Ctb'.
zstep (ltac:(oF' 0x53e04%Z)) (ltac:(oD' 0x53e04%Z)).
zsd (ltac:(oF' 0x53e08%Z)) (ltac:(oD' 0x53e08%Z)) (tmp + 24) (tbytes + size) ltac:(rewok Wt).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x1396b0 + 184) 8 (gbytes - size)) by zcell end.
zld (ltac:(oF' 0x53e0c%Z)) (ltac:(oD' 0x53e0c%Z)) (0x1396b0 + 184) Cgb2.
zstep (ltac:(oF' 0x53e10%Z)) (ltac:(oD' 0x53e10%Z)). zstep (ltac:(oF' 0x53e14%Z)) (ltac:(oD' 0x53e14%Z)). zstep (ltac:(oF' 0x53e18%Z)) (ltac:(oD' 0x53e18%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
- rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
{ zbft (ltac:(oF' 0x53e20%Z)) (ltac:(oD' 0x53e20%Z)).
zld (ltac:(oF' 0x53e24%Z)) (ltac:(oD' 0x53e24%Z)) b Cnext.
zsd (ltac:(oF' 0x53e28%Z)) (ltac:(oD' 0x53e28%Z)) (0x1396b0 + 168) next ltac:(rewok Wq).
zbtk (ltac:(oF' 0x53e2c%Z)) (ltac:(oD' 0x53e2c%Z)).
zstep (ltac:(oF' 0x53e34%Z)) (ltac:(oD' 0x53e34%Z)).
zsd (ltac:(oF' 0x53e38%Z)) (ltac:(oD' 0x53e38%Z)) (0x1396b0 + 160) (gc + -1) ltac:(rewok Wq).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x1396b0 + 184) 8 gbytes) by zcell end.
zld (ltac:(oF' 0x53e3c%Z)) (ltac:(oD' 0x53e3c%Z)) (b + 8) Csize'.
zld (ltac:(oF' 0x53e40%Z)) (ltac:(oD' 0x53e40%Z)) (0x1396b0 + 184) Cgb'.
zstep (ltac:(oF' 0x53e44%Z)) (ltac:(oD' 0x53e44%Z)).
zsd (ltac:(oF' 0x53e48%Z)) (ltac:(oD' 0x53e48%Z)) (0x1396b0 + 184) (gbytes - size) ltac:(rewok Wq).
zstep (ltac:(oF' 0x53e4c%Z)) (ltac:(oD' 0x53e4c%Z)).
zsd (ltac:(oF' 0x53e50%Z)) (ltac:(oD' 0x53e50%Z)) b 0 ltac:(rewok Wb).
zbft (ltac:(oF' 0x53e54%Z)) (ltac:(oD' 0x53e54%Z)).
stepn (ltac:(oF' 0x53e58%Z)) (ltac:(oD' 0x53e58%Z)).
zsd (ltac:(oF' 0x53e6c%Z)) (ltac:(oD' 0x53e6c%Z)) (tmp + 8) b ltac:(rewok Wt).
stepn (ltac:(oF' 0x53e70%Z)) (ltac:(oD' 0x53e70%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
zld (ltac:(oF' 0x53dfc%Z)) (ltac:(oD' 0x53dfc%Z)) (b + 8) Csize2.
zld (ltac:(oF' 0x53e00%Z)) (ltac:(oD' 0x53e00%Z)) (tmp + 24) Ctb'.
zstep (ltac:(oF' 0x53e04%Z)) (ltac:(oD' 0x53e04%Z)).
zsd (ltac:(oF' 0x53e08%Z)) (ltac:(oD' 0x53e08%Z)) (tmp + 24) (tbytes + size) ltac:(rewok Wt).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x1396b0 + 184) 8 (gbytes - size)) by zcell end.
zld (ltac:(oF' 0x53e0c%Z)) (ltac:(oD' 0x53e0c%Z)) (0x1396b0 + 184) Cgb2.
zstep (ltac:(oF' 0x53e10%Z)) (ltac:(oD' 0x53e10%Z)). zstep (ltac:(oF' 0x53e14%Z)) (ltac:(oD' 0x53e14%Z)). zstep (ltac:(oF' 0x53e18%Z)) (ltac:(oD' 0x53e18%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
- destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
{ zbft (ltac:(oF' 0x53e20%Z)) (ltac:(oD' 0x53e20%Z)).
zld (ltac:(oF' 0x53e24%Z)) (ltac:(oD' 0x53e24%Z)) b Cnext.
zsd (ltac:(oF' 0x53e28%Z)) (ltac:(oD' 0x53e28%Z)) (0x1396b0 + 168) next ltac:(rewok Wq).
zbtk (ltac:(oF' 0x53e2c%Z)) (ltac:(oD' 0x53e2c%Z)).
zstep (ltac:(oF' 0x53e34%Z)) (ltac:(oD' 0x53e34%Z)).
zsd (ltac:(oF' 0x53e38%Z)) (ltac:(oD' 0x53e38%Z)) (0x1396b0 + 160) (gc + -1) ltac:(rewok Wq).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x1396b0 + 184) 8 gbytes) by zcell end.
zld (ltac:(oF' 0x53e3c%Z)) (ltac:(oD' 0x53e3c%Z)) (b + 8) Csize'.
zld (ltac:(oF' 0x53e40%Z)) (ltac:(oD' 0x53e40%Z)) (0x1396b0 + 184) Cgb'.
zstep (ltac:(oF' 0x53e44%Z)) (ltac:(oD' 0x53e44%Z)).
zsd (ltac:(oF' 0x53e48%Z)) (ltac:(oD' 0x53e48%Z)) (0x1396b0 + 184) (gbytes - size) ltac:(rewok Wq).
zstep (ltac:(oF' 0x53e4c%Z)) (ltac:(oD' 0x53e4c%Z)).
zsd (ltac:(oF' 0x53e50%Z)) (ltac:(oD' 0x53e50%Z)) b 0 ltac:(rewok Wb).
zbtk (ltac:(oF' 0x53e54%Z)) (ltac:(oD' 0x53e54%Z)).
zsd (ltac:(oF' 0x53df8%Z)) (ltac:(oD' 0x53df8%Z)) plast b ltac:(rewok Wpl).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
zld (ltac:(oF' 0x53dfc%Z)) (ltac:(oD' 0x53dfc%Z)) (b + 8) Csize2.
zld (ltac:(oF' 0x53e00%Z)) (ltac:(oD' 0x53e00%Z)) (tmp + 24) Ctb'.
zstep (ltac:(oF' 0x53e04%Z)) (ltac:(oD' 0x53e04%Z)).
zsd (ltac:(oF' 0x53e08%Z)) (ltac:(oD' 0x53e08%Z)) (tmp + 24) (tbytes + size) ltac:(rewok Wt).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x1396b0 + 184) 8 (gbytes - size)) by zcell end.
zld (ltac:(oF' 0x53e0c%Z)) (ltac:(oD' 0x53e0c%Z)) (0x1396b0 + 184) Cgb2.
zstep (ltac:(oF' 0x53e10%Z)) (ltac:(oD' 0x53e10%Z)). zstep (ltac:(oF' 0x53e14%Z)) (ltac:(oD' 0x53e14%Z)). zstep (ltac:(oF' 0x53e18%Z)) (ltac:(oD' 0x53e18%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
Qed.
End SE.
#[using="Type"] Lemma art_rcy_more : ltac2:(TCodec.tc2 tcn__JbtRecycle5R "R?&:y5'QCyR0%211%5241'2y8%611%311p061'9'7&Cr5(QA+;(5%33A21%6251&QBr2%22C1%;3C41r6+7%;3I19%>231%@3H16'6&Izr4%3221&Jr3%2241%8241&L+2+R0%3221%82:1'8'>&F&DvQ0r:+Z_`L%Q33Q?1Q1/01Q?r9r8%8576321r1+Z_a0%Q:3QF1Q8/01QF%=5<4176%@3?61%QK1QL%QA2Q97r;%QC219%QE3QM31pRH51%Q6271qRNQO1%J2R01p0L1p0Q21p0Q<1p0QB1pR>QO1pRFR01pS0R21pHR31pRLR91").
Proof.
intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbft (ltac:(oF' 0x53e1c%Z)) (ltac:(oD' 0x53e1c%Z)). apply mst_refl. } intros r. reflexivity.
Qed.
#[using="Type"] Lemma art_rcy_exit : ltac2:(TCodec.tc2 tcn__JbtRecycle5R "R?&:y5'QCyR0%211%5241'2y8%611%311p061'9'7&Cr5(QA+;(5%33A21%6251&QBr2%22C1%;3C41r6+7%;3I19%>231%@3H16'6&Izr3%3221r4%5231%7231&J&L+2+R0%3221%52L1'8'>&F&DvQ0r:+Z_`L%Q33Q?1Q1/01Q?r9r8%8576321r1+Z_cD%Q:3QF1Q8/01QF%=5<4176%@3?61%QK1QL%QA2Q97r;%QC219%QE3QM31pRH51%Q6271qRNQO1%J2R01p0L1p0Q31p0Q<1p0QB1pR>QO1pRFR01pS0R21pHR31pRLR91").
Proof.
intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbtk (ltac:(oF' 0x53e1c%Z)) (ltac:(oD' 0x53e1c%Z)). apply mst_refl. } intros r. reflexivity.
Qed.
Definition art_rcy_tail_mem (M : word -> option byte) (tmp k b : Z) : word -> option byte :=
Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x1396b0 + 152) 0) (0x1396b0 + 153) 0.
Section SE.
Local Abbreviation SEC_T_art_rcy_tail := (ltac2:(TCodec.tc2 tcn__JbtRecycle5R "UH&:y5'QCyR0%211%5241'2y8%611%311p061'9'7&Cr6(QA+2(5%33A21%6251&QBr3%22C1%;3C41r7+:%;3I19%>231+QWUe@%92J1%B3J31r8+>%B3Q01@%E231r4%@2Q11%I3Q131r9+6%I3Q71G%L231%N3Q616&I+Vb\P0%221E&J&H+Q0%22B1&L+R0%22Q41%7241'6z%=21I%;2J5%4221&=&Fr=r;%44321?r>+TH%C2Q61+4%948421'8'>&DvQ0rA+Z_cD%QL3R81QJ/01R8r@r?%8576321r1+Z`T<%R33R?1R1/01R?&Ar<%249FI1%@5?7419%B3L91+1%R;3RI1R9%R>2;1+Z_dD%R>3RJ1R</01RJ%RC3RK41+;%RB3S01R@%RE2B1%R?2S0Q3%RH3S021%S31S4&G(0+3%RJ3S81RH%RK3S9Q7RI+8%RM3S;1RK+9%RO3S=1RM+<%S13S?1RO+=%S33SA1S1+B%S53SC1S3+C%S73SE1S5+D%S93SG1S7+E%S;3SI1S9+F%S=3SK1S;+G%S?3SM1S=+H%SA3SO1S?+I%SC3T11SA+J%SE3T31SC+K%SG3T51SE(1%11Q3%Q23Q431%Q33Q561%Q43Q691%Q53Q7<1%Q63Q8?1%Q73Q9B1%Q83Q:E1%Q93Q;H1%Q:3Q<K1%Q;3Q=N1%Q<3Q>Q11%Q=3Q?Q41%Q>3Q@SK1%Q?3QAQ81%Q@3QBQ;1%QA3QCQ>1%QB3QDQ@1%QC3QET81%QE3QFR;1r2%T@2T81rC%TB213%TD3TL31p061pRHQM1%S=2QO1%S>2R51%S?2R=1qRNU11%S22U21p0S41p0S:1p0S@1p0SA1p0SG1p0T01p0T41p0T:1p0TB1p0TJ1pQNU71pRDU81pS<U91pS0U;1pHU<1pRLUB1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rcy_tail) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rcy_tail) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rcy_tail) 2%nat 0%nat).
Variable tmp : ltac:(sec_ty2 constr:(SEC_T_art_rcy_tail) 3%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_art_rcy_tail) 4%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_rcy_tail) 5%nat 0%nat).
Lemma art_rcy_tail : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_tail) 6%nat 0%nat).
Proof using Type regs M rom tmp k b.
intros H2 H10 H14 H6 Htmp Htmp' Hk Hb Wt Wq.
eexists. split.
{ zsd (ltac:(oF' 0x53e74%Z)) (ltac:(oD' 0x53e74%Z)) tmp k ltac:(rewok Wt).
zsd (ltac:(oF' 0x53e78%Z)) (ltac:(oD' 0x53e78%Z)) (tmp + 16) b ltac:(rewok Wt).
stepfence (ltac:(oF' 0x53e7c%Z)) (ltac:(oD' 0x53e7c%Z)).
zsb (ltac:(oF' 0x53e80%Z)) (ltac:(oD' 0x53e80%Z)) (0x1396b0 + 152) 0 ltac:(zwok').
stepfence (ltac:(oF' 0x53e84%Z)) (ltac:(oD' 0x53e84%Z)).
zsb (ltac:(oF' 0x53e88%Z)) (ltac:(oD' 0x53e88%Z)) (0x1396b0 + 153) 0 ltac:(zwok').
zstep (ltac:(oF' 0x53e8c%Z)) (ltac:(oD' 0x53e8c%Z)).
stepn (ltac:(oF' 0x53e90%Z)) (ltac:(oD' 0x53e90%Z)).
unfold art_rcy_tail_mem. apply mst_refl. }
split; [gres; bveq|]. split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
#[using="Type"] Lemma art_rcy_tail_mem_facts : ltac2:(TCodec.tc2 tcn__JbtRecycle5R "R9'QCyR0%211'2y8%511%311p051'9&I+Vb\P0r3%3221&J&Hr4+Q0%3221&L+2+R0%3221%9251&<&Fr6+QWUe@+TH%>221u4+X1%8576321'6&Er7&Ar5%243<1F%5241&@(0'4%12Q2Q2(3+8%24Q5Q5D1+@%Q12F1%54Q8Q814+4%74Q:Q:F1(1%11:%=3;31%>3<61%?3=:1%A31FCu8%Q35Q2EQ11F%Q45Q3F<2Q<z%Q65Q5HQ1Q01%N231%O251%Q0281%Q12K1p0Q31p0Q=1p0QH1pQNQM1pRDQN1pS<QO1pHR11").
Proof.
intros M tmp k b Htmp Htmp' Clk. unfold art_rcy_tail_mem.
split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|]. split; [zcell|]. split; [zcell|].
change (cellA (Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x1396b0 + 152) 0) (0x1396b0 + 153) 0) (0x1396b0 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
apply cell4_join; [lia|lia|lia|lia|lia| | | ].
- zcell.
- zcell.
- destruct (cell4_split M (0x1396b0 + 152) 257 ltac:(lia) ltac:(lia) ltac:(lia) Clk) as (_ & _ & C2). change (257 / 65536) with 0 in C2. zcell.
Qed.
#[using="Type"] Lemma art_rcy_epi : ltac2:(TCodec.tc2 tcn__JbtRecycle5R "UI&:y5'QCyR0%211%5241'2y8%611%311p061'9'7&Cr:(QA+2(5%33A21%6251&QB&Mr6+R@%3221%52F1%>3F71&?r8%211&I%1283&Jr9&L+R0%22D1%5241&<&Fr=+8%E2L1u8&QDr;%22Q;1%9587541r>+@%M251%=5<318Q5r?r<+H%Q2221%B5A41=Q:r@+Q0%Q62C1%F5E31AQ>rA+Q8%Q:2?1%J5I31EQBrB+Q@%Q>2?1%N5M31IQF'8'6'>&DvQ0rE+Z_dD%QM3R91QK/01R9rDrC%8576321r1%:591A43%<3Q<31+1%R63RD1R4%R9251%R;3RC1F%R;27R6%R52RFL%R>3RF21%R<3RJQBR:%R?2;1%R92RJQ4%RB3RJ21+9%RA3RO1R?%RD2@1%R>2ROQ>%RG3RO21+B%RF3S41RD%RI2E1%RC2S4QG%RL3S421+C%RK3S91RI%RN2J1%RH2S9R4%S13S921+D%S03S>1RN%S32O1%RM2S>QL%S63S>21%SA1SB&G(0+3%S83SF1S6+4%S:3SH1S8+E%S<3SJ1S:+F%S>3SL1S<+G%S@3SN1S>%SA3SOR:S?+I%SC3T11SA+J%SE3T31SC+K%SG3T51SE(1%11E%D3F31%E3G61%F3H91%G3I<1%H3J>1%I3KA1%J3LD1%K3MG1%L3NJ1%N3OR11r3r2%T8221rG%T:213%T<3TD31p071pRHQ71%RE2Q91%RF2Q?1%RG2QE1%RH2QK1%RI2R11%RJ2R61%RK2R:1%RL2R?1qRNTN1%RO2TO1p0S11p0S61p0S;1p0S@1p0SF1p0SK1p0T61p0T=1p0T@1p0TD1pR8U41pR6U51pR4U61pR<U71pR:U81pS2U91pRJUA1pS0U<1pHU=1pRLUC1").
Proof.
intros regs M rom raw sp g8 g9 g18 g19 g20 H2 Hret Hsp Hsp' F1 F8 F9 F18 F19 F20.
eexists. split.
{ zld (ltac:(oF' 0x53e94%Z)) (ltac:(oD' 0x53e94%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x53e98%Z)) (ltac:(oD' 0x53e98%Z)) (sp - 16) F8. zld (ltac:(oF' 0x53e9c%Z)) (ltac:(oD' 0x53e9c%Z)) (sp - 24) F9. zld (ltac:(oF' 0x53ea0%Z)) (ltac:(oD' 0x53ea0%Z)) (sp - 32) F18. zld (ltac:(oF' 0x53ea4%Z)) (ltac:(oD' 0x53ea4%Z)) (sp - 40) F19. zld (ltac:(oF' 0x53ea8%Z)) (ltac:(oD' 0x53ea8%Z)) (sp - 48) F20.
zstep (ltac:(oF' 0x53eac%Z)) (ltac:(oD' 0x53eac%Z)).
stepret (ltac:(oF' 0x53eb0%Z)) (ltac:(oD' 0x53eb0%Z)) raw ltac:(reflexivity).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
