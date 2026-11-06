(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim RefMemcpyLib As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatPoison JatAllocG JatUnwind.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatUnwindG () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatUnwind."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "0M'"; "5cell"; "5wr"; "6msteps"]; ["7ret_ok"; "8readable8"; "8trace_cells"; "9getr"; "9mkst"; ":mem_grows"; ";loaded_segments"; "<In"; "=add"; "=le"; "=lt"; "=modulo"; "=pow"; "=sub"; "0bot"; "0bp"]; ["0fx"; "0pc"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0sp"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0sz"; "0this"; "0top"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Ltac uwf_prefix W Wt Cg Cps sp raw regs this pc top :=
zstep (ltac:(oF' 0x99ff8%Z)) (ltac:(oD' 0x99ff8%Z));
zsd (ltac:(oF' 0x99ffc%Z)) (ltac:(oD' 0x99ffc%Z)) (sp - 8) (U raw) ltac:(rewok W); zsd (ltac:(oF' 0x9a000%Z)) (ltac:(oD' 0x9a000%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W);
zsd (ltac:(oF' 0x9a004%Z)) (ltac:(oD' 0x9a004%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W); zsd (ltac:(oF' 0x9a008%Z)) (ltac:(oD' 0x9a008%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W);
zsd (ltac:(oF' 0x9a00c%Z)) (ltac:(oD' 0x9a00c%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W); zsd (ltac:(oF' 0x9a010%Z)) (ltac:(oD' 0x9a010%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W);
zsd (ltac:(oF' 0x9a014%Z)) (ltac:(oD' 0x9a014%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W); zsd (ltac:(oF' 0x9a018%Z)) (ltac:(oD' 0x9a018%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W);
zstep (ltac:(oF' 0x9a01c%Z)) (ltac:(oD' 0x9a01c%Z)); zstep (ltac:(oF' 0x9a020%Z)) (ltac:(oD' 0x9a020%Z)); zstep (ltac:(oF' 0x9a024%Z)) (ltac:(oD' 0x9a024%Z)); zstep (ltac:(oF' 0x9a028%Z)) (ltac:(oD' 0x9a028%Z));
zbft (ltac:(oF' 0x9a02c%Z)) (ltac:(oD' 0x9a02c%Z));
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
let Cg' := fresh "Cg'" in let Cps' := fresh "Cps'" in
assert (Cg' : cellA X 0x132618 8 0x1ca7a0) by (recell Cg); assert (Cps' : cellA X 0x1ca7a0 8 4096) by (recell Cps);
zstep (ltac:(oF' 0x9a030%Z)) (ltac:(oD' 0x9a030%Z)); zld (ltac:(oF' 0x9a034%Z)) (ltac:(oD' 0x9a034%Z)) 0x132618 Cg'; zld (ltac:(oF' 0x9a038%Z)) (ltac:(oD' 0x9a038%Z)) 0x1ca7a0 Cps' end;
zbft (ltac:(oF' 0x9a03c%Z)) (ltac:(oD' 0x9a03c%Z));
zstep (ltac:(oF' 0x9a040%Z)) (ltac:(oD' 0x9a040%Z));
stepn (ltac:(oF' 0x9a044%Z)) (ltac:(oD' 0x9a044%Z)); rwH; rewrite art_zb_srli by lia;
zsw (ltac:(oF' 0x9a048%Z)) (ltac:(oD' 0x9a048%Z)) (this + 8) 1 ltac:(rewok Wt);
zsd (ltac:(oF' 0x9a04c%Z)) (ltac:(oD' 0x9a04c%Z)) (this + 16) pc ltac:(rewok Wt).
Ltac uwf_epilogue sp raw regs :=
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
let C56 := fresh "C56" in let C48 := fresh "C48" in let C40 := fresh "C40" in let C32 := fresh "C32" in
let C24 := fresh "C24" in let C16 := fresh "C16" in let C08 := fresh "C08" in let C00 := fresh "C00" in
assert (C56 : cellA X (sp - 64 + 56) 8 (U raw)) by (replace (sp - 64 + 56) with (sp - 8) by lia; zcell);
assert (C48 : cellA X (sp - 64 + 48) 8 (U (getr regs 8))) by (replace (sp - 64 + 48) with (sp - 16) by lia; zcell);
assert (C40 : cellA X (sp - 64 + 40) 8 (U (getr regs 9))) by (replace (sp - 64 + 40) with (sp - 24) by lia; zcell);
assert (C32 : cellA X (sp - 64 + 32) 8 (U (getr regs 18))) by (replace (sp - 64 + 32) with (sp - 32) by lia; zcell);
assert (C24 : cellA X (sp - 64 + 24) 8 (U (getr regs 19))) by (replace (sp - 64 + 24) with (sp - 40) by lia; zcell);
assert (C16 : cellA X (sp - 64 + 16) 8 (U (getr regs 20))) by (replace (sp - 64 + 16) with (sp - 48) by lia; zcell);
assert (C08 : cellA X (sp - 64 + 8) 8 (U (getr regs 21))) by (replace (sp - 64 + 8) with (sp - 56) by lia; zcell);
assert (C00 : cellA X (sp - 64 + 0) 8 (U (getr regs 22))) by (replace (sp - 64 + 0) with (sp - 64) by lia; zcell);
zld (ltac:(oF' 0x9a0f4%Z)) (ltac:(oD' 0x9a0f4%Z)) (sp - 64 + 56) C56; rewrite Z_to_bv_bv_unsigned;
zld (ltac:(oF' 0x9a0f8%Z)) (ltac:(oD' 0x9a0f8%Z)) (sp - 64 + 48) C48; rewrite Z_to_bv_bv_unsigned;
zld (ltac:(oF' 0x9a0fc%Z)) (ltac:(oD' 0x9a0fc%Z)) (sp - 64 + 40) C40; rewrite Z_to_bv_bv_unsigned;
zld (ltac:(oF' 0x9a100%Z)) (ltac:(oD' 0x9a100%Z)) (sp - 64 + 32) C32; rewrite Z_to_bv_bv_unsigned;
zld (ltac:(oF' 0x9a104%Z)) (ltac:(oD' 0x9a104%Z)) (sp - 64 + 24) C24; rewrite Z_to_bv_bv_unsigned;
zld (ltac:(oF' 0x9a108%Z)) (ltac:(oD' 0x9a108%Z)) (sp - 64 + 16) C16; rewrite Z_to_bv_bv_unsigned;
zld (ltac:(oF' 0x9a10c%Z)) (ltac:(oD' 0x9a10c%Z)) (sp - 64 + 8) C08; rewrite Z_to_bv_bv_unsigned;
zld (ltac:(oF' 0x9a110%Z)) (ltac:(oD' 0x9a110%Z)) (sp - 64 + 0) C00; rewrite Z_to_bv_bv_unsigned
end;
zstep (ltac:(oF' 0x9a114%Z)) (ltac:(oD' 0x9a114%Z));
stepret (ltac:(oF' 0x9a118%Z)) (ltac:(oD' 0x9a118%Z)) raw ltac:(rwH; reflexivity);
apply mst_refl.
Section SE.
Local Abbreviation SEC_T_art_unwind_fast_exit := (ltac2:(TCodec.tc2 tcn__JatUnwindG "XN&:y5'Q:yR0%211%5241'2y8%611%311p061'9'5&Cr:(Q8+1(3%33A21%6251r7%93A21&@r8%211r<+2%<3J1:%?231&Q9%12K7%C3K31r=+:%C3Q11A%F231%H3Q016r>+;%H3Q61F%K231%M3Q51;r?+<%M3Q;1K%Q0231%Q23Q:1@r@+=%Q23Q@1Q0%Q5231%Q73Q?1ErA+>%Q73QE1Q5%Q:231%Q<3QD1JrB+?%Q<3QJ1Q:%Q?231+N%Q12QK1%QC3QK31&I+R0%221H&H%12E3%521K&J+X0%52I1&L+QO%22QA1%6241z%>21Q>%92Q:Q5+TP0%A21Q2%<2N7'4rC%E281%@22;%4221'8rD%J21Q1&M+@%2291%N215%7251rF%Q12D1%I2R8Q1%M231%A231+VbTP0%Q321Q5rI%Q8221&>&FrMrJ%B21Q<%54431Q=rN%74614Q9&=rO+QVY`Hu8+QiYm0%55<4321rQ0%75>134Q8'6'?&DvQ0rQ4+cWoH%S@3SL1S>/01SLrQ3rQ2%8576321r2rQ1r1%<5;3215%>3N51%SL25S>%S=2T7C%SO3T721%SO28SJ%T13T918%T<1T=&G(0+8%T33TA1T1+9%T53TC1T3+B%T73TE1T5+C%T93TG1T7+D%T;3TI1T9+E%T=3TK1T;+F%T?3TM1T=+G%TA3TO1T?+H%TC3U11TA+I%TE3U31TC+J%TG3U51TE+K%TI3U71TG+3%TK3U91TI+4%TM3U;1TK(1%11Q0%O3Q131%Q03Q261%Q13Q391%Q23Q4<1%Q33Q5?1%Q43Q6B1%Q53Q7E1%Q63Q8H1%Q73Q9K1%Q83Q:N1%Q93Q;Q11%Q:3Q<Q41%Q;3Q=Q71%Q<3Q>Q:1%Q>3Q?QG1r4%UB21QKrQ6%UD21QM%UF3UN31p061pR6QF1&E%12R5R0&7%T52RAQG&Q;%12V7R4%T;231%T92REU1%T7231%SK231%811%T=2R;SD%82V>R=%TB221%T@2R>T<%T>231%T2231%?11%SL2RFTFr3%@2VF1%TJ231%TE22RJ%T9221%F11r5%11Q1rQ7%11Q3%VF3VI31p061p0>1p0F1pS0W21%U72VGS1%U82S2U;%TF221u4%SJ5T1S7Q31S5&B%13S9SFS7%TK231%TL261qRJW51%SH2W61%TO2<1%U02Q=1%U12Q@1%U22S81%U32S;1%U42S?1qJW>1%T02W?1qR<WE1%T22WF1p0T41p0T71p0T>1p0TA1p0TH1p0TM1p0U31p0U<1p0UB1p0UD1p0UG1p0UI1p0UL1p0V41p0V81p0V<1p0VD1p0VJ1p0W01p0W61p0W<1p0WB1p0WJ1p0WN1pQNX91pRNX:1pR0X;1pR4X<1pRLX=1pR@X>1pR8XF1pR>XA1pHXB1pR:XH1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 4%nat 0%nat).
Variable this : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 5%nat 0%nat).
Variable pc : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 6%nat 0%nat).
Variable bp : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 7%nat 0%nat).
Variable top : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 8%nat 0%nat).
Variable bot : ltac:(sec_ty2 constr:(SEC_T_art_unwind_fast_exit) 9%nat 0%nat).
Lemma art_unwind_fast_exit : ltac:(sec_stmt2 constr:(SEC_T_art_unwind_fast_exit) 10%nat 0%nat).
Proof using Type regs M rom raw sp this pc bp top bot.
intros H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbt Htop4 Htop Hbp EXIT Hpc IMG W Wt Cg Cps.
set (M1 := Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
(sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (this + 8) 1) (this + 16) pc).
assert (Htop12 : 1 <= top / 2 ^ 12) by (apply Z.div_le_lower_bound; lia). assert (Htop12' : top / 2 ^ 12 < 2 ^ 52) by (apply Z.div_lt_upper_bound; lia).
pose proof (art_u_lit top ltac:(lia)) as Utop.
assert (RUN : exists regs', msteps ASEGS (mkst regs (0x99ff8 : word) M rom) (mkst regs' raw M1 rom)
/\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
/\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)).
{ destruct (Z_le_gt_dec bp bot) as [E1|E1].
- eexists. split.
+ uwf_prefix W Wt Cg Cps sp raw regs this pc top.
zbtk (ltac:(oF' 0x9a050%Z)) (ltac:(oD' 0x9a050%Z)). zbft (ltac:(oF' 0x9a098%Z)) (ltac:(oD' 0x9a098%Z)). zbtk (ltac:(oF' 0x9a09c%Z)) (ltac:(oD' 0x9a09c%Z)).
uwf_epilogue sp raw regs.
+ split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity].
- assert (E2 : top - 16 <= bp) by lia.
eexists. split.
+ uwf_prefix W Wt Cg Cps sp raw regs this pc top.
zbtk (ltac:(oF' 0x9a050%Z)) (ltac:(oD' 0x9a050%Z)). zbft (ltac:(oF' 0x9a098%Z)) (ltac:(oD' 0x9a098%Z)). zbft (ltac:(oF' 0x9a09c%Z)) (ltac:(oD' 0x9a09c%Z)). zstep (ltac:(oF' 0x9a0a0%Z)) (ltac:(oD' 0x9a0a0%Z)). zbtk (ltac:(oF' 0x9a0a4%Z)) (ltac:(oD' 0x9a0a4%Z)).
uwf_epilogue sp raw regs.
+ split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]. }
destruct RUN as (regs' & RUN & P2 & P1 & PK).
exists regs', M1. split; [exact RUN|]. split; [exact P2|]. split; [exact P1|]. split; [exact PK|].
split. { unfold M1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
split. { intros x N1 N2 N3. unfold M1. rewrite !Wn_outside by (cbn; lia). reflexivity. }
exists 1. split; [lia|]. split; [unfold M1; zcell|].
intros i Hi. exists (Z_to_bv 64 pc). rewrite art_u_lit by lia. replace (this + 16 + 8 * i) with (this + 16) by lia. unfold M1. zcell.
Qed.
End SE.
#[using="Type"] Lemma art_unwind_fast_any : ltac2:(TCodec.tc2 tcn__JatUnwindG "Y7&:y5'Q:yR0%211%5241'2y8%611%311p061'9'5&Cr:(Q8+1(3%33A21%6251r7%93A21&@r8%211r<+2%<3J1:%?231&Q9%12K7%C3K31r=+:%C3Q11A%F231%H3Q016r>+;%H3Q61F%K231%M3Q51;r?+<%M3Q;1K%Q0231%Q23Q:1@r@+=%Q23Q@1Q0%Q5231%Q73Q?1ErA+>%Q73QE1Q5%Q:231%Q<3QD1JrB+?%Q<3QJ1Q:%Q?231+N%Q12QK1%QC3QK31&I+R0%221H&H%12E3%521K+RP@%42H1&M+@%22Q51%;241z%=21Q=&J%12Q:Q5+TP0%A21Q2&L+QO%22QJ1%72Q11rC%9213&KrD+8%3221%R@3RA1@'4rF%O2C1%>2R6O%C231%5231+VbTP0%Q121Q3rI%Q6221&>&FrMrJ%Q321Q:%54431Q;rN+X0%847251rG%Q321<%Q:2=Q9%Q5291&ArQ1rK%Q?21Q>%4331>p061p091&=rQ0+QVY`Hu8+QiYm0%55H4321%65I<23QA'6'?&DvQ0rQ5+cWoH%SI3T51SG/01T5rQ4rQ3%8576321r2rQ2r1%<5;3215%>3Q951%T525SG%SF2T@N%T83T@21%T828T3%T:3TB18%TE1TF&G(0%T;3TIR0T9+9%T=3TK1T;+B%T?3TM1T=+C%TA3TO1T?+D%TC3U11TA+E%TE3U31TC+F%TG3U51TE+G%TI3U71TG+H%TK3U91TI+I%TM3U;1TK+J%TO3U=1TM+K%U13U?1TO+3%U33UA1U1+4%U53UC1U3(1%11O%N3Q031%O3Q161%Q03Q291%Q13Q3<1%Q23Q4?1%Q33Q5B1%Q43Q6E1%Q53Q7H1%Q63Q8K1%Q73Q9N1%Q83Q:Q11%Q93Q;Q41%Q:3Q<Q71%Q;3Q=Q:1%Q=3Q>QF1r4%UJ21QJrQ7%UL21QL%UN3V631p061pR6QE1&E%12R4QO&7%T=2RKSF&Q;%12V?R3%TC231%TA2ROU9%T7231%SI231%811%TE2R:T?%82VFR<%TJ221%TH2R=S=%T>231%T0231%?11%TG2RETNr3%@2VN1%U2231%TE22RI%T7221%F11r5%11Q1rQ8%11Q3%VN3W131p061p0>1p0F1pS0W:1%U?2VOS0%U@2S1UC%TD221u4%SH5T;S6Q31S4&B%13S8T0S6%TI231%TJ261qRJW=1%SG2W>1%TM2<1%TN2Q=1%TO2Q@1%U02S71%U12S:1%U22S>1qJWF1%SO2WG1qR<WM1%T12WN1p0T31p0T51p0T<1p0TH1p0TL1p0U31p0U81p0U?1p0UE1p0UH1p0UM1p0V01p0V31p0V61p0V=1p0VA1p0VE1p0VM1p0W31p0W91p0W?1p0WE1p0WK1p0X31p0X71pQNXB1pRNXC1pR0XD1pR4XE1pRLXF1pR@XG1pR8XO1pR>XJ1pHXK1pR:Y11").
Proof.
intros regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbt Htop4 Htop Hbp Hbp8 Hpc IMG W Wt RD Cg Cps.
destruct (Z_lt_ge_dec bot bp) as [E1|E1]; [destruct (Z_lt_ge_dec bp (top - 16)) as [E2|E2]|].
- apply (art_unwind_fast_run regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot E1 E2 Htop Hbp8 Hpc IMG W Wt (RD E1 E2) Cg Cps).
- apply (art_unwind_fast_exit regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) ltac:(right; lia) Hpc IMG W Wt Cg Cps).
- apply (art_unwind_fast_exit regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) ltac:(left; lia) Hpc IMG W Wt Cg Cps).
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
