(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp JbtRefill1 JbtPopulate1 JbtPopulate2 JbtCellEx .
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtRecycle3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle3R () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRefill1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3le"; "3lt"; "4nth"]; ["5Z"; "0HI"; "6bvmap"; "0M"; "0M'"; "7Wn"; "7apart"; "7cell"; "7wok"; "7wr"; "8msteps"; "9ret_ok"; ":art_agree"; ";art_gfa_frame"; ";art_w4s"; "<getr"]; ["<mkst"; "<regupd"; "=mem_grows"; ">loaded_segments"; "?In"; "@add"; "@le"; "@lt"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0c"; "0chp"; "0dst"; "0fx"]; ["0g18"; "0g19"; "0g20"; "0g21"; "0g22"; "0g23"; "0g24"; "0g25"; "0g26"; "0g27"; "0g8"; "0g9"; "0ia"; "0j"; "0mfa"; "0mp"]; ["0n"; "0nf"; "0nfr"; "0qris"; "0r"; "0raw"; "0rb"; "0regs"; "0regs'"; "0ris"; "0rom"; "0send"; "0sp"; "0spb"; "0src"; "0st"]; ["ABV"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0ws"; "0x"]]).
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
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_rta_lock_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle3R "Y4&By5'RByR0%211%5241'5y8%611%311p061'@':&Or>(R@+1(8%33A21%6251r;%93A21r?+2%93G17%<231&RA%12H7%@3H31r@+:%@3N1>%C231%E3M16rA+;%E3Q31C%H231%J3Q21;rB+<%J3Q81H%M231%O3Q71@rC+=%O3Q=1M%Q2231%Q43Q<1ErD+>%Q43QB1Q2%Q7231%Q93QA1JrE+?%Q93QG1Q7%Q<231%Q>3QF1O&Q6&Q5+Vb\P0+T0%3221%521I&Q7&Q:+R0%22Q=1%42I1+RPP0%<21K+TP0%=2H1%?21='9%A2QLQ5+O%C2Q71%4231z%F21QD+Q5%A2QL1%H2QB1+Q?%D2QO1%F231%M28QF&Q8%12LG%O2QD1%K216%42OQF%RB3RCQB1&FrH%82Q31%Q62QA1&Q;rL%221Q7%744Q81Q8rK%Q=2H1%Q822Q5%O221rJ%QA2L1%Q<22Q9%Q3221&I&Q3rQ4rQ1%@21QE%54431QFrQ5rN%N2QI1%QL2=1%:4941QK&GrQ6rQ2+Q0%R2221u8%65@521LrQ7rQ3+Q@%R8221%;5E416Q1rQ8rM%Q?2R:F%R=221%@5J41;QJ'J&Q0vQ?rQ:+Zbh0%T13T=1SO/01T=rQ9%756521=&Q1%QB2JRG%SL2TC1%339SO1+8%T:3TH1T8%R12RLN%RO2Q51%T22TI1%93641+9%T@3TN1T>+]oooooooooooO%T72TN1%>3531%T92U0RC%@32T51+_oooooooooooO%T<2U31%C33T31rO%S72TBQ<%RA2Q>1%S?231%TB2U91%I36T41%J31T0;%K31SL<+QL%S?2TJ1%TH2U?1%O34SK1+@%U63UD1U4%Q2331C+A%U93UG1U7+Q^L%U02UG1%Q73531+B%U>3UL1U<%U42UKR2%Q;3421+C%UB3V01U@%U82UORA%Q?3421+D%UF3V41UD%U<2V3RA%QC3421+E%UJ3V81UHrQ0%UA2V81%QH3531+F%UO3V=1UM%UE2V<RM%QL3421+G%V33VA1V1+Q8%TB2UM1%UK2VB1%R23641+H%V93VG1V7+QM%TH2V31%V12VH1%R83641+I%V?3VM1V=+S`PPPP0%U42QE1%V72VN1%R>3641+J%VE3W31VC%U32V>Q1%U:2QE1%T421VG%V>2W51%RE3751+K%VL3W:1VJ%RH331QJ+ZcR<%VO3W;1VM/01W;&E&M%14S0SGSAS4+S@%TA2SI1%UI2RJRM%64SG421%74SH1RLR6%S<5S;<91SB%S>3T9S61p0S@1p0SF1p0SL1p0T41p0T:1p0TA1p0TB1p0TG1p0TH1p0TM1p0U61p0U91p0U>1p0U@1p0UG1p0UJ1p0V01p0V41p0V71p0V=1p0VD1p0VJ1p0W01p0W61p0W<1p0WB1p0WH1p0X01pT8X;1pTDX<1pTLX=1pT2X>1pRLX?1pRJX@1pU0XA1pT0XB1pSJXC1pTJXD1pT<XL1pTFXG1pQ8XH1pT@XN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 5%nat 0%nat).
Variable mp : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 6%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 7%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 8%nat 0%nat).
Variable chp : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 9%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 10%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 11%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 12%nat 0%nat).
Variable qris : ltac:(sec_ty2 constr:(SEC_T_art_rta_lock_fn) 13%nat 0%nat).
Lemma art_rta_lock_fn : ltac:(sec_stmt2 constr:(SEC_T_art_rta_lock_fn) 14%nat 0%nat).
Proof using Type regs M rom raw sp ia mp st c chp n spb ris qris.
intros H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hc Hspb Hspb' Hris Hris' Eris Ar Hmp Hst Hchp Hn W Wr Cspb Cris Cmx.
zstep (ltac:(oF' 0x54b00%Z)) (ltac:(oD' 0x54b00%Z)).
zsd (ltac:(oF' 0x54b04%Z)) (ltac:(oD' 0x54b04%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54b08%Z)) (ltac:(oD' 0x54b08%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x54b0c%Z)) (ltac:(oD' 0x54b0c%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x54b10%Z)) (ltac:(oD' 0x54b10%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd (ltac:(oF' 0x54b14%Z)) (ltac:(oD' 0x54b14%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x54b18%Z)) (ltac:(oD' 0x54b18%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x54b1c%Z)) (ltac:(oD' 0x54b1c%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x54b20%Z)) (ltac:(oD' 0x54b20%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd (ltac:(oF' 0x54b24%Z)) (ltac:(oD' 0x54b24%Z)) (sp - 72) (U (getr regs 23)) ltac:(rewok W).
zsd (ltac:(oF' 0x54b28%Z)) (ltac:(oD' 0x54b28%Z)) (sp - 80) (U (getr regs 24)) ltac:(rewok W). zsd (ltac:(oF' 0x54b2c%Z)) (ltac:(oD' 0x54b2c%Z)) (sp - 88) (U (getr regs 25)) ltac:(rewok W). zsd (ltac:(oF' 0x54b30%Z)) (ltac:(oD' 0x54b30%Z)) (sp - 96) (U (getr regs 26)) ltac:(rewok W).
zsd (ltac:(oF' 0x54b34%Z)) (ltac:(oD' 0x54b34%Z)) (sp - 104) (U (getr regs 27)) ltac:(rewok W).
zstep (ltac:(oF' 0x54b38%Z)) (ltac:(oD' 0x54b38%Z)). zstep (ltac:(oF' 0x54b3c%Z)) (ltac:(oD' 0x54b3c%Z)). zstep (ltac:(oF' 0x54b40%Z)) (ltac:(oD' 0x54b40%Z)). zstep (ltac:(oF' 0x54b44%Z)) (ltac:(oD' 0x54b44%Z)). zstep (ltac:(oF' 0x54b48%Z)) (ltac:(oD' 0x54b48%Z)). zstep (ltac:(oF' 0x54b4c%Z)) (ltac:(oD' 0x54b4c%Z)). zstep (ltac:(oF' 0x54b50%Z)) (ltac:(oD' 0x54b50%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (ia + 32) 8 spb) by zcell; assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
zld (ltac:(oF' 0x54b54%Z)) (ltac:(oD' 0x54b54%Z)) (ia + 32) Cspb'. zld (ltac:(oF' 0x54b58%Z)) (ltac:(oD' 0x54b58%Z)) (ia + 48) Cris'.
zstep (ltac:(oF' 0x54b5c%Z)) (ltac:(oD' 0x54b5c%Z)). zstep (ltac:(oF' 0x54b60%Z)) (ltac:(oD' 0x54b60%Z)). zstep (ltac:(oF' 0x54b64%Z)) (ltac:(oD' 0x54b64%Z)). zstep (ltac:(oF' 0x54b68%Z)) (ltac:(oD' 0x54b68%Z)). zstep (ltac:(oF' 0x54b6c%Z)) (ltac:(oD' 0x54b6c%Z)). zstep (ltac:(oF' 0x54b70%Z)) (ltac:(oD' 0x54b70%Z)). zstep (ltac:(oF' 0x54b74%Z)) (ltac:(oD' 0x54b74%Z)).
zstep (ltac:(oF' 0x54b78%Z)) (ltac:(oD' 0x54b78%Z)). zstep (ltac:(oF' 0x54b7c%Z)) (ltac:(oD' 0x54b7c%Z)). zstep (ltac:(oF' 0x54b80%Z)) (ltac:(oD' 0x54b80%Z)). zstep (ltac:(oF' 0x54b84%Z)) (ltac:(oD' 0x54b84%Z)). zstep (ltac:(oF' 0x54b88%Z)) (ltac:(oD' 0x54b88%Z)). zstep (ltac:(oF' 0x54b8c%Z)) (ltac:(oD' 0x54b8c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmx' : cellA X (ris + c * 2 ^ 7) 8 0) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zcell) end.
zld (ltac:(oF' 0x54b90%Z)) (ltac:(oD' 0x54b90%Z)) (ris + c * 2 ^ 7) Cmx'.
zstep (ltac:(oF' 0x54b94%Z)) (ltac:(oD' 0x54b94%Z)).
zsd (ltac:(oF' 0x54b98%Z)) (ltac:(oD' 0x54b98%Z)) (sp - 112) (ris + c * 2 ^ 7 + 8) ltac:(rewok W).
zstep (ltac:(oF' 0x54b9c%Z)) (ltac:(oD' 0x54b9c%Z)). zstep (ltac:(oF' 0x54ba0%Z)) (ltac:(oD' 0x54ba0%Z)).
stepn (ltac:(oF' 0x54ba4%Z)) (ltac:(oD' 0x54ba4%Z)). rwH. zclosed 16140901064495857664.
zstep (ltac:(oF' 0x54ba8%Z)) (ltac:(oD' 0x54ba8%Z)).
stepn (ltac:(oF' 0x54bac%Z)) (ltac:(oD' 0x54bac%Z)). rwH. zclosed 0.
zbft (ltac:(oF' 0x54bb0%Z)) (ltac:(oD' 0x54bb0%Z)).
stepn (ltac:(oF' 0x54bb4%Z)) (ltac:(oD' 0x54bb4%Z)). rwH. zclosed (2 ^ 60).
stepn (ltac:(oF' 0x54bb8%Z)) (ltac:(oD' 0x54bb8%Z)). rwH. zclosed (2 ^ 60).
assert (Hr8 : (ris + c * 2 ^ 7) mod 8 = 0). { rewrite Eris. replace (128 * qris + c * 2 ^ 7) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmx2 : cellA X (ris + c * 2 ^ 7) 8 0) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zcell);
assert (Wr' : wokA X (ris + c * 2 ^ 7) 8) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zwok) end.
chain_step; [reflexivity
| eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)) _ (Z_to_bv 64 0));
[exact (ltac:(oF' 0x54bbc%Z)) | reflexivity | exact (ltac:(oD' 0x54bbc%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
| exact Cmx2 | apply bytes_le_to_Z_8 ]
| ]. wpc.
chain_step; [reflexivity
| eapply art_step_branch_ft_r; [exact (ltac:(oF' 0x54bc0%Z)) | reflexivity | exact (ltac:(oD' 0x54bc0%Z)) | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
| ]. wpc.
chain_step; [reflexivity
| eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)));
[exact (ltac:(oF' 0x54bc4%Z)) | reflexivity | exact (ltac:(oD' 0x54bc4%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wr' ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 (ris + c * 2 ^ 7)) (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 60)))) with (Wn 8 M0 (ris + c * 2 ^ 7) (2 ^ 60)).
zbft (ltac:(oF' 0x54bc8%Z)) (ltac:(oD' 0x54bc8%Z)).
zbtk (ltac:(oF' 0x54bcc%Z)) (ltac:(oD' 0x54bcc%Z)).
unfold art_gfa_frame. zret.
Qed.
End SE.
#[using="Type"] Lemma art_rta_copy : ltac2:(TCodec.tc2 tcn__JbtRecycle3R "U7'2'@%211&By5'RByR0%211%5241'5y8%611%311p061':&Or6(R@+I(8%33@21%6251&RAr3%22B1%;3B41r7+F%;3H19%>231%@3G16r8+:%@3M1>%C231%E3L1;r4&Q5r5&Q8+4&Q9&1r:%22Q;1%411%7261%:291%Q23Q?<1'=u1r;%:2QC1%4231&Q6z%221N&Q7&Q:+2+R0%3221%52Q41+TP0%:21Er?%H2R11%J11%M2L1%Q02B1%=219&Fr<r@%Q02R91%Q211%Q52Q41%6451J1&I&Q3r=rA%Q82RA1%Q:11%Q=2Q<1%746D51'3&>r1rC%Q@2RI1%4231'9&?r2rD%34RO21Q9%Q;2Q:1+O%Q92Q81%Q;241%9241&GrB%QO1:%R22R11%R52Q91u4%65M521<%A281p0C1pSLI1';'J&Q0vQ?+ZcSL%S43S?1S2/01S?%554N1@Q6+ZcT@%S83SC1S6/01SC&N%13EQCM%;5:Q531Q<%=3Q?71%SJ1SK&<+;%SA3SN1S?%SE34Q;1%411%SG36Q7S9%611%SI38S@SC%811%SJ2S3S5rG%SL21S7%SN3T531p051p081p0;1pT:A1%QE2C1qTBT:1%Q32T;1p0Q51p0R01p0R91p0RA1p0RH1p0RK1p0S21p0S61p0S<1p0SJ1p0T01p0T61pTHTO1pTNU01pRNU11pTFTF1pQ8TG1pT@TM1pU:U41").
Proof.
induction ws as [|w ws IH]; intros regs M rom dst src send H25 H22 H10 Esend Hlen Hs Hs' Hd Hd' A W Cws; cbn [length] in *. lia.
destruct (Cws O ltac:(lia)) as [Rw Cw]. cbn [nth] in Rw, Cw. replace (src + 4 * Z.of_nat 0) with src in Cw by lia.
assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x54c7c : word) M rom) (mkst regs1 (0x54c8c : word) (Wn 4 M dst w) rom)
/\ getr regs1 25 = Z_to_bv 64 (dst + 4) /\ getr regs1 22 = Z_to_bv 64 (src + 4) /\ getr regs1 10 = Z_to_bv 64 send
/\ (forall r : reg, r <> 11%bv -> r <> 22%bv -> r <> 25%bv -> getr regs1 r = getr regs r)).
{ eexists. split.
- zlw (ltac:(oF' 0x54c7c%Z)) (ltac:(oD' 0x54c7c%Z)) src Cw.
zstep (ltac:(oF' 0x54c80%Z)) (ltac:(oD' 0x54c80%Z)).
zsw (ltac:(oF' 0x54c84%Z)) (ltac:(oD' 0x54c84%Z)) dst w ltac:(rewok W).
zstep (ltac:(oF' 0x54c88%Z)) (ltac:(oD' 0x54c88%Z)). apply mst_refl.
- repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
destruct STEP as (regs1 & RUN1 & P25 & P22 & P10 & K1).
destruct ws as [|w2 ws2].
- cbn [length] in *. eexists. split.
+ eapply msteps_trans; [exact RUN1|]. cbn [art_w4s]. zbft (ltac:(oF' 0x54c8c%Z)) (ltac:(oD' 0x54c8c%Z)). apply mst_refl.
+ intros r N11 N22 N25. gres. apply K1; assumption.
- cbn [length] in *.
assert (RUNb : msteps ASEGS (mkst regs1 (0x54c8c : word) (Wn 4 M dst w) rom) (mkst regs1 (0x54c7c : word) (Wn 4 M dst w) rom)).
{ zbtk (ltac:(oF' 0x54c8c%Z)) (ltac:(oD' 0x54c8c%Z)). apply mst_refl. }
unfold apart in A.
destruct (IH regs1 (Wn 4 M dst w) rom (dst + 4) (src + 4) send P25 P22 P10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(unfold apart; lia) ltac:(apply wr_Wn; eapply wr_sub; [exact W|lia|lia])
ltac:(intros j Hj; destruct (Cws (S j) ltac:(lia)) as [R C]; split; [exact R|];
replace (src + 4 + 4 * Z.of_nat j) with (src + 4 * Z.of_nat (S j)) by lia; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|exact C]))
as (regs' & RUN2 & K2).
exists regs'. split.
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. cbn [art_w4s]. exact RUN2.
+ intros r N11 N22 N25. rewrite K2 by assumption. apply K1; assumption.
Qed.
Ltac inl3 := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac gkeep3 K rnew i V := let E := fresh "E" in assert (E : getr rnew i = V) by (rewrite K by reg_neq_tac; gres; rwH; reflexivity).
Section SE.
Local Abbreviation SEC_T_art_rta_mid_run := (ltac2:(TCodec.tc2 tcn__JbtRecycle3R "\0'2'@%211&By5'RByR0%211%5241'5y8%611%311p061':&Or?(R@+2(8%33@21%6251&RA&Q;r<+T0%3221%52E1%>3E71r@+8%>3K1<%A231r6%<2L1%E3L31rA+<%E3Q21C%H231%J3Q116rB+B%J3Q71H%M231r;%H2Q81%Q13Q831rC+C%Q13Q>1O%Q4231r=%O2Q?1%Q83Q?31rD+D%Q83QE1Q6%Q;231%Q52QEQ;%Q>3QE21rE+E%Q>3QK1Q<%QA231%Q;2QKQ9%QD3QK21rF+F%QD3R11QB%QG231r>%QB2R21%QK3R231rG+I%QK3R81QI%QN231&Q5+S`PPPP0%22QH1%QK2R;1%R43R;51&Q6+Vb\P0%221N+U@%R02D1%52K1&Q7&Q:+R0%22R:1%42C1%;2:QJ%A2QFR6rH%>221%?2>QI+Q0%:2RB1%G2QE1rJ%D221rK+Q?%@2RH1%B231&Q9&1rQ1%22S>1%411%S33S@Q71'9+1%Q121D+@%Q32F1%5231+TP0%Q621C&Q8+4%221F%Q?2E1rO%Q<221z%Q>21Q1rIrL%QF221%;2:1%QC21Q6+M%Q>2SF1%QF271%QG2:8%QB29Q?%J221rQ3%QK2>1%QF22QC%N221&FrQ0%R521R4%J2IF%R7221rQ2%M2L1%7431;1rQ4%Q02O=%:4215T2%R>26R=%<4@T41E&I&Q3rQ=rQ;%T;21R<+Q@%645421rQ>rQ5%94821T>rQ?%RK23RJ%<4;21M&GrQ@rQ7%S021QIu8%55A421:rQArQ8+H%S6221%:5F416?rQBrQ9+R@%S;221%?5K41;D'3&>r1rQF%RB2UN1%4231&?r2rQG%34V321R4%SB2R51+O%S=2UE1%S?241%RG241rQE%RO19%RB2RA1%SO2Q81u4%Q45Q@521;%RN271p0A1pSLG1';'J&Q0vQ?+ZcR<%V73VB1V5/01VB%554G1L@+Zcm8%V;3VF1V9/01VF%958L1Q1D%;3R051%V?3VLS=V=%VB2O1+ZcUD%VB3VM1V@/01VM%VG3VN41%VG2Q4VBrQD%VA21V?%VC2W31%VL3W341+:%VK3W81VI%VN2Q;1%VH2W8QH%W13W821+;%W03W=1VN%W32Q@1%VM2W=R2%W63W=21%W62QCV?%W02W@R:%W93W@21+=%W83WE1W6%W;2QH1%W52WESK%W>3WE21%WH1WI&Q4(0+3%W@3WM1W>%WA3WNT7W?%WB3WOR@W@(4%118%73931%83:W81%93;61%:3<81%<3=R=1r4%WM21R:rQI%WO21R<%X13X831p061pU<D1&Q2%12RERF&L'7%12XEXE(6%X12QAV2%24XHXH1SFrQ<%V=21V<%U22U1SK%V?221%U42U3SI%84XNXN21%VB2T0U;%:4Y0Y01X3%VD2T2S:%<4Y2Y21X5%Q01>%Q63?21%Q73@51%Q83A81%Q93B?1%E31S;S<%VL2T9T5%T05T<S>;SL1%VN2SET7%T25T>S@;SN1%V12Y=Q1%SC2SB1r3%W32T<W2%W42TBS7%UI2UH1%W6231rQJ%SE4YESD1UF%T<5TH73S91p091pSLSN1%V82=1%V92@1%V:2C1%V;2Q:1%V<2Q=1%V=2R31%V>2R91%V?2R=1%V@2RC1%VA2RI1%VB2RO1%VC2S61qQ:YI1%SD2YJ1qTBZ01%SF2Z11p0SH1p0TA1p0TG1p0TM1p0U41p0U81p0U<1p0UD1p0UG1p0UK1p0V41p0V51p0V61p0V;1p0V?1p0VC1p0VI1p0VL1p0W31p0W61p0W=1p0WD1p0WI1p0WO1p0X11p0X51p0X71p0X=1p0XA1p0XE1p0XO1p0Y71p0Y>1p0YE1p0YM1p0Z51p0Z;1p0ZC1pT6[?1pSN[@1pT4[A1pT>[B1pT:[C1pT2[D1pRL[E1pRJ[F1pT0[G1pSJ[H1pQ4[I1pTJ[J1pTF[?1pQ8[@1pT@[F1pU:[M1")) (only parsing).
Variable ws : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 2%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 4%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 5%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 6%nat 0%nat).
Variable mp : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 7%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 8%nat 0%nat).
Variable chp : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 9%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 10%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 11%nat 0%nat).
Variable rb : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 12%nat 0%nat).
Variable nf : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 13%nat 0%nat).
Variable mfa : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 14%nat 0%nat).
Variable nfr : ltac:(sec_ty2 constr:(SEC_T_art_rta_mid_run) 15%nat 0%nat).
Lemma art_rta_mid_run : ltac:(sec_stmt2 constr:(SEC_T_art_rta_mid_run) 16%nat 0%nat).
Proof using Type ws regs M rom sp HI ia mp c chp n r rb nf mfa nfr.
intros H2 H8 H12 H18 H19 H20 H21 H22 H25 HHI Hsp Hsp' Hr Hr' Hrb Hrb' HHI' En Hn Hchp Hchp' Hnf Hmfa Hmfa' Hnfr Hia Hmp Hc
A1 A2 A3 W Wr Wfa Cnf Cmfa Cnfr Cws.
unfold apart in A1, A2, A3.
eassert (RUN1 : msteps ASEGS (mkst regs (0x54c4c : word) M rom) _).
{ zld (ltac:(oF' 0x54c4c%Z)) (ltac:(oD' 0x54c4c%Z)) (r + 16) Cnf.
zstep (ltac:(oF' 0x54c50%Z)) (ltac:(oD' 0x54c50%Z)). zstep (ltac:(oF' 0x54c54%Z)) (ltac:(oD' 0x54c54%Z)). zstep (ltac:(oF' 0x54c58%Z)) (ltac:(oD' 0x54c58%Z)). zstep (ltac:(oF' 0x54c5c%Z)) (ltac:(oD' 0x54c5c%Z)).
stepn (ltac:(oF' 0x54c60%Z)) (ltac:(oD' 0x54c60%Z)).
zcall (art_efas_warm_fn _ _ _ (0x54c64 : word) (sp - 128) r (nf + n) mfa).
zbft (ltac:(oF' 0x54c64%Z)) (ltac:(oD' 0x54c64%Z)).
zbft (ltac:(oF' 0x54c68%Z)) (ltac:(oD' 0x54c68%Z)).
zstep (ltac:(oF' 0x54c6c%Z)) (ltac:(oD' 0x54c6c%Z)). zstep (ltac:(oF' 0x54c70%Z)) (ltac:(oD' 0x54c70%Z)). zstep (ltac:(oF' 0x54c74%Z)) (ltac:(oD' 0x54c74%Z)). zstep (ltac:(oF' 0x54c78%Z)) (ltac:(oD' 0x54c78%Z)).
apply mst_refl. }
unfold art_efas_frame in RUN1.
assert (Hlen : (1 <= length ws)%nat) by lia.
match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA X1 (chp + 4 * Z.of_nat j) 4 (nth j ws 0))
by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
assert (Wfa1 : wrA X1 (rb + 3758096384 + 4 * nf) (4 * Z.of_nat (length ws))) by (repeat apply wr_Wn; eapply wr_sub; [exact Wfa|lia|lia]);
assert (Cnfr1 : cellA X1 (r + 80) 8 nfr) by zcell;
assert (Wr1 : wrA X1 r 128) by zwr;
assert (G1 : mem_grows M X1) by zgrows;
assert (AG1 : art_agree [(sp - 176, 48)] M X1) by (eapply art_agree_sub; [zagree|]; zsub);
destruct (art_rta_copy ws R1 X1 rom (rb + 3758096384 + 4 * nf) chp (chp + 4 * n) ltac:(gres; f_equal; lia) ltac:(gres; rwH; reflexivity) ltac:(gres; f_equal; lia)
ltac:(lia) Hlen ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia) Wfa1 Cws1) as (r2 & RUN2 & K2);
gkeep3 K2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -128)); gkeep3 K2 r2 (8%bv : reg) (Z_to_bv 64 r); gkeep3 K2 r2 (18%bv : reg) (Z_to_bv 64 c);
gkeep3 K2 r2 (19%bv : reg) (Z_to_bv 64 mp); gkeep3 K2 r2 (20%bv : reg) (Z_to_bv 64 ia); gkeep3 K2 r2 (21%bv : reg) (Z_to_bv 64 n); gkeep3 K2 r2 (23%bv : reg) (Z_to_bv 64 (nf + n));
set (X2 := art_w4s X1 (rb + 3758096384 + 4 * nf) ws) in *;
assert (Cnfr2 : cellA X2 (r + 80) 8 nfr) by (apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|exact Cnfr1]);
assert (Wr2 : wrA X2 r 128) by (eapply wr_grows; [apply art_w4s_grows|exact Wr1]);
assert (G2 : mem_grows X1 X2) by (apply art_w4s_grows);
assert (AG2 : art_agree [(rb + 3758096384 + 4 * nf, 4 * n)] X1 X2) by (intros x Hx; cbn [art_out fst snd] in Hx; apply art_w4s_outside; [lia|lia|rewrite <- En; tauto]);
assert (CW2 : forall j, (j < length ws)%nat -> cellA X2 (rb + 3758096384 + 4 * nf + 4 * Z.of_nat j) 4 (nth j ws 0))
by (intros j Hj; apply cell_w4s_nth; [lia|lia|exact Hj|intros k Hk; destruct (Cws k Hk) as [Rk _]; lia])
end.
clearbody X2.
match type of RUN2 with msteps _ _ ?S2 => eassert (RUN3 : msteps ASEGS S2 _) end.
{ zld (ltac:(oF' 0x54c90%Z)) (ltac:(oD' 0x54c90%Z)) (r + 80) Cnfr2.
zsd (ltac:(oF' 0x54c94%Z)) (ltac:(oD' 0x54c94%Z)) (r + 16) (nf + n) ltac:(zwok').
zstep (ltac:(oF' 0x54c98%Z)) (ltac:(oD' 0x54c98%Z)).
zsd (ltac:(oF' 0x54c9c%Z)) (ltac:(oD' 0x54c9c%Z)) (r + 80) (nfr + n) ltac:(zwok').
zstep (ltac:(oF' 0x54ca0%Z)) (ltac:(oD' 0x54ca0%Z)). zstep (ltac:(oF' 0x54ca4%Z)) (ltac:(oD' 0x54ca4%Z)). zstep (ltac:(oF' 0x54ca8%Z)) (ltac:(oD' 0x54ca8%Z)). zstep (ltac:(oF' 0x54cac%Z)) (ltac:(oD' 0x54cac%Z)).
stepn (ltac:(oF' 0x54cb0%Z)) (ltac:(oD' 0x54cb0%Z)).
apply mst_refl. }
eexists. eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
split; [gres; bveq|]. split; [gres; rwH; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split. { intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rewrite K2 by reg_neq_tac; gres; first [reflexivity | rwH; reflexivity]|]). destruct Hx. }
split. { eapply mem_grows_trans; [exact G1|]. eapply mem_grows_trans; [exact G2|]. zgrows. }
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|]; zagree|]. zsub. }
split; [zcell|]. split; [zcell|].
intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. replace (rb + 3758096384 + 4 * (nf + Z.of_nat j)) with (rb + 3758096384 + 4 * nf + 4 * Z.of_nat j) by lia.
apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. exact (CW2 j Hj).
Qed.
End SE.
Ltac zcl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ =>
let v := eval vm_compute in (bv_unsigned x) in replace x with (Z_to_bv 64 v : word) by (apply bv_eq; vm_compute; reflexivity) end.
Section SE.
Local Abbreviation SEC_T_art_rta_tail_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle3R "YN&By5'RByR0%211%5241'5y8%611%311p061'@':&OrE(R@+2(8%33A21%6251&RA&Q;rA+T0%3221%52F1%>3F71rF+8%>3L1<%A231%;2L9%D3L21rG+H%D3Q21B%G231&Q:+QM%22G1%D2Q51%M3Q551&Q6rD%22E1&Q7+R0%:2O1%32Q21&Q5&Q8rB%22M1%42:1%Q:3Q;Q81%52Q0<%Q<3Q=Q:1z%@21O'9+1%C21Q?+O%E2QA1%5231rI%A21Q;%F21D&FrJrK%QB21Q@%443Q<1QA&KrM%211rH%Q32D1%Q122O%D221&H&Q3rQ<rQ8u8%544321&GrQ=rQ9+QL%QE2R:1%55:4371rQ>+RQP0+ZooooPPPPoooO%95>32;1rQ?%R<2?R5&RC%12S0<%>5C43@1rQ@+@%RB2@1%B5G31DErQA%RE2>R8%E5J21GHrQB+Q0%RI2>1%I5N31KLrQC+Q8%RM2=1%M5Q231OQ0rQD+Q@%S12=1%Q15Q631Q3Q4rQE+QH%S52>1%Q55Q:31Q7Q8rQF%S82=R?%Q85Q=21Q:Q;rQG+R8%S<2=1%Q<5QA31Q>Q?rQH+R@%S@2=1%Q@5QE31QBQCrQI+RH%SD2=1%QD5QI31QFQGrQJ+S0%SH2>1%QH5QM31QJQKrQK+S8%SL2>1%QL5R131QNQO'J&Q0vQ?rQM+ZcUD%T93TE1T7/01TErQL%756521<&Q1%T>3TLS1T<%2381C%T;2TLH%432T>1+5%TC3U11TA%T?2U0S:%83421+6%TG3U51TE+QPPPPPPPPPPP0%TD2U51%=3531+7%TL3U:1TJ%@3319%TI2U:QI%B32TA1+9%U13U?1TO%TM2U>R1%F3421+:%U53UC1U3%I331=+;%U83UF1U6%L331E+<%U;3UI1U9+VPPPPPPPPPPP0%U82UI1%Q13531+=%U@3UN1U>%U<2UMS2%Q53421+>%UD3V21UB+^oooooooooooO%UA2V21%Q:3531+?%UI3V71UG+ooooPPPPPPP0%UF2V71%Q?3531%UM3V;S6UK+_ooooPPPPPPP0%UJ2V;1%QC3431+A%V23V@1V0+TPPPPPPPPPPP0%UO2V@1%QH3531+B%V73VE1V5%V32VDS;%QL3421+C%V;3VI1V9%V72VHSB%R03421+D%V?3VM1V=%V;2VLSJ%R43421+E%VC3W11VA%V?2W0T3%R83421+F%VG3W51VE%VC2W4T;%R<3421+G%VK3W91VI%VG2W8TD%R@3421%VI2W:TK%RB32V;1+I%W13W?1VOrQ;%VN2W?1%RG3531+J%W63WD1W4rQ:%W32WD1%RL3531+K%W;3WI1W9%W72WHU3%S03421&E%14U:S4SKV5%S;5S:3SD1S@%S=3U?S51p0S?1p0SD1p0SI1p0SN1p0T31p0T81p0T<1p0TA1p0TF1p0TK1p0U01p0U41p0U91p0U?1p0UD1p0UK1p0V21p0V31p0V41p0V51p0V61p0V71p0V81p0V91p0V:1p0V;1p0V<1p0V=1p0VB1p0VF1p0VL1p0W01p0W71p0W:1p0W=1p0WD1p0WI1p0WM1p0X71p0X>1pSDXN1pSBXO1pS@Y01pS>Y11pS<Y21pS:Y31pS8Y41pS6Y51pS4Y61pS2Y71pSHY81pSFY91pRJY:1pT8Y;1pTDY<1pT:Y=1pTJY>1pT<YF1pTFYA1pQ8YB1pT@YH1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 4%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 5%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 6%nat 0%nat).
Variable qris : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 7%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 8%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 9%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 10%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 11%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 12%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 13%nat 0%nat).
Variable g21 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 14%nat 0%nat).
Variable g22 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 15%nat 0%nat).
Variable g23 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 16%nat 0%nat).
Variable g24 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 17%nat 0%nat).
Variable g25 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 18%nat 0%nat).
Variable g26 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 19%nat 0%nat).
Variable g27 : ltac:(sec_ty2 constr:(SEC_T_art_rta_tail_fn) 20%nat 0%nat).
Lemma art_rta_tail_fn : ltac:(sec_stmt2 constr:(SEC_T_art_rta_tail_fn) 21%nat 0%nat).
Proof using Type regs M rom raw sp r ris qris c g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27.
intros H2 H8 H24 Hsp Hsp' Er Eris Hris Hc Hr' Ar Hret
Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24 Hg25 Hg26 Hg27 Wst Cst Crd F8 F16 F24 F32 F40 F48 F56 F64 F72 F80 F88 F96 F104.
assert (Hr8 : r mod 8 = 0). { rewrite Er, Eris. replace (128 * qris + 128 * c) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
zld (ltac:(oF' 0x54cb4%Z)) (ltac:(oD' 0x54cb4%Z)) r Cst.
stepn (ltac:(oF' 0x54cb8%Z)) (ltac:(oD' 0x54cb8%Z)). zcl. stepn (ltac:(oF' 0x54cbc%Z)) (ltac:(oD' 0x54cbc%Z)). zcl. stepn (ltac:(oF' 0x54cc0%Z)) (ltac:(oD' 0x54cc0%Z)). zcl.
stepn (ltac:(oF' 0x54cc4%Z)) (ltac:(oD' 0x54cc4%Z)).
stepn (ltac:(oF' 0x54cc8%Z)) (ltac:(oD' 0x54cc8%Z)). zcl. stepn (ltac:(oF' 0x54ccc%Z)) (ltac:(oD' 0x54ccc%Z)). zcl. stepn (ltac:(oF' 0x54cd0%Z)) (ltac:(oD' 0x54cd0%Z)). zcl.
zld (ltac:(oF' 0x54cd4%Z)) (ltac:(oD' 0x54cd4%Z)) 0x10400 Crd.
stepn (ltac:(oF' 0x54cd8%Z)) (ltac:(oD' 0x54cd8%Z)). zcl. stepn (ltac:(oF' 0x54cdc%Z)) (ltac:(oD' 0x54cdc%Z)). zcl. stepn (ltac:(oF' 0x54ce0%Z)) (ltac:(oD' 0x54ce0%Z)). zcl. stepn (ltac:(oF' 0x54ce4%Z)) (ltac:(oD' 0x54ce4%Z)). zcl. stepn (ltac:(oF' 0x54ce8%Z)) (ltac:(oD' 0x54ce8%Z)). zcl.
stepn (ltac:(oF' 0x54cec%Z)) (ltac:(oD' 0x54cec%Z)).
stepn (ltac:(oF' 0x54d08%Z)) (ltac:(oD' 0x54d08%Z)). zcl. stepn (ltac:(oF' 0x54d0c%Z)) (ltac:(oD' 0x54d0c%Z)). zcl.
zbft (ltac:(oF' 0x54d10%Z)) (ltac:(oD' 0x54d10%Z)).
stepn (ltac:(oF' 0x54d14%Z)) (ltac:(oD' 0x54d14%Z)). zcl.
zbtk (ltac:(oF' 0x54d18%Z)) (ltac:(oD' 0x54d18%Z)).
stepn (ltac:(oF' 0x54d3c%Z)) (ltac:(oD' 0x54d3c%Z)). rwH. zcl. stepn (ltac:(oF' 0x54d40%Z)) (ltac:(oD' 0x54d40%Z)). zcl. stepn (ltac:(oF' 0x54d44%Z)) (ltac:(oD' 0x54d44%Z)). zcl. stepn (ltac:(oF' 0x54d48%Z)) (ltac:(oD' 0x54d48%Z)). zcl. stepn (ltac:(oF' 0x54d4c%Z)) (ltac:(oD' 0x54d4c%Z)). zcl.
stepn (ltac:(oF' 0x54d50%Z)) (ltac:(oD' 0x54d50%Z)). zcl. stepn (ltac:(oF' 0x54d54%Z)) (ltac:(oD' 0x54d54%Z)). zcl.
zbtk (ltac:(oF' 0x54d58%Z)) (ltac:(oD' 0x54d58%Z)).
chain_step; [reflexivity
| eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r) _ (Z_to_bv 64 (2 ^ 60)));
[exact (ltac:(oF' 0x54cf0%Z)) | reflexivity | exact (ltac:(oD' 0x54cf0%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
| exact Cst | apply bytes_le_to_Z_8 ]
| ]. wpc.
chain_step; [reflexivity
| eapply art_step_branch_ft_r; [exact (ltac:(oF' 0x54cf4%Z)) | reflexivity | exact (ltac:(oD' 0x54cf4%Z)) | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite ?art_u_lit by lia; rewrite Z.eqb_refl; reflexivity ]
| ]. wpc.
chain_step; [reflexivity
| eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r));
[exact (ltac:(oF' 0x54cf8%Z)) | reflexivity | exact (ltac:(oD' 0x54cf8%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wst ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 r) (word_to_le_bytes 8 (Z_to_bv 64 0))) with (Wn 8 M0 r 0).
zbft (ltac:(oF' 0x54cfc%Z)) (ltac:(oD' 0x54cfc%Z)).
zbtk (ltac:(oF' 0x54d00%Z)) (ltac:(oD' 0x54d00%Z)).
zbft (ltac:(oF' 0x54d68%Z)) (ltac:(oD' 0x54d68%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (E8 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (E16 : cellA X (sp - 16) 8 g8) by zcell; assert (E24 : cellA X (sp - 24) 8 g9) by zcell;
assert (E32 : cellA X (sp - 32) 8 g18) by zcell; assert (E40 : cellA X (sp - 40) 8 g19) by zcell; assert (E48 : cellA X (sp - 48) 8 g20) by zcell;
assert (E56 : cellA X (sp - 56) 8 g21) by zcell; assert (E64 : cellA X (sp - 64) 8 g22) by zcell; assert (E72 : cellA X (sp - 72) 8 g23) by zcell;
assert (E80 : cellA X (sp - 80) 8 g24) by zcell; assert (E88 : cellA X (sp - 88) 8 g25) by zcell; assert (E96 : cellA X (sp - 96) 8 g26) by zcell;
assert (E104 : cellA X (sp - 104) 8 g27) by zcell end.
zld (ltac:(oF' 0x54d6c%Z)) (ltac:(oD' 0x54d6c%Z)) (sp - 8) E8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54d70%Z)) (ltac:(oD' 0x54d70%Z)) (sp - 16) E16. zld (ltac:(oF' 0x54d74%Z)) (ltac:(oD' 0x54d74%Z)) (sp - 24) E24. zld (ltac:(oF' 0x54d78%Z)) (ltac:(oD' 0x54d78%Z)) (sp - 32) E32. zld (ltac:(oF' 0x54d7c%Z)) (ltac:(oD' 0x54d7c%Z)) (sp - 40) E40.
zld (ltac:(oF' 0x54d80%Z)) (ltac:(oD' 0x54d80%Z)) (sp - 48) E48. zld (ltac:(oF' 0x54d84%Z)) (ltac:(oD' 0x54d84%Z)) (sp - 56) E56. zld (ltac:(oF' 0x54d88%Z)) (ltac:(oD' 0x54d88%Z)) (sp - 64) E64. zld (ltac:(oF' 0x54d8c%Z)) (ltac:(oD' 0x54d8c%Z)) (sp - 72) E72.
zld (ltac:(oF' 0x54d90%Z)) (ltac:(oD' 0x54d90%Z)) (sp - 80) E80. zld (ltac:(oF' 0x54d94%Z)) (ltac:(oD' 0x54d94%Z)) (sp - 88) E88. zld (ltac:(oF' 0x54d98%Z)) (ltac:(oD' 0x54d98%Z)) (sp - 96) E96. zld (ltac:(oF' 0x54d9c%Z)) (ltac:(oD' 0x54d9c%Z)) (sp - 104) E104.
zstep (ltac:(oF' 0x54da0%Z)) (ltac:(oD' 0x54da0%Z)).
stepret (ltac:(oF' 0x54da4%Z)) (ltac:(oD' 0x54da4%Z)) raw ltac:(reflexivity).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rta_run := (ltac2:(TCodec.tc2 tcn__JbtRecycle3R "]B'2'@%211&By5'RByR0%211%5241'5y8%611%311p061':&OrB(R@+1(8%33@21%6251r?%93@21&Kr@%211rD+2%<3I1:%?231&RA%12J7%C3J31rE+:%C3Q01A%F231%72Q0@%I3Q021rF+;%I3Q61G%L231%N3Q516rG+<%N3Q;1L%Q1231%Q33Q:1;rH+=%Q33Q@1Q1%Q6231%Q83Q?1@rI+>%Q83QE1Q6%Q;231%Q=3QD1ErJ+?%Q=3QJ1Q;%Q@231%QB3QI1J&Q6+Vb\P0%221K&Q;+V@%22D1%62J1&Q7&Q:+R0%22Q?1%42E1&Q5+XPPP0%22H1+Q?%82QE1%A231+RPP0%C21M+TP0%92J1%F21E'9%H2R7Q7+N%J2Q91%4231+Q5%E2R21%B2QB1%RB3ROQH1&Q8+T0%221QK%RF3S3QG1%H2QC@rQ0%Q6221rK&Q9&1rQ7%22S;1%411%S03S=61rL%Q?2RN1+@%QA231%K231rN%QD2Q01rO+4%G214%Q<231rQ4%QJ221&F%L267%QA2Q0Q9%34I2;1z%R021B+Q8%QJ2S71%QL2E1%Q=241rMrQ1%QK221%Q82B1%R921K+M%R32S@1%R<271%R=2>8%R729R4%QH221rQ8%RA2B1%R;22R8%QL221&I&Q3rQ@rQ=%RE21RD%54431RErQArQ5rQ9%QM2QL1%RB231%;4:51QNrQBrQ:+Q0%RK2T81%R4231%RI2QK1+S`PPPP0%RK221rQ3%E4D921&GrQCrQ>%S121;u8%55J421OrQDrQ?+Q@%S7221%:5O416Q4rQE%S:2Q0QEu4+SoooooO%?5Q44321rQF+QV`l0+QiaW0%C5Q832?1rQG%E5Q:13AS;rQH+RQP0+ZooooPPPPoooO%I5Q>32E1rQI%S52S4Q;%SJ2Q?1%M5QB31IR8rQJ%S92S8Q9%SN2N1%SO21RKrQ<%Q35QH52O1rQK%S?2S>Q4%T42O1+H%T6221%Q95QN51Q57rQL%SE2SDQ5%T:2R01+R@%T<221%Q?5R451Q;='3&>r1rR0%SE2VN1%4231&?r2rR1%34W321S4%U42S51+O%TN2V;1%U0241%TA241rQO%T219%T;2SE1%U02QB1%R35RH41QF:%TG261p0@1pSLF1';'J&Q0vQ?+Zbh0%W63WA1W4/01WA%554F1K?rQN%756I1NA%93S631%W>2KW0rQM%W02WI1%WB3WI31%WL1WM&Q4(0+3%WD3X11WB%WE3X2T?WC+8%WG3X41WE+9%WI3X61WG+B%WK3X81WI+C%WM3X:1WK+D%WO3X<1WM+E%X13X>1WO+F%X33X@1X1+G%X53XB1X3%X63XCR5X4+I%X83XE1X6+J%X:3XG1X8+K%X<3XI1X:(4%11N%M3O31%N3Q061%O3Q191%Q03Q2<1%Q13Q3>1%Q23Q4A1%Q33Q5D1%Q43Q6G1%Q53Q7J1%Q63Q8M1%Q73Q9Q01%Q83Q:Q31%Q93Q;Q61%Q:3Q<Q81%Q<3Q=RA1r4%Y121R>rR3%Y321R@%Y53Y<31p061pU<QD1&Q2%12RIRJ&L'7%12YIYI(6%WH2QNWG%24YLYL1WH%VM2SMTJ%WB2T91%WC21TI%W02V:U0%WE221%W22V<T8%94Z3Z321%W42W3T4%WI2TE1%<4Z6Z61R0%WK22VG%>4Z8Z81R2%WM24SB%@4Z:Z:1R4%Q>1B%R:3C21%R;3D51%R<3E81%R=3F<1%R>3GD1%J31SDSE%U85UMSF=U4VC%X72UCTI%U:5UOSH=U61%X92UOTK%U<5V1SJ=U81%W>2ZGQ7%SM2SL1r3%WJ2TBUG%X?2TM1%X@21UF%XA2U=SC%WN2W81%XC231rR4%T14[1T01W2%UH5V=93U;1p0;1pSLT:1%X>2?1%X?2B1%X@2E1%XA2G1%XB2QC1%XC2QF1%XD2S<1%XE2SA1qQ:[11%SM2[21qTB[81%SO2[91p0T11p0TI1p0U01p0U71p0U>1p0UC1p0UH1p0UK1p0V01p0V61p0V<1p0VC1p0VN1p0W51p0W<1p0W=1p0WB1p0WF1p0WJ1p0X01p0X71p0X<1p0XC1p0XF1p0XL1p0Y41p0Y81p0Y=1p0Z;1p0YC1p0YI1p0YM1p0Z01p0Z71p0Z=1p0ZB1p0ZF1p0ZL1p0[21p0[81p0[>1p0[D1p0[K1p0\31p0\71pT6\N1pSN\O1pT4]01pT8]11pTD]21pTL]31pT2]41pRL]51pRJ]61pU0]71pT0]81pSJ]91pQ4]:1pTJ];1pT<]61pTF]11pQ8]21pT@]81pU:]?1")) (only parsing).
Variable ws : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 2%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 3%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 4%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 5%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 6%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 7%nat 0%nat).
Variable mp : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 8%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 9%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 10%nat 0%nat).
Variable chp : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 11%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 12%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 13%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 14%nat 0%nat).
Variable qris : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 15%nat 0%nat).
Variable nf : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 16%nat 0%nat).
Variable mfa : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 17%nat 0%nat).
Variable nfr : ltac:(sec_ty2 constr:(SEC_T_art_rta_run) 18%nat 0%nat).
Lemma art_rta_run : ltac:(sec_stmt2 constr:(SEC_T_art_rta_run) 19%nat 0%nat).
Proof using Type ws regs M rom raw sp HI ia mp st c chp n spb ris qris nf mfa nfr.
intros H1 Hret H2 H10 H11 H12 H13 H14 H15 HHI Hsp Hsp' HHI' Hia Hia' Hc Hspb Eris Eq Hris' En Hn Hchp Hchp' Achp
Hnf Hmfa Hmfa' Hnfr Hmp Hst W Wr Wfa Cspb Cris Crel Cpc Cpg Crd Cmx Cnf Cmfa Cnfr Cws.
set (r := ris + 128 * c) in *. set (rb := spb + c * 2 ^ 32) in *.
assert (Hr : 0x693000 <= r /\ r + 128 <= HI) by (unfold r; lia). destruct Hr as (Hr & Hr').
assert (Hrb : 0x693000 <= rb /\ rb + 2 ^ 32 <= ris) by (unfold rb; lia). destruct Hrb as (Hrb & Hrb').
unfold apart in Achp.
pose proof (art_rta_lock_fn regs M rom raw sp ia mp st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 H15 ltac:(lia) Hsp' Hia Hia' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Eq
ltac:(unfold apart; fold r; lia) Hmp Hst ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Wr Cspb Cris Cmx) as RUN1.
fold r in RUN1. unfold art_gfa_frame in RUN1.
match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
assert (F1 : mem_grows M X1 /\ art_agree [(sp - 208, 208); (r, 8)] M X1) by (split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
assert (C1 : cellA X1 r 8 (2 ^ 60) /\ cellA X1 (r + 16) 8 nf /\ cellA X1 (r + 24) 8 mfa /\ cellA X1 (r + 80) 8 nfr
/\ cellA X1 (ia + 48) 8 ris /\ cellA X1 (ia + 40) 4 0xffffffff /\ cellA X1 0x134380 8 0x1cc4e0 /\ cellA X1 0x1cc4e0 8 4096 /\ cellA X1 0x10400 8 0xafffff00000fffff
/\ cellA X1 (sp - 8) 8 (U raw) /\ cellA X1 (sp - 16) 8 (U (getr regs 8)) /\ cellA X1 (sp - 24) 8 (U (getr regs 9)) /\ cellA X1 (sp - 32) 8 (U (getr regs 18))
/\ cellA X1 (sp - 40) 8 (U (getr regs 19)) /\ cellA X1 (sp - 48) 8 (U (getr regs 20)) /\ cellA X1 (sp - 56) 8 (U (getr regs 21)) /\ cellA X1 (sp - 64) 8 (U (getr regs 22))
/\ cellA X1 (sp - 72) 8 (U (getr regs 23)) /\ cellA X1 (sp - 80) 8 (U (getr regs 24)) /\ cellA X1 (sp - 88) 8 (U (getr regs 25)) /\ cellA X1 (sp - 96) 8 (U (getr regs 26))
/\ cellA X1 (sp - 104) 8 (U (getr regs 27))) by (repeat split; zcell);
assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA X1 (chp + 4 * Z.of_nat j) 4 (nth j ws 0))
by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
assert (W1 : wrA X1 (sp - 208) 208 /\ wrA X1 r 128 /\ wrA X1 (rb + 3758096384) mfa) by (repeat split; zwr);
set (Ra := R1) in *; set (Xa := X1) in *
end.
destruct F1 as (G1 & AG1). destruct W1 as (W1a & W1r & W1f).
destruct C1 as (Cst1 & Cnf1 & Cmfa1 & Cnfr1 & Cris1 & Crel1 & Cpc1 & Cpg1 & Crd1 & E8 & E16 & E24 & E32 & E40 & E48 & E56 & E64 & E72 & E80 & E88 & E96 & E104).
clearbody Xa.
destruct (art_rta_mid_run ws Ra Xa rom sp HI ia mp c chp n r rb nf mfa nfr ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
ltac:(unfold Ra; gres; reflexivity) HHI ltac:(lia) Hsp' Hr Hr' Hrb ltac:(lia) ltac:(lia) En Hn Hchp Hchp' ltac:(lia) Hmfa Hmfa' Hnfr ltac:(lia) Hmp ltac:(lia)
ltac:(unfold apart, rb; lia) ltac:(unfold apart, r; lia) ltac:(unfold apart, r, rb; lia)
ltac:(eapply wr_sub; [exact W1a|lia|lia]) W1r W1f Cnf1 Cmfa1 Cnfr1 Cws1)
as (r2 & M2 & RUN2 & B1 & B2 & B10 & B11 & B12 & B13 & BK & G2 & AG2 & Cnf2 & Cnfr2 & Cfa2).
set (W2 := [(sp - 176, 48); (rb + 3758096384 + 4 * nf, 4 * n); (r + 16, 8); (r + 80, 8)]) in *.
assert (T2 : forall a (k : nat) v, art_gap W2 a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA Xa a k v -> cellA M2 a k v).
{ intros a k v G Ha Hk C. exact (art_cell_tr W2 Xa M2 a k v AG2 G Ha Hk C). }
assert (GI : forall a k, 0x10000 <= a -> a + k <= 0x693000 -> art_gap W2 a k).
{ intros a k Ha Hk. unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (Cris2 : cellA M2 (ia + 48) 8 ris) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cris1]).
assert (Crel2 : cellA M2 (ia + 40) 4 0xffffffff) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Crel1]).
assert (Cpc2 : cellA M2 0x134380 8 0x1cc4e0) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cpc1]).
assert (Cpg2 : cellA M2 0x1cc4e0 8 4096) by (apply T2; [apply GI; cbn; lia|lia|cbn; lia|exact Cpg1]).
destruct (art_mrtos_ret r2 M2 rom (0x54cb4 : bv 64)%bv (sp - 128) ia c ris (nf + n) ((nfr + n) mod 2 ^ 64) B1 ltac:(unfold ret_ok; bveq) B2 B10 B12 B13 ltac:(lia) ltac:(lia)
ltac:(eapply wr_grows; [exact G2|]; eapply wr_sub; [exact W1a|lia|lia]) Hc Hia ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; fold r; lia) ltac:(lia)
ltac:(apply Z.mod_pos_bound; lia) ltac:(eapply wr_grows; [exact G2|exact W1r]) Cris2 Cpc2 Cpg2 Crel2 Cnf2 ltac:(apply art_cell_norm; exact Cnfr2))
as (r3 & RUN3 & D2 & DK).
destruct (art_f80_facts M2 (sp - 128) (0x54cb4 : bv 64)%bv r2 ltac:(lia) ltac:(lia)) as (G3 & AG3).
set (M3 := art_f80 M2 (sp - 128) (0x54cb4 : bv 64)%bv r2) in *. clearbody M3.
replace (sp - 128 - 80) with (sp - 208) in AG3 by lia.
assert (T3 : forall a (k : nat) v, art_gap W2 a (Z.of_nat k) -> apart a (Z.of_nat k) (sp - 208) 80 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA Xa a k v -> cellA M3 a k v).
{ intros a k v G A Ha Hk C. apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A|exact I]|exact Ha|exact Hk|]. exact (T2 a k v G Ha Hk C). }
assert (GF : forall a k, sp - 128 <= a -> a + k <= sp -> art_gap W2 a k /\ apart a k (sp - 208) 80).
{ intros a k Ha Hk. unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (GR : art_gap W2 r 8 /\ apart r 8 (sp - 208) 80) by (unfold W2; cbn [art_gap fst snd]; unfold apart, r, rb; repeat split; try exact I; lia).
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
pose proof (bv_unsigned_in_range 64 (getr regs 19)) as R19. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as R20. pose proof (bv_unsigned_in_range 64 (getr regs 21)) as R21.
pose proof (bv_unsigned_in_range 64 (getr regs 22)) as R22. pose proof (bv_unsigned_in_range 64 (getr regs 23)) as R23. pose proof (bv_unsigned_in_range 64 (getr regs 24)) as R24.
pose proof (bv_unsigned_in_range 64 (getr regs 25)) as R25. pose proof (bv_unsigned_in_range 64 (getr regs 26)) as R26. pose proof (bv_unsigned_in_range 64 (getr regs 27)) as R27.
change (bv_modulus 64) with (2 ^ 64) in *.
pose proof (art_rta_tail_fn r3 M3 rom raw sp r ris qris c _ _ _ _ _ _ _ _ _ _ _ _ D2
ltac:(rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity) ltac:(rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity)
ltac:(lia) Hsp' eq_refl Eq ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia) Hret R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
ltac:(apply (wr_wok _ _ r 128); [eapply wr_grows; [exact G3|]; eapply wr_grows; [exact G2|exact W1r]|lia|cbn; lia])
ltac:(apply T3; [apply GR|apply GR|lia|cbn; lia|exact Cst1]) ltac:(apply T3; [apply GI; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Crd1])
ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E8]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E16])
ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E24]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E32])
ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E40]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E48])
ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E56]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E64])
ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E72]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E80])
ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E88]) ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E96])
ltac:(apply T3; [apply GF; cbn; lia|apply GF; cbn; lia|lia|cbn; lia|exact E104])) as RUN4.
assert (T4 : forall a (k : nat) v, apart a (Z.of_nat k) (sp - 208) 80 -> apart a (Z.of_nat k) r 8 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M2 a k v -> cellA (Wn 8 M3 r 0) a k v).
{ intros a k v A1 A2 Ha Hk C. apply cell_Wn_other; [lia|cbn; lia|exact Ha|exact Hk|apply apart_sym; exact A2|].
apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A1|exact I]|exact Ha|exact Hk|exact C]. }
eexists. exists (Wn 8 M3 r 0).
split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|]; exact RUN4|].
split; [gres; reflexivity|].
split. { intros x Hx. cbn [In] in Hx.
destruct Hx as [<-|Hx]; [gres; rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity|].
destruct Hx as [<-|Hx]; [gres; rewrite DK by inl3; rewrite BK by inl3; unfold Ra; gres; reflexivity|].
repeat (destruct Hx as [<-|Hx]; [gres; apply Z_to_bv_bv_unsigned|]). destruct Hx. }
split. { eapply mem_grows_trans; [exact G1|]. eapply mem_grows_trans; [exact G2|]. eapply mem_grows_trans; [exact G3|]. apply Wn_grows. }
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|]; eapply art_agree_trans; [exact AG3|]; apply art_agree_Wn; [lia|cbn; lia]|].
unfold W2. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; lia. }
split; [apply cell_Wn_hit; [lia|cbn; lia]|].
split; [apply T4; [unfold apart; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Cnf2]|].
split; [apply T4; [unfold apart; cbn; lia|unfold apart; cbn; lia|lia|cbn; lia|exact Cnfr2]|].
intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. apply T4; [unfold apart, rb; cbn; lia|unfold apart, r, rb; cbn; lia|unfold rb; lia|unfold rb; cbn; lia|exact (Cfa2 j Hj)].
Qed.
End SE.
End FPX.
