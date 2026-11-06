(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG JbtFree1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRefill1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRefill1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1length"; "1list"; "1nat"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3le"; "3lt"; "4nth"; "5Z"; "6bvmap"; "0M"; "7Wn"]; ["7apart"; "7cell"; "7wr"; "8msteps"; "9ret_ok"; ":art_gfa_frame"; ":art_w4s"; ";getr"; ";mkst"; ";regupd"; "<mem_grows"; "=loaded_segments"; ">add"; ">le"; ">lt"; ">mul"]; [">of_nat"; ">pow"; ">sub"; "0b"; "0c"; "0chp"; "0dend"; "0dst"; "0fa"; "0fx"; "0g18"; "0g19"; "0g20"; "0g21"; "0g22"; "0g23"]; ["0g24"; "0g25"; "0g26"; "0g27"; "0g8"; "0g9"; "0i"; "0ia"; "0j"; "0m"; "0n"; "0na"; "0nf"; "0qris"; "0r"; "0raw"]; ["0regs"; "0regs'"; "0ris"; "0rom"; "0sp"; "0spb"; "0src"; "0st"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_unsigned"; "0u"; "0ws"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Ltac zlhu F D a HYP :=
chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.
Definition art_gfa_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
(Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (bv_unsigned raw)) (sp - 16) (bv_unsigned (getr regs 8))) (sp - 24) (bv_unsigned (getr regs 9))) (sp - 32) (bv_unsigned (getr regs 18))) (sp - 40) (bv_unsigned (getr regs 19))) (sp - 48) (bv_unsigned (getr regs 20))) (sp - 56) (bv_unsigned (getr regs 21))) (sp - 64) (bv_unsigned (getr regs 22))) (sp - 72) (bv_unsigned (getr regs 23))) (sp - 80) (bv_unsigned (getr regs 24))) (sp - 88) (bv_unsigned (getr regs 25))) (sp - 96) (bv_unsigned (getr regs 26))) (sp - 104) (bv_unsigned (getr regs 27))).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_gfa_lock_fn := (ltac2:(TCodec.tc2 tcn__JbtRefill1 "XF&=y5'R:yR0%211%5241'3y8%611%311p061'<'6&Gr=(R8+1(4%33A21%6251r:%93A21r>+2%93G17%<231&R9%12H7%@3H31r?+:%@3N1>%C231%E3M16r@+;%E3Q31C%H231%J3Q21;rA+<%J3Q81H%M231%O3Q71@rB+=%O3Q=1M%Q2231%Q43Q<1ErC+>%Q43QB1Q2%Q7231%Q93QA1J&M+T0%221F&N&Q1+R0%22Q51%42F1&L+Vb\P0%2219%;21E+RPP0%=21G+TP0%72D1%@217'5%B2QHL+O%D2N1%4231z%G21Q;+Q5%E2QH1%B2Q91+Q?%H2QK1%J231%N28Q=&O%12OK%I2Q;1%O216%42Q2Q=%R>3R?Q91&@rDrH%92Q71%Q1231&Q2rK%221Q;%844Q<1Q<rJ%Q?2I1%Q=22Q:%Q0221rI%QC2M1%QA22Q>%Q4221&B&KrQ2rO%@21QI%54431QJrQ3rM%O2QM1%QG2=1%:4941QO&ArQ4rQ0+Q0%QM221u8%65@521LrQ5rQ1+Q@%R3221%;5E416Q1rQ6rL%Q@2R><%R8221%@5J41;QK'C&HvQ9rQ8+ZkbL%SN3T:1SL/01T:rQ7%756521=&I%QB2JRK%SI2T@1%339SL1+5%T73TE1T5%SM2TDR;%73421+6%T;3TI1T9+QL%S22T51%T32TJ1%=3641+7%TA3TO1T?%@331:+8%TD3U21TB%R?2S=Q5%S72QB1%T<2U31%F3641+9%TJ3U81TH%T@2U7QH%J3421%S>27:%TC2U:1%M33T?1+?%U13U?1TO%Q0331J+@%U43UB1U2%RD2SHU4%TK2UB1%Q53531+A%U93UG1U7%Q8331Q2+C%U<3UJ1U:+QM%T32U61%U42UK1%Q>3641+D%UB3V01U@rN%T92U<R9%S?2R51%T7231+S`PPPP0%T9221%U>2V51%QH3:81+E%UL3V:1UJ+Q8%TC2UF1%UD2V;1%QN3641+F%V23V@1V0%TH2UKB%TE2QG1%SD21V4%UK2VB1%R53751+G%V93VG1V7%R8331QL+H%V<3VJ1V:+Q^L%V32VJ1%R=3531+I%VA3VO1V?%T12U5Q4%T221VB%V92W01%RC3641+Zkm<%VG3W31VE/01W3&?&E%14RKSBS<RO%34S?1R6R?%S35S2851S9%S53T0RM1p0S71p0S=1p0SC1p0SK1p0T11p0T81p0T91p0T>1p0TC1p0TM1p0U01p0U51p0U71p0U>1p0UA1p0UG1p0UK1p0UN1p0V31p0V91p0V=1p0VC1p0VI1p0VO1p0W51p0W;1p0WC1pSLWN1pT6WO1pT<X01pSFX11pR<X21pR:X31pT@X41pS@X51pT:X61pT0X>1pT8X91pNX:1pT2X@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 5%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 7%nat 0%nat).
Variable chp : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 8%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 9%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 10%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 11%nat 0%nat).
Variable qris : ltac:(sec_ty2 constr:(SEC_T_art_gfa_lock_fn) 12%nat 0%nat).
Lemma art_gfa_lock_fn : ltac:(sec_stmt2 constr:(SEC_T_art_gfa_lock_fn) 13%nat 0%nat).
Proof using Type regs M rom raw sp ia st c chp n spb ris qris.
intros H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hc Hspb Hspb' Hris Hris' Eris Ar Hst Hchp Hn W Wr Cspb Cris Cmx.
zstep (ltac:(oF' 0x56e5c%Z)) (ltac:(oD' 0x56e5c%Z)).
zsd (ltac:(oF' 0x56e60%Z)) (ltac:(oD' 0x56e60%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x56e64%Z)) (ltac:(oD' 0x56e64%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x56e68%Z)) (ltac:(oD' 0x56e68%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x56e6c%Z)) (ltac:(oD' 0x56e6c%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd (ltac:(oF' 0x56e70%Z)) (ltac:(oD' 0x56e70%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x56e74%Z)) (ltac:(oD' 0x56e74%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x56e78%Z)) (ltac:(oD' 0x56e78%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x56e7c%Z)) (ltac:(oD' 0x56e7c%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd (ltac:(oF' 0x56e80%Z)) (ltac:(oD' 0x56e80%Z)) (sp - 72) (U (getr regs 23)) ltac:(rewok W).
zsd (ltac:(oF' 0x56e84%Z)) (ltac:(oD' 0x56e84%Z)) (sp - 80) (U (getr regs 24)) ltac:(rewok W). zsd (ltac:(oF' 0x56e88%Z)) (ltac:(oD' 0x56e88%Z)) (sp - 88) (U (getr regs 25)) ltac:(rewok W). zsd (ltac:(oF' 0x56e8c%Z)) (ltac:(oD' 0x56e8c%Z)) (sp - 96) (U (getr regs 26)) ltac:(rewok W).
zsd (ltac:(oF' 0x56e90%Z)) (ltac:(oD' 0x56e90%Z)) (sp - 104) (U (getr regs 27)) ltac:(rewok W).
zstep (ltac:(oF' 0x56e94%Z)) (ltac:(oD' 0x56e94%Z)). zstep (ltac:(oF' 0x56e98%Z)) (ltac:(oD' 0x56e98%Z)). zstep (ltac:(oF' 0x56e9c%Z)) (ltac:(oD' 0x56e9c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (ia + 32) 8 spb) by zcell; assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
zld (ltac:(oF' 0x56ea0%Z)) (ltac:(oD' 0x56ea0%Z)) (ia + 32) Cspb'. zld (ltac:(oF' 0x56ea4%Z)) (ltac:(oD' 0x56ea4%Z)) (ia + 48) Cris'.
zstep (ltac:(oF' 0x56ea8%Z)) (ltac:(oD' 0x56ea8%Z)). zstep (ltac:(oF' 0x56eac%Z)) (ltac:(oD' 0x56eac%Z)). zstep (ltac:(oF' 0x56eb0%Z)) (ltac:(oD' 0x56eb0%Z)). zstep (ltac:(oF' 0x56eb4%Z)) (ltac:(oD' 0x56eb4%Z)). zstep (ltac:(oF' 0x56eb8%Z)) (ltac:(oD' 0x56eb8%Z)). zstep (ltac:(oF' 0x56ebc%Z)) (ltac:(oD' 0x56ebc%Z)).
zstep (ltac:(oF' 0x56ec0%Z)) (ltac:(oD' 0x56ec0%Z)). zstep (ltac:(oF' 0x56ec4%Z)) (ltac:(oD' 0x56ec4%Z)). zstep (ltac:(oF' 0x56ec8%Z)) (ltac:(oD' 0x56ec8%Z)). zstep (ltac:(oF' 0x56ecc%Z)) (ltac:(oD' 0x56ecc%Z)). zstep (ltac:(oF' 0x56ed0%Z)) (ltac:(oD' 0x56ed0%Z)). zstep (ltac:(oF' 0x56ed4%Z)) (ltac:(oD' 0x56ed4%Z)). zstep (ltac:(oF' 0x56ed8%Z)) (ltac:(oD' 0x56ed8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmx' : cellA X (ris + c * 2 ^ 7) 8 0) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; zcell);
assert (Wr' : wok AsanUbsan.M.loaded_segments X (ris + c * 2 ^ 7) 8) by (replace (ris + c * 2 ^ 7) with (ris + 128 * c) by lia; rewok Wr) end.
zld (ltac:(oF' 0x56edc%Z)) (ltac:(oD' 0x56edc%Z)) (ris + c * 2 ^ 7) Cmx'.
zstep (ltac:(oF' 0x56ee0%Z)) (ltac:(oD' 0x56ee0%Z)).
zstep (ltac:(oF' 0x56ee4%Z)) (ltac:(oD' 0x56ee4%Z)). zstep (ltac:(oF' 0x56ee8%Z)) (ltac:(oD' 0x56ee8%Z)).
stepn (ltac:(oF' 0x56eec%Z)) (ltac:(oD' 0x56eec%Z)). rwH. try rewrite art_zb_slli by lia.
zstep (ltac:(oF' 0x56ef0%Z)) (ltac:(oD' 0x56ef0%Z)).
stepn (ltac:(oF' 0x56ef4%Z)) (ltac:(oD' 0x56ef4%Z)). rwH. try (rewrite art_zb_and by lia; rewrite Z.land_0_l).
zbft (ltac:(oF' 0x56ef8%Z)) (ltac:(oD' 0x56ef8%Z)).
stepn (ltac:(oF' 0x56efc%Z)) (ltac:(oD' 0x56efc%Z)). rwH. try (unfold v_or; rewrite !art_u_lit by lia; rewrite Z.lor_0_l).
stepn (ltac:(oF' 0x56f00%Z)) (ltac:(oD' 0x56f00%Z)). rwH. try (rewrite art_zb_and by lia; rewrite art_land_full_l by lia).
assert (Hr8 : (ris + c * 2 ^ 7) mod 8 = 0). { rewrite Eris. replace (128 * qris + c * 2 ^ 7) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
chain_step; [reflexivity
| eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)) _ (Z_to_bv 64 0));
[exact (ltac:(oF' 0x56f04%Z)) | reflexivity | exact (ltac:(oD' 0x56f04%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
| exact Cmx' | apply bytes_le_to_Z_8 ]
| ]. wpc.
chain_step; [reflexivity
| eapply art_step_branch_ft_r; [exact (ltac:(oF' 0x56f08%Z)) | reflexivity | exact (ltac:(oD' 0x56f08%Z)) | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
| ]. wpc.
chain_step; [reflexivity
| eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ris + c * 2 ^ 7)));
[exact (ltac:(oF' 0x56f0c%Z)) | reflexivity | exact (ltac:(oD' 0x56f0c%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wr' ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 (ris + c * 2 ^ 7)) (word_to_le_bytes 8 (Z_to_bv 64 1152921504606846976))) with (Wn 8 M0 (ris + c * 2 ^ 7) (2 ^ 60)).
zbft (ltac:(oF' 0x56f10%Z)) (ltac:(oD' 0x56f10%Z)).
zbtk (ltac:(oF' 0x56f14%Z)) (ltac:(oD' 0x56f14%Z)).
unfold art_gfa_frame. zret.
Qed.
End SE.
End FPX.
Fixpoint art_w4s (M : word -> option byte) (dst : Z) (ws : list Z) : word -> option byte :=
match ws with [] => M | w :: ws' => art_w4s (Wn 4 M dst w) (dst + 4) ws' end.
Lemma art_w4s_grows : ltac2:(TCodec.tc2 tcn__JbtRefill1 "E'1'<%211'R:yR0%211'3y8%511%311p051&Jr2&Fr1r3%33421%6251pR@A1pN91pTLB1").
Proof. induction ws as [|w ws IH]; intros M dst; cbn [art_w4s]. apply mem_grows_refl. eapply mem_grows_trans; [apply Wn_grows | apply IH]. Qed.
Lemma art_w4s_outside : ltac2:(TCodec.tc2 tcn__JbtRefill1 "QK'1'<%211'R:yR0%211'3y8%511%311p051&Mzr2%3221&N&Lr3&O+4&Q0&0r5%22F1%411%7261%:291&Q1+2+R0%3221%@251&8'5r4&R;%12Q0C%J231r6%B2Q61%D11%G2F1%J281%L271%;271%=11'6&Fr7%24;K1?%<1@%53Q:21p071p0F1p0Q81pTNQB1pR@QG1pNQ?1pTLQH1").
Proof.
induction ws as [|w ws IH]; intros M dst x Hd Hd' N; cbn [art_w4s]. reflexivity.
cbn [length] in Hd', N. rewrite IH; [|lia|lia|lia]. rewrite Wn_outside; [reflexivity|lia|cbn; lia|cbn; lia].
Qed.
Lemma cell_w4s_other : ltac2:(TCodec.tc2 tcn__JbtRefill1 "R3'1'<%211'R:yR0%211'3y8%511%311p051'2&Mzr4%3221&N&Lr5&O+4&Q0&0r7%22G1%411%7261%:291&Q1+2+R0%3221%@251%E2D?r6%>1A%C221%E216&@r8r:%C2Q81%E11%H2G1%G1:%7462F1&A&K%25189I>&Fr;r<%332<1r9%85721?Op071p0;1p0D1p0I1p0K1p0Q=1pTJQL1pSDQC1pR8QN1pR@QO1pNQG1pTLR01").
Proof.
induction ws as [|w ws IH]; intros M dst b m u Hd Hd' Hb Hm A C; cbn [art_w4s]. exact C.
cbn [length] in Hd', A. unfold apart in A. apply IH; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|exact C].
Qed.
Lemma cell_w4s_nth : ltac2:(TCodec.tc2 tcn__JbtRefill1 "R7'1'<%211'R:yR0%211'3y8%511%311p051'2&Mzr2%3221&N&Lr3&O+4&Q0&0r5%22G1%411%7261%:291&Q1+2+R0%3221%@251&:r6%=2Q21%32B1r1r8%A2Q61%7231'5&;r9%24Q;N1O%Q12Q01+Q0%C2B1%Q0241%8241p0:1pSBQ81&A&K&Fr7%231FB%Q41Q2%Q72Q61%Q:2I1u4%C4QLQ6GQ@%:596321p0<1p0L1p0Q11p0QC1pS>QH1pR@R31pNQK1pTLR41").
Proof.
induction ws as [|w ws IH]; intros M dst i Hd Hd' Hi Hws; cbn [length] in *. lia.
destruct i as [|i].
- cbn [nth art_w4s]. replace (dst + 4 * Z.of_nat 0) with dst by lia.
apply cell_w4s_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; cbn; lia.
- cbn [nth art_w4s]. replace (dst + 4 * Z.of_nat (S i)) with (dst + 4 + 4 * Z.of_nat i) by lia.
apply IH; [lia|lia|lia|]. intros j Hj. apply (Hws (S j)). lia.
Qed.
Section FPX2. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_gfa_copy : ltac2:(TCodec.tc2 tcn__JbtRefill1 "UH'1'<%211&=y5'R:yR0%211%5241'3y8%611%311p061'6&Gr6(R8+=(4%33@21%6251&R9r3%22B1%;3B41r7+D%;3H19%>231%@3G16r8+;%@3M1>%C231%E3L1;r4&L&O+4&Q0&0r:%22Q:1%411%7261%92N1%Q13Q>;1'9u1r;%:2QB1%4231&Mz%221H&N&Q1+2+R0%3221%52Q31r9%:291r?%H2R01%J11%M2L1%O2J1%=219+TP0r<%C221&@r=rA%Q32R;1%Q511%Q82Q71%645181&B&Kr@r>rB%Q<2RD1%Q>11%QA2Q@1%847651'2&:r1rD%QD2RL1%4231'5&;r2rE%34S221Q=%Q?2Q>1+O%Q=2Q<1%Q?241%9241&ArC%R31:%R62R51%R82K1u4%65N521<%A281p0C1pSBI1'7'C&HvQ9+Zkn@%S73SB1S5/01SB%554N1@Q6+Zko4%S;3SF1S9/01SF&F%13EQDM%;5:Q531Q<%=3Q@71%SC2Q7S>%S=2SMR3%SF3SM21%SF2Q:S9%RM2T5Q4%RO11%S22S11%S42QG1%SD2T41%SM3T461%T71T8&8+<%SN3T;1SL%T234QE1%411%T436QASN%611%T638SMSH%811r5%T821SCrH%T:21SE%T<3TC31p061p091p0<1pSNB1%R02D1%R12L1%R22Q01qT4TJ1%Q@2TK1p0QB1p0R=1p0RG1p0RO1p0S31p0S:1p0S=1p0SD1p0SH1p0SN1p0T;1p0TA1p0TG1pR>U@1pT>UA1pR@UB1pT8U71pNU81pT2U>1pTLUE1").
Proof.
induction ws as [|w ws IH]; intros regs M rom dst src dend H13 H20 H11 Edend Hlen Hd Hd' Hs Hs' IMG A W Cws; cbn [length] in *. lia.
destruct (Cws O ltac:(lia)) as [Rw Cw]. cbn [nth] in Rw, Cw. replace (src + 4 * Z.of_nat 0) with src in Cw by lia.
assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x56fd0 : word) M rom) (mkst regs1 (0x56fe0 : word) (Wn 4 M dst w) rom)
/\ getr regs1 13 = Z_to_bv 64 (dst + 4) /\ getr regs1 20 = Z_to_bv 64 (src + 4) /\ getr regs1 11 = Z_to_bv 64 dend
/\ (forall r : reg, r <> 12%bv -> r <> 13%bv -> r <> 20%bv -> getr regs1 r = getr regs r)).
{ eexists. split.
- zlw (ltac:(oF' 0x56fd0%Z)) (ltac:(oD' 0x56fd0%Z)) src Cw.
zsw (ltac:(oF' 0x56fd4%Z)) (ltac:(oD' 0x56fd4%Z)) dst w ltac:(rewok W).
zstep (ltac:(oF' 0x56fd8%Z)) (ltac:(oD' 0x56fd8%Z)). zstep (ltac:(oF' 0x56fdc%Z)) (ltac:(oD' 0x56fdc%Z)). apply mst_refl.
- repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
destruct STEP as (regs1 & RUN1 & P13 & P20 & P11 & K1).
destruct ws as [|w2 ws2].
-
cbn [length] in *. eexists. split; [|split; [|split]].
+ eapply msteps_trans; [exact RUN1|]. cbn [art_w4s]. zbft (ltac:(oF' 0x56fe0%Z)) (ltac:(oD' 0x56fe0%Z)). replace (dst + 4) with dend by lia. apply mst_refl.
+ gres. rewrite P13. f_equal; lia.
+ gres. rewrite P20. f_equal; lia.
+ intros r N12 N13 N20. gres. apply K1; assumption.
- cbn [length] in *.
assert (RUNb : msteps ASEGS (mkst regs1 (0x56fe0 : word) (Wn 4 M dst w) rom) (mkst regs1 (0x56fd0 : word) (Wn 4 M dst w) rom)).
{ zbtk (ltac:(oF' 0x56fe0%Z)) (ltac:(oD' 0x56fe0%Z)). apply mst_refl. }
unfold apart in A.
destruct (IH regs1 (Wn 4 M dst w) rom (dst + 4) (src + 4) dend P13 P20 P11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(unfold apart; lia) ltac:(apply wr_Wn; eapply wr_sub; [exact W|lia|lia])
ltac:(intros j Hj; destruct (Cws (S j) ltac:(lia)) as [R C]; split; [exact R|];
replace (src + 4 + 4 * Z.of_nat j) with (src + 4 * Z.of_nat (S j)) by lia; apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|exact C]))
as (regs' & RUN2 & Q13 & Q20 & K2).
exists regs'. split; [|split; [|split]].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. cbn [art_w4s]. exact RUN2.
+ exact Q13.
+ rewrite Q20. f_equal. lia.
+ intros r N12 N13 N20. rewrite K2 by assumption. apply K1; assumption.
Qed.
End FPX2.
Section FPX3. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_gfa_mid_fn : ltac2:(TCodec.tc2 tcn__JbtRefill1 "T>&=y5'R:yR0%211%5241'3y8%611%311p061'<'6&Gr8(R8+8(4%33A21%6251&R9r5%22C1%;3C41r9+D%;3I19%>231%@3H16r:+=%@3N1>%C231%E3M1;r;+>%E3Q31C%H231%J3Q21@&Mz%221A&N&L+T0%22@1&Q1+2+R0%3221%8251%<2;F&O+4%221Q8%<2E1%>217%B2AGr<%726I%A221%C21<'5+1%I216%J27O%4221+Q8%F2E1%K2;1&B&KrCrA%44321N&ArDrB+@%Q4221u8r>%75;6321'C&HvQ9rF+Zkm<%R93RE1R7/01RErE%756521?&I+;%R?3RM1R=r@%QB2QAQA%Q=221%QG2I1%R?2S01%83>61+?%RG3S51RE&Q2r?%221:%QF21:%RG2S81%@3861%R22Q03%RJ2S;1%C33RE1+Zkn@%S23S>1S0/01S>&?%R92Q<Q6%24Q5K1<%Q25Q1741Q:%Q43Q@L1p0Q61p0Q?1p0QE1p0QI1p0QO1p0R41p0R61p0R<1p0R>1p0RH1p0RL1p0S21p0S81p0S>1pSJSK1pSFSL1pR<SM1pRBSN1pSNSO1pT8T11pNT21pT2T81").
Proof.
intros regs M rom r fa chp n nf H8 H20 H13 H14 Hr Hr' Hfa Hfa' Hchp Hchp' Hn Hnf Wr Cnf.
zld (ltac:(oF' 0x56fac%Z)) (ltac:(oD' 0x56fac%Z)) (r + 16) Cnf.
zbft (ltac:(oF' 0x56fb0%Z)) (ltac:(oD' 0x56fb0%Z)).
zstep (ltac:(oF' 0x56fb4%Z)) (ltac:(oD' 0x56fb4%Z)).
zsd (ltac:(oF' 0x56fb8%Z)) (ltac:(oD' 0x56fb8%Z)) (r + 16) (nf - n) ltac:(rewok Wr).
zbft (ltac:(oF' 0x56fbc%Z)) (ltac:(oD' 0x56fbc%Z)).
zstep (ltac:(oF' 0x56fc0%Z)) (ltac:(oD' 0x56fc0%Z)). zstep (ltac:(oF' 0x56fc4%Z)) (ltac:(oD' 0x56fc4%Z)). zstep (ltac:(oF' 0x56fc8%Z)) (ltac:(oD' 0x56fc8%Z)). zstep (ltac:(oF' 0x56fcc%Z)) (ltac:(oD' 0x56fcc%Z)).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_gfa_tail_fn := (ltac2:(TCodec.tc2 tcn__JbtRefill1 "ZI&=y5'R:yR0%211%5241'3y8%611%311p061'<'6&GrG(R8+2(4%33A21%6251&R9&Q2rC+T0%3221%52F1%>3F71rH+8%>3L1<%A231%;2L9%D3L21rI+>%D3Q21B%G231%I3Q116rJ+C%I3Q71G%L231&Q1+QM%22L1%I2Q:1%Q23Q:51&M%12IQ2&N+R0%92Q31%32I1&L+Vb\P0%221Q0%921GrF&OrD%22Q51%8241%QB3QCM1%52Q86%QD3QEQB1z%C21Q7'5+1%F21QG+O%H2QI1%5231rM%E21QC%J21H&@rNrO%QJ21QH%443QI1QI%Q22@4%Q125O%@221&DrQ3%211rL%Q92G1%Q822Q6%G221&B&KrQBrQ>%44321R8&ArQCrQ?+R8%Q?221u8rQ=%75;6321rQDrQ@+QL%R12RK1%<5@4371rQE+RQP0+ZooooPPPPoooO%@5D32;1rQF%RM2ARF&R;%12SA<%E5I43@1rQG+@%S32@1%I5M31DCrQH+H%S72?1%M5Q131HGrQI+Q0%S;2?1%Q15Q531LKrQJ+Q8%S?2>1%Q55Q931Q0OrQK+Q@%SC2>1%Q95Q=31Q4Q3rQL+QH%SG2>1%Q=5QA31Q8Q7rQM%SJ2=RM%Q@5QD21Q;Q:rQN%SM2<Q?%QC5QG21Q>Q=rQO+R@%T12<1%QG5QK31QBQArR0+RH%T52<1%QK5QO31QFQErR1+S0%T92=1%QO5R331QJQIrR2+S8%T=2>1%R35R731QNQM'C&HvQ9rR4+Zko4%TJ3U61TH/01U6rR3%756521<&I%TO3U=S:TM%2381C%TL2U=H%432TO1+5%U43UB1U2+QN%T;2U51%U22UC1%:3641+6%U:3UH1U8%U62UGSI%>3421+7%U>3UL1U<%U:2UKRC%B3421%U<2UMR2%D32U41+9%UD3V21UB%U@2V1R:%H3421+:%UH3V61UF%UD2V5T4%L3421+;%UL3V:1UJ%O331B+<%UO3V=1UM%Q2331A+=%V23V@1V0+VPPPPPPPPPPP0%UO2V@1%Q73531%V12VBS6%Q932UC1+?%V93VG1V7+^oooooooooooO%V62VG1%Q>3531%V=3VKS5V;+ooooPPPPPPP0%V:2VK1%QB3431+A%VB3W01V@+_ooooPPPPPPP0%V?2W01%QG3531+B%VG3W51VE%VC2W4SA%QK3421%VE2W6SH%QM32V21+D%VM3W;1VK%VI2W:T0%R13421+E%W13W?1VO%VM2W>T9%R53421+F%W53WC1W3%W12WBTD%R93421+G%W93WG1W7%W52WFTL%R=3421%W<3WJT0W:rQA%W92WJ1%RA3431+I%WA3WO1W?%W=2WNTH%RE3421+J%WE3X31WC%WA2X2U3%RI3421+K%WI3X71WG%WE2X6U;%RM3421+L%WM3X;1WK%S0331RC&?%VJ2SKU<%VK2T2SO%34U<S621%44U=1SNVA%S>5S=6SG1SC%S@3UHS81p0SB1p0SG1p0SL1p0T11p0T61p0T:1p0T>1p0TC1p0TH1p0TM1p0U21p0U71p0U<1p0UB1p0UG1p0UM1p0V61p0V<1p0V=1p0V>1p0V?1p0V@1p0VA1p0VB1p0VC1p0VD1p0VE1p0VF1p0VG1p0VL1p0W01p0W31p0W51p0W;1p0W?1p0WF1p0WI1p0WL1p0X31p0X81p0X=1p0X@1p0XJ1p0Y01p0Y71pS8YG1pS6YH1pS4YI1pS2YJ1pS0YK1pRNYL1pRLYM1pRJYN1pRHYO1pRFZ01pS<Z11pS:Z21pR:Z31pSLZ41pT6Z51pSHZ61pSFZ71pSNZ81pT:Z91pT0ZA1pT8Z<1pNZ=1pT2ZC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 4%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 6%nat 0%nat).
Variable na : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 7%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 8%nat 0%nat).
Variable qris : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 9%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 10%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 11%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 12%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 13%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 14%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 15%nat 0%nat).
Variable g21 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 16%nat 0%nat).
Variable g22 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 17%nat 0%nat).
Variable g23 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 18%nat 0%nat).
Variable g24 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 19%nat 0%nat).
Variable g25 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 20%nat 0%nat).
Variable g26 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 21%nat 0%nat).
Variable g27 : ltac:(sec_ty2 constr:(SEC_T_art_gfa_tail_fn) 22%nat 0%nat).
Lemma art_gfa_tail_fn : ltac:(sec_stmt2 constr:(SEC_T_art_gfa_tail_fn) 23%nat 0%nat).
Proof using Type regs M rom raw sp r n na ris qris c g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27.
intros H2 H8 H14 H19 Hsp Hsp' IMG Er Eris Hris Hc Hr' Ar Hn Hna Hret
Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Hg24 Hg25 Hg26 Hg27 Wr Cna Cst Crd F8 F16 F24 F32 F40 F48 F56 F64 F72 F80 F88 F96 F104.
assert (Hr8 : r mod 8 = 0). { rewrite Er, Eris. replace (128 * qris + 128 * c) with ((16 * qris + 16 * c) * 8) by lia. apply Z_mod_mult. }
zld (ltac:(oF' 0x56fe4%Z)) (ltac:(oD' 0x56fe4%Z)) (r + 72) Cna.
zstep (ltac:(oF' 0x56fe8%Z)) (ltac:(oD' 0x56fe8%Z)).
zsd (ltac:(oF' 0x56fec%Z)) (ltac:(oD' 0x56fec%Z)) (r + 72) (na + n) ltac:(rewok Wr).
zstep (ltac:(oF' 0x56ff0%Z)) (ltac:(oD' 0x56ff0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cst' : cellA X r 8 (2 ^ 60)) by zcell; assert (Crd' : cellA X 0x10400 8 0xafffff00000fffff) by zcell;
assert (Wst : wok AsanUbsan.M.loaded_segments X r 8) by (rewok Wr) end.
zld (ltac:(oF' 0x56ff4%Z)) (ltac:(oD' 0x56ff4%Z)) r Cst'.
zstep (ltac:(oF' 0x56ff8%Z)) (ltac:(oD' 0x56ff8%Z)). zstep (ltac:(oF' 0x56ffc%Z)) (ltac:(oD' 0x56ffc%Z)).
stepn (ltac:(oF' 0x57000%Z)) (ltac:(oD' 0x57000%Z)). zstep (ltac:(oF' 0x57004%Z)) (ltac:(oD' 0x57004%Z)).
stepn (ltac:(oF' 0x57008%Z)) (ltac:(oD' 0x57008%Z)). stepn (ltac:(oF' 0x5700c%Z)) (ltac:(oD' 0x5700c%Z)). stepn (ltac:(oF' 0x57010%Z)) (ltac:(oD' 0x57010%Z)).
zld (ltac:(oF' 0x57014%Z)) (ltac:(oD' 0x57014%Z)) 0x10400 Crd'.
stepn (ltac:(oF' 0x57018%Z)) (ltac:(oD' 0x57018%Z)). stepn (ltac:(oF' 0x5701c%Z)) (ltac:(oD' 0x5701c%Z)). stepn (ltac:(oF' 0x57020%Z)) (ltac:(oD' 0x57020%Z)). zstep (ltac:(oF' 0x57024%Z)) (ltac:(oD' 0x57024%Z)). stepn (ltac:(oF' 0x57028%Z)) (ltac:(oD' 0x57028%Z)).
stepn (ltac:(oF' 0x5702c%Z)) (ltac:(oD' 0x5702c%Z)).
stepn (ltac:(oF' 0x57048%Z)) (ltac:(oD' 0x57048%Z)). stepn (ltac:(oF' 0x5704c%Z)) (ltac:(oD' 0x5704c%Z)).
zbft (ltac:(oF' 0x57050%Z)) (ltac:(oD' 0x57050%Z)).
stepn (ltac:(oF' 0x57054%Z)) (ltac:(oD' 0x57054%Z)).
zbtk (ltac:(oF' 0x57058%Z)) (ltac:(oD' 0x57058%Z)).
stepn (ltac:(oF' 0x5707c%Z)) (ltac:(oD' 0x5707c%Z)). rwH. vnorm. stepn (ltac:(oF' 0x57080%Z)) (ltac:(oD' 0x57080%Z)). stepn (ltac:(oF' 0x57084%Z)) (ltac:(oD' 0x57084%Z)). stepn (ltac:(oF' 0x57088%Z)) (ltac:(oD' 0x57088%Z)). stepn (ltac:(oF' 0x5708c%Z)) (ltac:(oD' 0x5708c%Z)). stepn (ltac:(oF' 0x57090%Z)) (ltac:(oD' 0x57090%Z)). stepn (ltac:(oF' 0x57094%Z)) (ltac:(oD' 0x57094%Z)).
zbtk (ltac:(oF' 0x57098%Z)) (ltac:(oD' 0x57098%Z)).
chain_step; [reflexivity
| eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r) _ (Z_to_bv 64 (2 ^ 60)));
[exact (ltac:(oF' 0x57030%Z)) | reflexivity | exact (ltac:(oD' 0x57030%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8
| exact Cst' | apply bytes_le_to_Z_8 ]
| ]. wpc.
chain_step; [reflexivity
| eapply art_step_branch_ft_r; [exact (ltac:(oF' 0x57034%Z)) | reflexivity | exact (ltac:(oD' 0x57034%Z)) | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite ?art_u_lit by lia; rewrite Z.eqb_refl; reflexivity ]
| ]. wpc.
chain_step; [reflexivity
| eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 r));
[exact (ltac:(oF' 0x57038%Z)) | reflexivity | exact (ltac:(oD' 0x57038%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hr8 | gres; rwH; reflexivity | exact Wst ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 r) (word_to_le_bytes 8 (Z_to_bv 64 0))) with (Wn 8 M0 r 0).
zbft (ltac:(oF' 0x5703c%Z)) (ltac:(oD' 0x5703c%Z)).
zbtk (ltac:(oF' 0x57040%Z)) (ltac:(oD' 0x57040%Z)).
zbtk (ltac:(oF' 0x570a8%Z)) (ltac:(oD' 0x570a8%Z)).
zstep (ltac:(oF' 0x570bc%Z)) (ltac:(oD' 0x570bc%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (E8 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (E16 : cellA X (sp - 16) 8 g8) by zcell; assert (E24 : cellA X (sp - 24) 8 g9) by zcell;
assert (E32 : cellA X (sp - 32) 8 g18) by zcell; assert (E40 : cellA X (sp - 40) 8 g19) by zcell; assert (E48 : cellA X (sp - 48) 8 g20) by zcell;
assert (E56 : cellA X (sp - 56) 8 g21) by zcell; assert (E64 : cellA X (sp - 64) 8 g22) by zcell; assert (E72 : cellA X (sp - 72) 8 g23) by zcell;
assert (E80 : cellA X (sp - 80) 8 g24) by zcell; assert (E88 : cellA X (sp - 88) 8 g25) by zcell; assert (E96 : cellA X (sp - 96) 8 g26) by zcell;
assert (E104 : cellA X (sp - 104) 8 g27) by zcell end.
zld (ltac:(oF' 0x570c0%Z)) (ltac:(oD' 0x570c0%Z)) (sp - 8) E8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x570c4%Z)) (ltac:(oD' 0x570c4%Z)) (sp - 16) E16. zld (ltac:(oF' 0x570c8%Z)) (ltac:(oD' 0x570c8%Z)) (sp - 24) E24. zld (ltac:(oF' 0x570cc%Z)) (ltac:(oD' 0x570cc%Z)) (sp - 32) E32. zld (ltac:(oF' 0x570d0%Z)) (ltac:(oD' 0x570d0%Z)) (sp - 40) E40.
zld (ltac:(oF' 0x570d4%Z)) (ltac:(oD' 0x570d4%Z)) (sp - 48) E48. zld (ltac:(oF' 0x570d8%Z)) (ltac:(oD' 0x570d8%Z)) (sp - 56) E56. zld (ltac:(oF' 0x570dc%Z)) (ltac:(oD' 0x570dc%Z)) (sp - 64) E64. zld (ltac:(oF' 0x570e0%Z)) (ltac:(oD' 0x570e0%Z)) (sp - 72) E72.
zld (ltac:(oF' 0x570e4%Z)) (ltac:(oD' 0x570e4%Z)) (sp - 80) E80. zld (ltac:(oF' 0x570e8%Z)) (ltac:(oD' 0x570e8%Z)) (sp - 88) E88. zld (ltac:(oF' 0x570ec%Z)) (ltac:(oD' 0x570ec%Z)) (sp - 96) E96. zld (ltac:(oF' 0x570f0%Z)) (ltac:(oD' 0x570f0%Z)) (sp - 104) E104.
zstep (ltac:(oF' 0x570f4%Z)) (ltac:(oD' 0x570f4%Z)).
stepret (ltac:(oF' 0x570f8%Z)) (ltac:(oD' 0x570f8%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
End FPX3.
