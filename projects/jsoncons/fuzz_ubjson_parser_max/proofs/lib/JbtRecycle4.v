(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp JbtFree1 JbtPopulate1 JbtCellEx JbtRecycle3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle4."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle4.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0HI"; "4bvmap"]; ["0M"; "0M'"; "5Wf"; "5Wn"; "5cell"; "5wr"; "6class_size"; "6zrange"; "7msteps"; "8art_agree"; "9art_tsd"; ":art_poison_frame"; ";art_f48"; "=art_cbr_stats_mem"; "<art_cas30w_ok"; "<art_cbr_stats_mem"]; [">getr"; ">mkst"; ">v_and"; ">v_divuw"; ">v_or"; ">v_xor"; "?mem_grows"; "@loaded_segments"; "AIn"; "Aforallb"; "Badd"; "Bdiv"; "Bland"; "Ble"; "Blor"; "Blt"]; ["Bmodulo"; "Bmul"; "Bof_nat"; "Bpow"; "Bsub"; "0a"; "0ab"; "0b1"; "0c"; "0cache"; "0cb"; "0ctx"; "0f1"; "0f2"; "0fx"; "0g18"]; ["0g19"; "0g20"; "0g8"; "0g9"; "0hb"; "0i"; "0k"; "0key"; "0m"; "0mu"; "0n"; "0off"; "0r"; "0ra"; "0raw"; "0regs"]; ["0regs'"; "0ris"; "0rom"; "0s0"; "0s1"; "0s2"; "0s3"; "0s4"; "0s5"; "0sp"; "0sp1"; "0spb"; "CBV"; "CZ_to_bv"; "Cbv"; "Cbv_unsigned"]; ["0sz"; "0szi"; "0t"; "0tp"; "0tsd"; "0v"; "0x"; "0y"]]).
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
Ltac zcl4 := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ =>
let v := eval vm_compute in (bv_unsigned x) in replace x with (Z_to_bv 64 v : word) by (apply bv_eq; vm_compute; reflexivity) end.
Lemma art_zb_divuw : ltac2:(TCodec.tc2 tcn__JbtRecycle4 "Q>'='9&Q=zr2%3221&Q?&QC+2+R0%3221%5271%;271%72:9+Q0%8271%:2<1%@241&Q;&Q@r4%2216r3%5221+O%B2A1%D231':'RNyR0%211&Q3&RMr5%2251%326?%5221%B24F%D21B%72:1%=3:41p0?1p0I1p0O1pV@Q<1pV>Q=1").
Proof.
intros x y Hx Hy Hq. unfold v_divuw. rewrite !art_u_lit by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
assert (0 <= x mod 2 ^ 32 / y) by (apply Z.div_pos; [apply Z.mod_pos_bound|]; lia).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_land_31 : ltac2:(TCodec.tc2 tcn__JbtRecycle4 "B'='9&Q=zr1%3221&Q?+Q0%2241%8241':&Q<r2+O%3221%53?13p071pSBA1").
Proof. intros c Hc. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Definition art_cas30w_ok (b1 : Z) : bool :=
bv_eqb (v_xor (Z_to_bv 64 (3 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (3 + 256 * b1)) (Z_to_bv 64 0)) (Z_to_bv 64 255))) (Z_to_bv 64 (256 * b1)).
Lemma art_cas30w_all : ltac2:(TCodec.tc2 tcn__JbtRecycle4 "<':'0&Q9'=&N&Gz+X0%3221%73651(7%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma art_cas30w : ltac2:(TCodec.tc2 tcn__JbtRecycle4 "Q2'='9&Q=zr1%3221&Q?+X0%2241%8241':'RNyR0%211&Q5&RM&Q:+3&QAr2%22=1%5241%72:1&Q2%92<E%;231+WO%<2?1%5231%?271%?2B:%E3B21p0G1pS@Q11").
Proof.
intros b1 Hb. pose proof art_cas30w_all as H. rewrite forallb_forall in H.
specialize (H b1 ltac:(unfold AsanTab.zrange; apply AsanTab.in_ziota; rewrite Z2Nat.id by lia; lia)). unfold art_cas30w_ok, bv_eqb in H.
apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
Ltac zlhu4 F D a HYP :=
chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].
Lemma art_zb_or4 : ltac2:(TCodec.tc2 tcn__JbtRecycle4 "Q0'='9&Q=zr2%3221&Q?&QC+2+R0%3221%5271%;271':'RNyR0%211&Q4&RMr4%2251r3%4271%6231&Q>%1264%82;1%>3;41p0@1p0A1pV@N1pV>O1").
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_cbr_pa1 := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "WE&?y5'RNyR0%211%5241'4y8%611%311p061'=':&Q0r:(RL+1(8%33A21%6251r7%93A21r;+2%93G17%<231&RM%12H7%@3H31r<+:%@3N1>%C231%E3M16r=+;%E3Q31C%H231%J3Q21;&Q=&Q:+Vb\P0+Q@%3221%521N&Q?&QC+R0%22I1%42K1&E&Q7r?&QD%12I<%54431='9z%C21M%>2N;%4221%F2DQ7+Q5%A2Q81%H2Q31+Q?%D2Q;1%F231%M2QDQ7+N%O2Q91%?231+Q0%K2QB1%M2Q=1%C2A1r@&QAr>%2216%Q82L1%Q921Q?%R63R761&DrF+QWTnH%Q>21>u8%55Q5421<';'H&Q1vQNrI+Z`^4%R@3RL1R>/01RLrHrG%8576321r1+Z`cD%RG3S31RE/01S3&LrE%2491F=%@5?7419%B3QI91%S029RE%QI25R4%RE2S<1%S43S<31+8%S33SA1S1%S62?1rD%RK2SB1%S:3SB31+9%S93SG1S7%S<2E1rC%S12SH1%S@3SH31+C%S?3SM1S=%SB2K1%S62SMQ;%SE3SM21+D%SD3T21SB%SG2Q01%S;2T2R6%SJ3T221%SJ2Q3S8rB%S?2T61%SN3T631%SN2Q7S7%S424R=%SC2T:1%T23T:31+<%T13T?1SO%T42Q=1rA%SI2T@1%T83T@31+=%T73TE1T5%T:2QC1%T<3TD15+>%T;3TI1T9%T>2QG1%S72Q2D%T32TJ1%TB3TJ31+?%TA3TO1T?%TD2QM1&F%11A%T:2U11%TI3U141%U41U5&Q8(1+3%TK3U91TI+4%TM3U;1TK+E%TO3U=1TM+F%U13U?1TO+G%U33UA1U1+H%U53UC1U3+I%U73UE1U5+J%U93UG1U7+K%U;3UI1U9(3%11F%E3G31%F3H61%G3I91%H3J<1%I3K?1%J3LB1%K3ME1%L3NH1%M3OK1%O3Q0S21r3r2%UL221rK%UN213%V03V831p071pTJQ81%TG2Q:1%TH2QB1%TI2QI1%TJ2QN1%TK2R51%TL2R:1%TM2R?1%TN2RE1%TO2RK1%U02S21%U12S91%U22S>1qU2VF1%T32VG1p0T51p0T<1p0TD1p0TI1p0TN1p0U51p0U71p0U=1p0UD1p0UJ1p0V11p0V71p0V=1p0VE1pTHW01pSBW11pUHW21pTBW31pSFW41pUDW51pTNW=1pU6W81pQ2W91pU0W?1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 4%nat 0%nat).
Variable cb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 5%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 6%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 7%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 8%nat 0%nat).
Variable off : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa1) 9%nat 0%nat).
Lemma art_cbr_pa1 : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_pa1) 10%nat 0%nat).
Proof using Type regs M rom raw sp cb m spb c off.
intros H1 H2 H10 H11 Hsp Hsp' W Hcb Hspb Hspb' Hc Hoff Em Cspb.
assert (Ediv : (m - spb) / 2 ^ 32 = c).
{ symmetry. apply (Z.div_unique_pos (m - spb) (2 ^ 32) c off); lia. }
destruct (Z_le_gt_dec c 16) as [Lc|Gc].
- eexists. split.
{ zstep (ltac:(oF' 0x541c4%Z)) (ltac:(oD' 0x541c4%Z)).
zsd (ltac:(oF' 0x541c8%Z)) (ltac:(oD' 0x541c8%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x541cc%Z)) (ltac:(oD' 0x541cc%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x541d0%Z)) (ltac:(oD' 0x541d0%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x541d4%Z)) (ltac:(oD' 0x541d4%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x541d8%Z)) (ltac:(oD' 0x541d8%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x541dc%Z)) (ltac:(oD' 0x541dc%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zstep (ltac:(oF' 0x541e0%Z)) (ltac:(oD' 0x541e0%Z)). zstep (ltac:(oF' 0x541e4%Z)) (ltac:(oD' 0x541e4%Z)).
stepn (ltac:(oF' 0x541e8%Z)) (ltac:(oD' 0x541e8%Z)). stepn (ltac:(oF' 0x541ec%Z)) (ltac:(oD' 0x541ec%Z)). zcl4.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1283032 + 32) 8 spb) by zcell end.
zld (ltac:(oF' 0x541f0%Z)) (ltac:(oD' 0x541f0%Z)) (1283032 + 32) Cspb'.
zstep (ltac:(oF' 0x541f4%Z)) (ltac:(oD' 0x541f4%Z)). zstep (ltac:(oF' 0x541f8%Z)) (ltac:(oD' 0x541f8%Z)).
zbft (ltac:(oF' 0x541fc%Z)) (ltac:(oD' 0x541fc%Z)).
zstep (ltac:(oF' 0x54200%Z)) (ltac:(oD' 0x54200%Z)).
zbft (ltac:(oF' 0x54204%Z)) (ltac:(oD' 0x54204%Z)).
zstep (ltac:(oF' 0x54208%Z)) (ltac:(oD' 0x54208%Z)).
stepn (ltac:(oF' 0x5420c%Z)) (ltac:(oD' 0x5420c%Z)). rwH. rewrite (art_zb_srli (m - spb) 32) by lia. rewrite Ediv.
stepn (ltac:(oF' 0x54210%Z)) (ltac:(oD' 0x54210%Z)). rwH. rewrite (art_zb_andi c 31) by lia. rewrite (art_land_31 c) by lia.
zstep (ltac:(oF' 0x54214%Z)) (ltac:(oD' 0x54214%Z)).
zbft (ltac:(oF' 0x54218%Z)) (ltac:(oD' 0x54218%Z)).
zstep (ltac:(oF' 0x5421c%Z)) (ltac:(oD' 0x5421c%Z)).
zbft (ltac:(oF' 0x54220%Z)) (ltac:(oD' 0x54220%Z)).
zbft (ltac:(oF' 0x54224%Z)) (ltac:(oD' 0x54224%Z)).
zstep (ltac:(oF' 0x54228%Z)) (ltac:(oD' 0x54228%Z)).
stepn (ltac:(oF' 0x5422c%Z)) (ltac:(oD' 0x5422c%Z)).
unfold art_f48. apply mst_refl. }
rewrite (art_class_size_small c ltac:(lia)).
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
- eexists. split.
{ zstep (ltac:(oF' 0x541c4%Z)) (ltac:(oD' 0x541c4%Z)).
zsd (ltac:(oF' 0x541c8%Z)) (ltac:(oD' 0x541c8%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x541cc%Z)) (ltac:(oD' 0x541cc%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x541d0%Z)) (ltac:(oD' 0x541d0%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x541d4%Z)) (ltac:(oD' 0x541d4%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x541d8%Z)) (ltac:(oD' 0x541d8%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x541dc%Z)) (ltac:(oD' 0x541dc%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zstep (ltac:(oF' 0x541e0%Z)) (ltac:(oD' 0x541e0%Z)). zstep (ltac:(oF' 0x541e4%Z)) (ltac:(oD' 0x541e4%Z)).
stepn (ltac:(oF' 0x541e8%Z)) (ltac:(oD' 0x541e8%Z)). stepn (ltac:(oF' 0x541ec%Z)) (ltac:(oD' 0x541ec%Z)). zcl4.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1283032 + 32) 8 spb) by zcell end.
zld (ltac:(oF' 0x541f0%Z)) (ltac:(oD' 0x541f0%Z)) (1283032 + 32) Cspb'.
zstep (ltac:(oF' 0x541f4%Z)) (ltac:(oD' 0x541f4%Z)). zstep (ltac:(oF' 0x541f8%Z)) (ltac:(oD' 0x541f8%Z)).
zbft (ltac:(oF' 0x541fc%Z)) (ltac:(oD' 0x541fc%Z)).
zstep (ltac:(oF' 0x54200%Z)) (ltac:(oD' 0x54200%Z)).
zbft (ltac:(oF' 0x54204%Z)) (ltac:(oD' 0x54204%Z)).
zstep (ltac:(oF' 0x54208%Z)) (ltac:(oD' 0x54208%Z)).
stepn (ltac:(oF' 0x5420c%Z)) (ltac:(oD' 0x5420c%Z)). rwH. rewrite (art_zb_srli (m - spb) 32) by lia. rewrite Ediv.
stepn (ltac:(oF' 0x54210%Z)) (ltac:(oD' 0x54210%Z)). rwH. rewrite (art_zb_andi c 31) by lia. rewrite (art_land_31 c) by lia.
zstep (ltac:(oF' 0x54214%Z)) (ltac:(oD' 0x54214%Z)).
zbft (ltac:(oF' 0x54218%Z)) (ltac:(oD' 0x54218%Z)).
zstep (ltac:(oF' 0x5421c%Z)) (ltac:(oD' 0x5421c%Z)).
zbtk (ltac:(oF' 0x54220%Z)) (ltac:(oD' 0x54220%Z)).
zstep (ltac:(oF' 0x54250%Z)) (ltac:(oD' 0x54250%Z)). zstep (ltac:(oF' 0x54254%Z)) (ltac:(oD' 0x54254%Z)). zstep (ltac:(oF' 0x54258%Z)) (ltac:(oD' 0x54258%Z)). zstep (ltac:(oF' 0x5425c%Z)) (ltac:(oD' 0x5425c%Z)). zstep (ltac:(oF' 0x54260%Z)) (ltac:(oD' 0x54260%Z)). zstep (ltac:(oF' 0x54264%Z)) (ltac:(oD' 0x54264%Z)).
zstep (ltac:(oF' 0x54268%Z)) (ltac:(oD' 0x54268%Z)). zstep (ltac:(oF' 0x5426c%Z)) (ltac:(oD' 0x5426c%Z)). zstep (ltac:(oF' 0x54270%Z)) (ltac:(oD' 0x54270%Z)).
fold (art_pop_szw c). rewrite (art_pop_szw_ok c ltac:(lia)).
unfold art_f48. apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_cbr_pa2 := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "WG&?y5'RNyR0%211%5241'4y8%611%311p061'=&Fr4%211':&Q0r;(RL+:(8%33D21%6251&RMr7%22F1%;3F41r<+;%;3L19%>231&Q:r8&QC+2+Q5%3221%6251%?2Q31%H3Q391r=+<%H3Q91F%K231%M3Q81Cr>+=%M3Q>1K%Q0231%J2Q>A%Q33Q>21r?+>%Q33QD1Q1%Q6231&QD%12MQ7%Q22QF1%Q;3QF41r@+?%Q;3QL1Q9%Q>231r6%Q92QM1%QB3QM31rA+C%QB3R31Q@%QE231+QWTnH%Q@2R41%QI3R431&Q=+Vb\P0%221N&Q?%Q>2JQ9+Q?%Q>2Q=1%4231%QB2FQ=%R33R7O1'9+1%<21Q2+N%>2Q41%5231z%A21Q7+Q0%QK2QJ1%A2Q:1%;241rDrC&QA%12Q06%R4231%R521Q9%RF3RJ61%M2=Q;%62QDQ5rB%Q0221%R;2Q8F%:2QH1%Q0241%J241%=2QC6%R@21QD%Q721Q>+S`PPPP0%Q92:1&D&Q7rK+Q@%RH2QA1u8rG%7565321rLrH+T0%M215%S0231%S121:%>5=619Q2';'H&Q1vQNrO+Z`cD%SF3T51SD/01T5rNrM%8576321r1+Z`eH%SM3T<1SK/01T<%=5<4176%?3N61+B%T23TC1T0%T5281rI%QF21QK%SI2Q31rE%QI21Q1%SL231%T52TI1%T>3TI81%TL1TM&Q8(1%T?3U0R=T=%T@3U1T0T>+3%TB3U31T@+4%TD3U51TB+8%TF3U71TD+9%TH3U91TF+D%TJ3U;1TH+E%TL3U=1TJ+F%TN3U?1TL+G%U03UA1TN+H%U23UC1U0+I%U43UE1U2+J%U63UG1U4+K%U83UI1U6(3%11N%M3O31%N3Q061%O3Q191%Q03Q2<1%Q13Q3?1%Q23Q4B1%Q33Q5E1%Q43Q6H1%Q53Q7T11%Q63Q8L1%Q73Q9O1%Q83Q:Q21%Q93Q;Q51%Q:3Q<Q81%Q;3Q=Q:1%Q=3Q>QO1r3r2%UO221rQ1%V1213%V33V>31p071pTJQF1%T22QH1%T32R41qU2VB1%RF2VC1p0RH1p0S01p0S91p0S<1p0S@1p0SH1p0SJ1p0T21p0T91p0T@1p0TC1p0TI1p0TM1p0U51p0U=1p0UF1p0UM1p0V31p0VA1tV2W1VN1pTDW21pT<W31pTHW41pSBW51pU4W61pUHW71pTBW81pU6W:1pQ2W;1pU0WA1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 3%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 4%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 6%nat 0%nat).
Variable off : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 7%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 8%nat 0%nat).
Variable mu : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pa2) 9%nat 0%nat).
Lemma art_cbr_pa2 : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_pa2) 10%nat 0%nat).
Proof using Type regs M rom m spb ris c off i mu.
intros sz H10 H11 H12 H13 H14 H15 H19 Hspb Hspb' Eris Hc Hoff Em Hi Hoi Hmu Hmu' Cris Cmu.
pose proof (art_class_size_facts c Hc) as (Hsz & _). fold sz in Hsz.
assert (Emod : (m - spb) mod 2 ^ 32 = off).
{ symmetry. apply (Z.mod_unique_pos (m - spb) (2 ^ 32) c off); lia. }
assert (Eq : off / sz = i).
{ symmetry. apply (Z.div_unique_pos off sz i (off - sz * i)); lia. }
assert (Hi' : i < 2 ^ 27). { assert (sz * i < 2 ^ 32) by lia. nia. }
eexists. split.
{ stepn (ltac:(oF' 0x54274%Z)) (ltac:(oD' 0x54274%Z)). rwH. rewrite (art_zb_divuw (m - spb) sz) by (rewrite ?Emod, ?Eq; lia). rewrite Emod, Eq.
zstep (ltac:(oF' 0x54278%Z)) (ltac:(oD' 0x54278%Z)).
zld (ltac:(oF' 0x5427c%Z)) (ltac:(oD' 0x5427c%Z)) (1283032 + 48) Cris.
zstep (ltac:(oF' 0x54280%Z)) (ltac:(oD' 0x54280%Z)). zstep (ltac:(oF' 0x54284%Z)) (ltac:(oD' 0x54284%Z)). zstep (ltac:(oF' 0x54288%Z)) (ltac:(oD' 0x54288%Z)). zstep (ltac:(oF' 0x5428c%Z)) (ltac:(oD' 0x5428c%Z)).
zld (ltac:(oF' 0x54290%Z)) (ltac:(oD' 0x54290%Z)) (ris + 128 * c + 48) Cmu.
stepn (ltac:(oF' 0x54294%Z)) (ltac:(oD' 0x54294%Z)). rwH. rewrite (art_zb_srli_exact _ 32 i) by lia.
zstep (ltac:(oF' 0x54298%Z)) (ltac:(oD' 0x54298%Z)). zstep (ltac:(oF' 0x5429c%Z)) (ltac:(oD' 0x5429c%Z)). zstep (ltac:(oF' 0x542a0%Z)) (ltac:(oD' 0x542a0%Z)). zstep (ltac:(oF' 0x542a4%Z)) (ltac:(oD' 0x542a4%Z)). zstep (ltac:(oF' 0x542a8%Z)) (ltac:(oD' 0x542a8%Z)).
stepn (ltac:(oF' 0x542ac%Z)) (ltac:(oD' 0x542ac%Z)). rwH. rewrite (art_zb_and 18446744073709551615 (c * 2 ^ 32 + spb + sz * i)) by lia. rewrite art_land_full_l by lia.
zbft (ltac:(oF' 0x542b0%Z)) (ltac:(oD' 0x542b0%Z)).
zbft (ltac:(oF' 0x542b4%Z)) (ltac:(oD' 0x542b4%Z)).
apply mst_refl. }
split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_cbr_magic := (forall regs (M rom : word -> option byte) (m ab : Z), getr regs 9 = Z_to_bv 64 m -> getr regs 18 = Z_to_bv 64 ab ->
0x693000 <= ab -> ab + 8 < 2 ^ 47 -> 0 <= m < 2 ^ 64 -> ab mod 8 = 0 ->
cellA M 0x10358 8 0xcc6e96b9cc6e96b9 ->
(ab <> m -> cellA M ab 8 0xcc6e96b9cc6e96b9 /\ wrA M ab 8) ->
exists regs', msteps ASEGS (mkst regs (0x542b8 : word) M rom) (mkst regs' (0x542d4 : word) (if ab =? m then M else Wn 8 M ab 0) rom)
/\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_magic) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_magic) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_magic) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cbr_magic) 3%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_cbr_magic) 4%nat 0%nat).
Lemma art_cbr_magic : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_magic) 5%nat 0%nat).
Proof using Type regs M rom m ab.
intros H9 H18 Hab Hab' Hm Hab8 Cmag Hne.
destruct (Z.eqb_spec ab m) as [E|NE].
- eexists. split.
{ zbtk (ltac:(oF' 0x542b8%Z)) (ltac:(oD' 0x542b8%Z)). apply mst_refl. }
intros r Hr. reflexivity.
- destruct (Hne NE) as [Cab Wab].
eexists. split.
{ zbft (ltac:(oF' 0x542b8%Z)) (ltac:(oD' 0x542b8%Z)).
stepn (ltac:(oF' 0x542bc%Z)) (ltac:(oD' 0x542bc%Z)). zcl4.
zld (ltac:(oF' 0x542c0%Z)) (ltac:(oD' 0x542c0%Z)) 0x10358 Cmag.
chain_step; [reflexivity
| eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ab) _ (Z_to_bv 64 0xcc6e96b9cc6e96b9));
[exact (ltac:(oF' 0x542c4%Z)) | reflexivity | exact (ltac:(oD' 0x542c4%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hab8
| exact Cab | apply bytes_le_to_Z_8 ]
| ]. wpc.
chain_step; [reflexivity
| eapply art_step_branch_ft_r; [exact (ltac:(oF' 0x542c8%Z)) | reflexivity | exact (ltac:(oD' 0x542c8%Z)) | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
| ]. wpc.
chain_step; [reflexivity
| eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ab));
[exact (ltac:(oF' 0x542cc%Z)) | reflexivity | exact (ltac:(oD' 0x542cc%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hab8 | gres; rwH; reflexivity
| eapply (wr_wok _ _ _ _ Wab); lia ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 ab) (word_to_le_bytes 8 (Z_to_bv 64 0))) with (Wn 8 M0 ab 0).
zbft (ltac:(oF' 0x542d0%Z)) (ltac:(oD' 0x542d0%Z)).
apply mst_refl. }
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_cbr_cas30 := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "TH&?y5'RNyR0%211%5241'4y8%611%311p061'=':&Q0r5(RL+9(8%33A21%6251&RMr2%22C1%;3C41&Q=+@r3%3221&Q?&Q:r4%2216&QC+2+Q?%3221%8251&Q@%12H=z%L3M21'9%B23L+X0%@2N1%4231&D&Q7r9r7u4+3&QAr6%22;1%J241%:598761&Er:r8+4%44>321';'H&Q1vQNr=+Z`fD%QE3R11QC/01R1r<r;%8576321r1+Z`h<%QL3R81QJ/01R8&C%J2Q3N%24M9E1%@5?7419%B3Q291%R@1RA&Q8(1+1%R73RE1R5%R83RFQFR6%R93RGQ5R7%R:3RHMR8+8%R<3RJ1R:+B%R>3RL1R<+C%R@3RN1R>+D%RB3S01R@+E%RD3S21RB+F%RF3S41RD+G%RH3S61RF+H%RJ3S81RH+I%RL3S:1RJ+J%RN3S<1RL+K%S03S>1RN(3%11O%N3Q031%O3Q161%Q03Q291%Q13Q3<1%Q23Q4?1%Q33Q5B1%Q43Q6E1%Q53Q7H1%Q63Q8K1%Q73Q9N1%Q83Q:S:1%Q93Q;Q21%Q:3Q<Q51%Q;3Q=Q71%Q<3Q>Q91%Q=3Q?Q;1%Q?3Q@QI1%SF2S9S>r?%SH21S@%SJ3T231p051pTJQF1%S02QH1qU2T51%R=2T61p0R?1p0RE1p0S11p0S71p0S<1p0SF1p0SK1pS@T81pTBT91pU6T;1pQ2T<1pU0TB1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_cas30) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_cas30) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_cas30) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cbr_cas30) 3%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_cas30) 4%nat 0%nat).
Lemma art_cbr_cas30 : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_cas30) 5%nat 0%nat).
Proof using Type regs M rom m b1.
intros H9 Hm Hm' Hm16 Hb1 Chw Whw.
assert (Hm4 : m mod 4 = 0). { pose proof (Z.div_mod m 16 ltac:(lia)) as E. rewrite Hm16 in E. rewrite E. replace (16 * (m / 16) + 0) with ((4 * (m / 16)) * 4) by lia. apply Z_mod_mult. }
eexists. split.
{ stepn (ltac:(oF' 0x542d4%Z)) (ltac:(oD' 0x542d4%Z)). rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612. rewrite art_land_m4 by lia.
replace (m / 4 * 4) with m by (pose proof (Z.div_mod m 4 ltac:(lia)); lia).
stepn (ltac:(oF' 0x542d8%Z)) (ltac:(oD' 0x542d8%Z)). rwH. rewrite art_zb_slli by lia.
zstep (ltac:(oF' 0x542dc%Z)) (ltac:(oD' 0x542dc%Z)). zstep (ltac:(oF' 0x542e0%Z)) (ltac:(oD' 0x542e0%Z)).
stepn (ltac:(oF' 0x542e4%Z)) (ltac:(oD' 0x542e4%Z)). rwH. rewrite art_sllw_0 by lia.
stepn (ltac:(oF' 0x542e8%Z)) (ltac:(oD' 0x542e8%Z)). rwH. rewrite art_sllw_0 by lia.
chain_step; [reflexivity
| eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m) _ (Z_to_bv 64 (3 + 256 * b1)));
[exact (ltac:(oF' 0x542ec%Z)) | reflexivity | exact (ltac:(oD' 0x542ec%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4
| exact Chw | apply art_bytes4; lia ]
| ]. wpc. rewrite art_v_lw_small by lia.
chain_step; [reflexivity | eapply art_step_and_r; [exact (ltac:(oF' 0x542f0%Z)) | reflexivity | exact (ltac:(oD' 0x542f0%Z)) | reflexivity] | ]. wpc.
gres. rewrite (art_zb_and (3 + 256 * b1) 255) by lia.
replace (Z.land (3 + 256 * b1) 255) with 3.
2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. replace (3 + 256 * b1) with (3 + b1 * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
chain_step; [reflexivity
| eapply art_step_branch_ft_r; [exact (ltac:(oF' 0x542f4%Z)) | reflexivity | exact (ltac:(oD' 0x542f4%Z)) | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
| ]. wpc.
chain_step; [reflexivity | eapply art_step_xor_r; [exact (ltac:(oF' 0x542f8%Z)) | reflexivity | exact (ltac:(oD' 0x542f8%Z)) | reflexivity] | ]. wpc.
chain_step; [reflexivity | eapply art_step_and_r; [exact (ltac:(oF' 0x542fc%Z)) | reflexivity | exact (ltac:(oD' 0x542fc%Z)) | reflexivity] | ]. wpc.
chain_step; [reflexivity | eapply art_step_xor_r; [exact (ltac:(oF' 0x54300%Z)) | reflexivity | exact (ltac:(oD' 0x54300%Z)) | reflexivity] | ]. wpc.
gres.
rewrite art_cas30w by lia.
match goal with |- msteps _ (mkstr _ _ ?X _ _) _ => assert (Whw' : wokA X m 4) by (eapply (wr_wok _ _ _ _ Whw); lia) end.
chain_step; [reflexivity
| eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m));
[exact (ltac:(oF' 0x54304%Z)) | reflexivity | exact (ltac:(oD' 0x54304%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4 | gres; rwH; reflexivity
| exact Whw' ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 m) (word_to_le_bytes 4 (Z_to_bv 64 (256 * b1)))) with (Wn 4 M0 m (256 * b1)).
zbft (ltac:(oF' 0x54308%Z)) (ltac:(oD' 0x54308%Z)).
apply mst_refl. }
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_cbr_pd := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "U?&?y5'RNyR0%211%5241'4y8%611%311p061'=':&Q0r5(RL+9(8%33A21%6251&RMr2%22C1%;3C41&Q=+@r3%3221&Q?&Q:r4%2216&QC+2+Q?%3221%8251'9z%?219+Q0%9281%>2<1%6241&D&Q7r8r6%C21?u2%655421<r9r7+4%I221u4%<5;5219';'H&Q1vQNr<+Z`h<%Q@3QL1Q>/01QLr;r:%8576321r1+_YU@%QG3R31QE/01R3%=5<4176%?3L61+1%QL3R:1QJ%QO281+Z`i@%QO3R;1QM/01R;%R43R<41+:%R33RA1R1%R62?1%QG2Q1QK%R12RB1%R:3RB31+;%R93RG1R7%R<2E1&QA&Q;+7%R02Q?1+8%4221%6212%R=2RN1%RF3RN91+<%RE3S31RC%RH2Q11+WJ%RC2S41%RL3S431%S71S8&Q8(1%RM3S;R;RK+3%RO3S=1RM%S03S>QJRN%S13S?BRO+B%S33SA1S1+C%S53SC1S3+D%S73SE1S5+E%S93SG1S7+F%S;3SI1S9+G%S=3SK1S;+H%S?3SM1S=+I%SA3SO1S?+J%SC3T11SA+K%SE3T31SC(3%11M%L3N31%M3O61%N3Q091%O3Q1<1%Q03Q2?1%Q13Q3B1%Q23Q4E1%Q33Q5H1%Q43Q6K1%Q53Q7N1%Q63Q8SO1%Q73Q9Q21%Q83Q:Q41%Q93Q;Q61%Q:3Q<Q91%Q<3Q=RB1%T:2SMT2r>%T<21T4%T>3TF31p051pTJQC1%SH2QE1%SI2QL1%SJ2R91%SK2R@1%SL2RH1qU2TM1%S:2TN1p0S<1p0SC1p0SK1p0T31p0T=1p0TB1pTFTO1pTBU01pU6U21pQ2U31pU0U91")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pd) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pd) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pd) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pd) 3%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_cbr_pd) 4%nat 0%nat).
Lemma art_cbr_pd : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_pd) 5%nat 0%nat).
Proof using Type regs M rom m n.
intros H9 Hm Hm' Hn Chi Cn.
eexists. split.
{ zlhu4 (ltac:(oF' 0x5430c%Z)) (ltac:(oD' 0x5430c%Z)) (m + 2) Chi.
zlwu (ltac:(oF' 0x54310%Z)) (ltac:(oD' 0x54310%Z)) (m + 4) Cn.
zstep (ltac:(oF' 0x54314%Z)) (ltac:(oD' 0x54314%Z)). zstep (ltac:(oF' 0x54318%Z)) (ltac:(oD' 0x54318%Z)).
stepn (ltac:(oF' 0x5431c%Z)) (ltac:(oD' 0x5431c%Z)). rwH. rewrite (art_zb_or4 0 n) by lia. rewrite Z.lor_0_l.
zstep (ltac:(oF' 0x54320%Z)) (ltac:(oD' 0x54320%Z)).
stepn (ltac:(oF' 0x54324%Z)) (ltac:(oD' 0x54324%Z)). rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
zstep (ltac:(oF' 0x54328%Z)) (ltac:(oD' 0x54328%Z)).
stepn (ltac:(oF' 0x5432c%Z)) (ltac:(oD' 0x5432c%Z)).
apply mst_refl. }
split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Definition art_cbr_stats_mem (M : word -> option byte) (sp1 t n f1 f2 : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp1 - 8) 0x54334) (sp1 - 24) 0x82434) (t + 2800 + 40) (f1 + 1)) (t + 2800 + 48) (n + f2).
Section SE.
Local Abbreviation SEC_T_art_cbr_stats := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "W7&?y5'RNyR0%211%5241'4y8%611%311p061'=':&Q0r>(RL+2(8%33A21%6251&RMr;%22C1%;3C41r?+4%;3I19%>231r:%92J1%B3J31r@+9%B3Q01@%E231r6%@2Q11%I3Q131&Q=+Vb\P0r=%3221&QD+Q0%22D1%72O1&Q?&QC+R0%22Q11%42C1&E&Q7rCrA%=21<%54431=&JrDr<%362MQ4Q>D1+TP0%H21F&Q:%12QB3%K21<+8%42>1%N21:rB&QA%125B%9231%:217rE%Q5221+U0%>281rF%Q9221rJ%N4M1<D+@%Q=21>%E2O2rI%Q@221'9z%QC21Q4%Q;2R:Q?%Q=2Q61%5231%Q?2Q8Q<%7251&DrQ0rG%Q321RBu2%55Q@421<rQ1rH%Q821R>u4%:5QE4218rQ2+Rg@%Q=2L1+Q8%Q?221u8%A5QL621?rQ3rK%QD218+Q@%QF221%G5R2517E';'H&Q1vQNrQ6+Z`i@%S>3SJ1S</01SJrQ5rQ4%8576321r1+Z`jL%SE3T11SC/01T1&MrM%269G1FQHQC%@5?7419%B3RF91%T91T:&Q8(1+3%T03T>1SN%T13T?R>SO+B%T33TA1T1+C%T53TC1T3+D%T73TE1T5+E%T93TG1T7+F%T;3TI1T9+G%T=3TK1T;+H%T?3TM1T=+I%TA3TO1T?+J%TC3U11TA+K%TE3U31TC(3%11K%J3L31%K3M61%L3N91%M3O<1%N3Q0?1%O3Q1B1%Q03Q2E1%Q13Q3H1%Q23Q4K1%Q33Q5N1%Q43Q6T@1%Q53Q7Q21%Q63Q8TI1%Q73Q9Q51%Q83Q:U31%Q:3Q;QD1r3r2%U<221rQ8%U>213%U@3UH31p071pTJQC1%S82QE1qU2UK1%R:2UL1p0R<1p0RC1p0RK1p0S11p0S81p0S91p0S<1p0SC1p0SG1p0SJ1p0SM1p0T21p0T:1p0T>1p0TB1p0TE1p0TJ1p0U11p0U71p0U<1p0UA1p0UI1p0V11pSLV>1pSJV?1pTFV@1pTBVA1pV6VB1pSHVC1pV:VD1pT@VE1pV8VF1pNVG1pUFVH1pU6VJ1pQ2VK1pU0W11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 2%nat 0%nat).
Variable sp1 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 3%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 4%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 5%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 6%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 7%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 8%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 9%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 10%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 11%nat 0%nat).
Variable f1 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 12%nat 0%nat).
Variable f2 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_stats) 13%nat 0%nat).
Lemma art_cbr_stats : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_stats) 14%nat 0%nat).
Proof using Type regs M rom sp1 HI tp key tsd ctx t m n f1 f2.
intros H2 H4 H9 HHI Hsp Hsp' W TSD Ht Ht' Htp Htsd Hctx Wt Hm Hm' Hn Hf1 Hf2 Chi Cn C40 C48.
pose proof TSD as (_ & _ & _ & _ & _ & R).
eexists. split.
{ stepn (ltac:(oF' 0x54330%Z)) (ltac:(oD' 0x54330%Z)).
zcall (art_thread_stats_fn _ _ _ (0x54334 : word) sp1 tp key tsd ctx t).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chi' : cellA X (m + 2) 2 0) by zcell; assert (Cn' : cellA X (m + 4) 4 n) by zcell;
assert (C40' : cellA X (t + 2800 + 40) 8 f1) by zcell; assert (C48' : cellA X (t + 2800 + 48) 8 f2) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
zlhu4 (ltac:(oF' 0x54334%Z)) (ltac:(oD' 0x54334%Z)) (m + 2) Chi'.
zlwu (ltac:(oF' 0x54338%Z)) (ltac:(oD' 0x54338%Z)) (m + 4) Cn'.
zld (ltac:(oF' 0x5433c%Z)) (ltac:(oD' 0x5433c%Z)) (t + 2800 + 48) C48'.
zld (ltac:(oF' 0x54340%Z)) (ltac:(oD' 0x54340%Z)) (t + 2800 + 40) C40'.
zstep (ltac:(oF' 0x54344%Z)) (ltac:(oD' 0x54344%Z)).
stepn (ltac:(oF' 0x54348%Z)) (ltac:(oD' 0x54348%Z)). rwH. rewrite (art_zb_or4 0 n) by lia. rewrite Z.lor_0_l.
zstep (ltac:(oF' 0x5434c%Z)) (ltac:(oD' 0x5434c%Z)). zstep (ltac:(oF' 0x54350%Z)) (ltac:(oD' 0x54350%Z)).
zsd (ltac:(oF' 0x54354%Z)) (ltac:(oD' 0x54354%Z)) (t + 2800 + 40) (f1 + 1) ltac:(zwok').
zsd (ltac:(oF' 0x54358%Z)) (ltac:(oD' 0x54358%Z)) (t + 2800 + 48) (n + f2) ltac:(zwok').
unfold art_cbr_stats_mem. apply mst_refl. }
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; exact H2]|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_cbr_tailp := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "XE&?y5'RNyR0%211%5241'4y8%611%311p061'=&Q:r8&QAr7&QC+2+Q0%3221%6251%9281r6%;221':&Q0r@(RL(8%23L<1%5241&RM&QDr<+Q@%3221%52Q11%=3Q171rA+8%=3Q71<%@231%;2Q79%C3Q721rB+B%C3Q=1B%F231r3%B2Q>1%J3Q>31rC+C%J3QD1I%M231+QWTnH%I2QE1%Q13QE31rD+D%Q13QK1Q0%Q4231+Q5%Q?2Q>1%Q12QM1%Q93QM41&Q=%12Q1M&Q?+R0%QF2QE1%32K1+Vb\P0%721Q?%QN2Q4;+Q?%QL2QK1%9231'9+1%>21Q:+N%@2Q<1%5231z%C21Q?%B2Q@R3%9221rF%G251rG%R?21QD%H21F&D&Q7rL%RD2Q9R>u8%554321:rMrIrH%9583251rNrK%R921R2&RO%12S8<%?5>53;1rO+@%R?2@1%C5B31?HrQ0+H%RC2@1%G5F31CLrQ1%RF2?S4%J5I21FOrQ2+Q8%RJ2=1%N5M31JQ3rQ3%RM2<RK%Q15Q021MQ6';'H&Q1vQNrQ6+Z`jL%S:3T21S9/01T2rQ5rQ4%8576321r1+Za^8%SA3T91S@/01T9%=5<4176%?3QA61%SE3T?R1SD%SH271%SJ3T>1F%SJ29SF%SE2TAL%SM3TA21+:%SL3TF1SK%SO2>1%SJ2TFQ8%T23TF21+;%T13TK1T0%T42C1%T63TJ1S6+<%T53TO1T4%T82G1%T32TOQK%T;3TO21+=%T:3U41T9%T=2L1%T82U4R=%T@3U421%T@2OT1%T;2U7R;%TC3U721+9%TB3U<1TA%TE2Q41%T@2U<R7%TH3U<21%TH2Q7T3rJ%TD2U@1%TL3U@31%TL2Q;T0%TG2UCRB%TO3UC21%TO2Q>SL%TJ2UFRD%U23UF21%UI1UJ&Q8(1+3%U43UN1U3+4%U63V01U5+E%U83V21U7+F%U:3V41U9+G%U<3V61U;%U=3V7RFU<+I%U?3V91U>+J%UA3V;1U@+K%UC3V=1UB(3%11E%D3F31%E3G61%F3H91%G3I<1%H3J>1%I3KA1%J3LD1%K3MG1%L3NJ1%N3OR@1r2%V32U<1rQ8%V5213%V73VK31p061pTJQ61%TD2Q81%TE2Q<1%TF2Q@1%TG2QE1%TH2QK1%TI2QO1%TJ2R51%TK2R;1%TL2R@1%TM2RF1%TN2RJ1%TO2RN1qU2W91%S@2W:1p0SB1p0SF1p0SK1p0SO1p0T41p0T91p0T@1p0TE1p0TL1p0U01p0U31p0U81p0U?1p0UD1p0UG1p0UL1p0UO1p0V81p0V@1p0VH1p0VO1tS>WJW>1pT4WK1pT2WL1pT0WM1pT8WN1pT6WO1pV4X01pSBX11pUHX21pSDX31pSFX41pUDX51pTNX=1pU6X81pQ2X91pU0X?1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 4%nat 0%nat).
Variable cb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 5%nat 0%nat).
Variable cache : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 6%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 7%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 8%nat 0%nat).
Variable szi : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 9%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 10%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 11%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 12%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 13%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tailp) 14%nat 0%nat).
Lemma art_cbr_tailp : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_tailp) 15%nat 0%nat).
Proof using Type regs M rom raw sp cb cache spb c szi g8 g9 g18 g19 g20.
intros ab H2 H8 H18 H19 H20 Hsp Hsp' Hspb Hspb' Hc Hszi Hcb Hcb' Cspb Ccb F1 F8 F9 F18 F19 F20.
assert (Hab : ab = spb + c * 2 ^ 32 + szi) by reflexivity. clearbody ab.
assert (Ec : (ab - spb) * 2 ^ 27 / 2 ^ 59 = c).
{ symmetry. apply (Z.div_unique_pos ((ab - spb) * 2 ^ 27) (2 ^ 59) c (szi * 2 ^ 27)); lia. }
eexists. split.
{ zbft (ltac:(oF' 0x5435c%Z)) (ltac:(oD' 0x5435c%Z)).
zld (ltac:(oF' 0x54360%Z)) (ltac:(oD' 0x54360%Z)) (1283032 + 32) Cspb.
zbft (ltac:(oF' 0x54364%Z)) (ltac:(oD' 0x54364%Z)).
zstep (ltac:(oF' 0x54368%Z)) (ltac:(oD' 0x54368%Z)).
zbft (ltac:(oF' 0x5436c%Z)) (ltac:(oD' 0x5436c%Z)).
zld (ltac:(oF' 0x54370%Z)) (ltac:(oD' 0x54370%Z)) cb Ccb.
zstep (ltac:(oF' 0x54374%Z)) (ltac:(oD' 0x54374%Z)).
zstep (ltac:(oF' 0x54378%Z)) (ltac:(oD' 0x54378%Z)).
stepn (ltac:(oF' 0x5437c%Z)) (ltac:(oD' 0x5437c%Z)). rwH. rewrite (art_zb_srli ((ab - spb) * 2 ^ 27) 59) by lia. rewrite Ec.
stepn (ltac:(oF' 0x54380%Z)) (ltac:(oD' 0x54380%Z)). stepn (ltac:(oF' 0x54384%Z)) (ltac:(oD' 0x54384%Z)). zcl4.
zstep (ltac:(oF' 0x54388%Z)) (ltac:(oD' 0x54388%Z)).
zld (ltac:(oF' 0x5438c%Z)) (ltac:(oD' 0x5438c%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54390%Z)) (ltac:(oD' 0x54390%Z)) (sp - 16) F8. zld (ltac:(oF' 0x54394%Z)) (ltac:(oD' 0x54394%Z)) (sp - 24) F9. zld (ltac:(oF' 0x54398%Z)) (ltac:(oD' 0x54398%Z)) (sp - 32) F18. zld (ltac:(oF' 0x5439c%Z)) (ltac:(oD' 0x5439c%Z)) (sp - 40) F19. zld (ltac:(oF' 0x543a0%Z)) (ltac:(oD' 0x543a0%Z)) (sp - 48) F20.
zstep (ltac:(oF' 0x543a4%Z)) (ltac:(oD' 0x543a4%Z)).
stepn (ltac:(oF' 0x543a8%Z)) (ltac:(oD' 0x543a8%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_cbr_tails := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "WI&?y5'RNyR0%211%5241'4y8%611%311p061'=':&Q0r<(RL+2(8%33A21%6251&RM&QDr8+Q@%3221%52F1%>3F71r=+B%>3L1<%A231r7%<2M1%E3M31r>+C%E3Q31C%H231+QWTnH%C2Q41%L3Q431r?+D%L3Q:1J%O231&QC+Q5%22O1%L2Q=1%Q53Q=51&Q=%12LQ5&Q?+R0%92Q61%32L1+Vb\P0%721N&Q:%12I<+Q?%@2Q=1%:231'9z%=21O%>2Q0<%4221'<r@%B2M1%=22H%F21O%5231&D&Q7rE+Q0%D2Q81u8rA%7565321rFrC+8%R0221&ROrD%22RE1%?5>74:1rG+@%R7251%C5B31>=rH+H%R;2D1%G5F31BArI%R>2AF%J5I21EDrJ+Q8%RB2=1%N5M31IHrK%RE2<RC%Q15Q021LK';'H&Q1vQNrN+Z`jL%S33S?1S1/01S?rMrL%8576321r1+Zal@%S:3SF1S8/01SF%=5<4176%?3QA61+1%S?3SM1S=%SB281%SD3SL1G%SD2:S?%S>2SOM%SG3SO21+:%SF3T41SD%SI2?1+QWUPH%SD2T51%SM3T531+;%SL3T:1SJ%SO2E1+QWUd8%SJ2T;1%T33T;31+<%T23T@1T0%T52K1%SO2T@QE%T83T@21%T63TDR1T4%T92O1%T32TDQM%T<3TD21+9%T;3TI1T9%T>2Q41%T82TIR:%TA3TI21%TA2Q7T1%T;2TLRC%TD3TL21%TD2Q:SM%T>2TOR;%TG3TO21%TG2Q=SI%TA2U2RB%TJ3U221%U51U6&Q8(1+3%TL3U:1TJ+4%TN3U<1TL+E%U03U>1TN+F%U23U@1U0+G%U43UB1U2%U53UCREU3+I%U73UE1U5+J%U93UG1U7+K%U;3UI1U9(3%11E%D3F31%E3G61%F3H91%G3I<1%H3J>1%I3KA1%J3LD1%K3MG1%L3NJ1%N3OR?1r3r2%UL221rQ0%UN213%V03V831p071pTJQ71%T@2Q91%TA2Q=1%TB2QA1%TC2QE1%TD2QK1%TE2R01%TF2R61%TG2R=1%TH2RD1%TI2RH1%TJ2RM1qU2VE1%S?2VF1p0SA1p0SE1p0SJ1p0SN1p0T31p0T81p0TA1p0TJ1p0U11p0U71p0U=1p0U@1p0UE1p0UH1p0V21p0V:1p0VB1pT4W21pT2W31pT0W41pT8W51pT6W61pT:W71pUHW81pUDW91pTNWA1pU6W<1pQ2W=1pU0WC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 4%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 5%nat 0%nat).
Variable hb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 6%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 7%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 8%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 9%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 10%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_cbr_tails) 11%nat 0%nat).
Lemma art_cbr_tails : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_tails) 12%nat 0%nat).
Proof using Type regs M rom raw sp spb hb g8 g9 g18 g19 g20.
intros H2 H18 H19 H20 Hsp Hsp' Hspb Hspb' Hhb Hsec Cspb F1 F8 F9 F18 F19 F20.
destruct (Z_lt_le_dec hb spb) as [Lo|Hi].
- eexists. split.
{ zbft (ltac:(oF' 0x5435c%Z)) (ltac:(oD' 0x5435c%Z)).
zld (ltac:(oF' 0x54360%Z)) (ltac:(oD' 0x54360%Z)) (1283032 + 32) Cspb.
zbtk (ltac:(oF' 0x54364%Z)) (ltac:(oD' 0x54364%Z)).
zstep (ltac:(oF' 0x543cc%Z)) (ltac:(oD' 0x543cc%Z)). zstep (ltac:(oF' 0x543d0%Z)) (ltac:(oD' 0x543d0%Z)). zstep (ltac:(oF' 0x543d4%Z)) (ltac:(oD' 0x543d4%Z)).
zld (ltac:(oF' 0x543d8%Z)) (ltac:(oD' 0x543d8%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x543dc%Z)) (ltac:(oD' 0x543dc%Z)) (sp - 16) F8. zld (ltac:(oF' 0x543e0%Z)) (ltac:(oD' 0x543e0%Z)) (sp - 24) F9. zld (ltac:(oF' 0x543e4%Z)) (ltac:(oD' 0x543e4%Z)) (sp - 32) F18. zld (ltac:(oF' 0x543e8%Z)) (ltac:(oD' 0x543e8%Z)) (sp - 40) F19. zld (ltac:(oF' 0x543ec%Z)) (ltac:(oD' 0x543ec%Z)) (sp - 48) F20.
zstep (ltac:(oF' 0x543f0%Z)) (ltac:(oD' 0x543f0%Z)).
stepn (ltac:(oF' 0x543f4%Z)) (ltac:(oD' 0x543f4%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
- eexists. split.
{ zbft (ltac:(oF' 0x5435c%Z)) (ltac:(oD' 0x5435c%Z)).
zld (ltac:(oF' 0x54360%Z)) (ltac:(oD' 0x54360%Z)) (1283032 + 32) Cspb.
zbft (ltac:(oF' 0x54364%Z)) (ltac:(oD' 0x54364%Z)).
zstep (ltac:(oF' 0x54368%Z)) (ltac:(oD' 0x54368%Z)).
zbtk (ltac:(oF' 0x5436c%Z)) (ltac:(oD' 0x5436c%Z)).
zstep (ltac:(oF' 0x543cc%Z)) (ltac:(oD' 0x543cc%Z)). zstep (ltac:(oF' 0x543d0%Z)) (ltac:(oD' 0x543d0%Z)). zstep (ltac:(oF' 0x543d4%Z)) (ltac:(oD' 0x543d4%Z)).
zld (ltac:(oF' 0x543d8%Z)) (ltac:(oD' 0x543d8%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x543dc%Z)) (ltac:(oD' 0x543dc%Z)) (sp - 16) F8. zld (ltac:(oF' 0x543e0%Z)) (ltac:(oD' 0x543e0%Z)) (sp - 24) F9. zld (ltac:(oF' 0x543e4%Z)) (ltac:(oD' 0x543e4%Z)) (sp - 32) F18. zld (ltac:(oF' 0x543e8%Z)) (ltac:(oD' 0x543e8%Z)) (sp - 40) F19. zld (ltac:(oF' 0x543ec%Z)) (ltac:(oD' 0x543ec%Z)) (sp - 48) F20.
zstep (ltac:(oF' 0x543f0%Z)) (ltac:(oD' 0x543f0%Z)).
stepn (ltac:(oF' 0x543f4%Z)) (ltac:(oD' 0x543f4%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_cbr_sa := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "VC&?y5'RNyR0%211%5241'4y8%611%311p061'=':&Q0r8(RL+1(8%33A21%6251r5%93A21r9+2%93G17%<231&RM%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;&Q=&Q:+Vb\P0+Q@%3221%521N&Q?&QC+R0%22I1%42K1&E&Q7r=&QD%12I<%54431='9z%C21M%>2N;%4221%F2DQ0+Q5%A2Q81%H2N1+Q?%D2Q;1%F231'<r<%I2B1%O228%Q121D%5231&DrC+QWTnH+Q0%Q6221u8%65M521L';'H&Q1vQNrF+Z`^4%R83RD1R6/01RDrErD%8576321r1+ZaR8%R?3RK1R=/01RK&LrB%2491G=%@5?7419%B3QA91%RH29RC+Z`aL%RH3S41RF/01S4%RM3S541%RM2>RB%QF2:R1%RB2S91%S13S931+8%S03S>1RN%S32D1rA%RH2S?1%S73S?31+9%S63SD1S4%S92J1r@%RN2SE1%S=3SE31+C%S<3SJ1S:%S?2Q01%S32SJQA%SB3SJ21+D%SA3SO1S?%SD2Q51%S82SOR3%SG3SO21%SG2Q8S5+QWUPH%S<2T31%SK3T331%SK2Q<S4%SM3T51A%T81T9&Q8(1+3%SO3T=1SM+4%T13T?1SO+E%T33TA1T1+F%T53TC1T3+G%T73TE1T5+H%T93TG1T7+I%T;3TI1T9+J%T=3TK1T;+K%T?3TM1T=(3%11F%E3G31%F3H61%G3I91%H3J<1%I3K?1%J3LB1%K3ME1%L3NH1%M3OK1%O3Q0R>1r3r2%U0221rH%U2213%U43U<31p071pTJQ81%SK2Q:1%SL2Q=1%SM2QB1%SN2QH1%SO2QN1%T02R51%T12R<1%T22RA1%T32RG1qU2UG1%S<2UH1p0S>1p0SF1p0SM1p0T41p0T61p0T71p0T=1p0TD1p0TJ1p0U11p0U71p0U=1p0UE1pUHV01pTBV11pSFV21pUDV31pTNV;1pU6V61pQ2V71pU0V=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sa) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sa) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sa) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sa) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sa) 4%nat 0%nat).
Variable cb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sa) 5%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sa) 6%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sa) 7%nat 0%nat).
Lemma art_cbr_sa : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_sa) 8%nat 0%nat).
Proof using Type regs M rom raw sp cb m spb.
intros H1 H2 H10 H11 Hsp Hsp' W Hcb Hm Hspb Hspb' Hsec Cspb.
destruct (Z_lt_le_dec m spb) as [Lo|Hi].
- eexists. split.
{ zstep (ltac:(oF' 0x541c4%Z)) (ltac:(oD' 0x541c4%Z)).
zsd (ltac:(oF' 0x541c8%Z)) (ltac:(oD' 0x541c8%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x541cc%Z)) (ltac:(oD' 0x541cc%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x541d0%Z)) (ltac:(oD' 0x541d0%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x541d4%Z)) (ltac:(oD' 0x541d4%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x541d8%Z)) (ltac:(oD' 0x541d8%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x541dc%Z)) (ltac:(oD' 0x541dc%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zstep (ltac:(oF' 0x541e0%Z)) (ltac:(oD' 0x541e0%Z)). zstep (ltac:(oF' 0x541e4%Z)) (ltac:(oD' 0x541e4%Z)).
stepn (ltac:(oF' 0x541e8%Z)) (ltac:(oD' 0x541e8%Z)). stepn (ltac:(oF' 0x541ec%Z)) (ltac:(oD' 0x541ec%Z)). zcl4.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1283032 + 32) 8 spb) by zcell end.
zld (ltac:(oF' 0x541f0%Z)) (ltac:(oD' 0x541f0%Z)) (1283032 + 32) Cspb'.
zstep (ltac:(oF' 0x541f4%Z)) (ltac:(oD' 0x541f4%Z)). zstep (ltac:(oF' 0x541f8%Z)) (ltac:(oD' 0x541f8%Z)).
zbtk (ltac:(oF' 0x541fc%Z)) (ltac:(oD' 0x541fc%Z)).
zstep (ltac:(oF' 0x54230%Z)) (ltac:(oD' 0x54230%Z)). zstep (ltac:(oF' 0x54234%Z)) (ltac:(oD' 0x54234%Z)).
stepn (ltac:(oF' 0x54238%Z)) (ltac:(oD' 0x54238%Z)).
unfold art_f48. apply mst_refl. }
split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
- eexists. split.
{ zstep (ltac:(oF' 0x541c4%Z)) (ltac:(oD' 0x541c4%Z)).
zsd (ltac:(oF' 0x541c8%Z)) (ltac:(oD' 0x541c8%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x541cc%Z)) (ltac:(oD' 0x541cc%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x541d0%Z)) (ltac:(oD' 0x541d0%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x541d4%Z)) (ltac:(oD' 0x541d4%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x541d8%Z)) (ltac:(oD' 0x541d8%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x541dc%Z)) (ltac:(oD' 0x541dc%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zstep (ltac:(oF' 0x541e0%Z)) (ltac:(oD' 0x541e0%Z)). zstep (ltac:(oF' 0x541e4%Z)) (ltac:(oD' 0x541e4%Z)).
stepn (ltac:(oF' 0x541e8%Z)) (ltac:(oD' 0x541e8%Z)). stepn (ltac:(oF' 0x541ec%Z)) (ltac:(oD' 0x541ec%Z)). zcl4.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1283032 + 32) 8 spb) by zcell end.
zld (ltac:(oF' 0x541f0%Z)) (ltac:(oD' 0x541f0%Z)) (1283032 + 32) Cspb'.
zstep (ltac:(oF' 0x541f4%Z)) (ltac:(oD' 0x541f4%Z)). zstep (ltac:(oF' 0x541f8%Z)) (ltac:(oD' 0x541f8%Z)).
zbft (ltac:(oF' 0x541fc%Z)) (ltac:(oD' 0x541fc%Z)).
zstep (ltac:(oF' 0x54200%Z)) (ltac:(oD' 0x54200%Z)).
zbtk (ltac:(oF' 0x54204%Z)) (ltac:(oD' 0x54204%Z)).
zstep (ltac:(oF' 0x54230%Z)) (ltac:(oD' 0x54230%Z)). zstep (ltac:(oF' 0x54234%Z)) (ltac:(oD' 0x54234%Z)).
stepn (ltac:(oF' 0x54238%Z)) (ltac:(oD' 0x54238%Z)).
unfold art_f48. apply mst_refl. }
split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_cbr_sb := (ltac2:(TCodec.tc2 tcn__JbtRecycle4 "U1&?y5'RNyR0%211%5241'4y8%611%311p061'=':&Q0r5(RL+:(8%33A21%6251&RMr1%22C1%;3C41r6+C%;3I19%>231+QWTnH%92J1%B3J31r7+D%B3Q01@%E231&QC+2+Q5%3221%C2Q41%L3Q461&Q=+Vb\P0%221M&Q?&Q:%12F8+Q?%=2<1%5231'9z%;21L+R0%C2B1%;2O1%6241'<r8%?2L1%?22F%D21N%5231&D&Q7r;+Q0%F2Q71u8r9%7565321';'H&Q1vQNr>+Z`aL%QN3R:1QL/01R:r=r<%8576321+Z`i@%R43R@1R2/01R@%<5;R0165%>3F51+B%R93RG1R7%R<2R41r:%R72RH1%R@3RH31%RK1RL&Q8(1%RA3ROQLR?+3%RC3S11RA+4%RE3S31RC+8%RG3S51RE+9%RI3S71RG+E%RK3S91RI+F%RM3S;1RK+G%RO3S=1RM+H%S13S?1RO+I%S33SA1S1+J%S53SC1S3+K%S73SE1S5(3%11K%J3L31%K3M61%L3N91%M3O<1%N3Q0?1%O3Q1B1%Q03Q2E1%Q13Q3RO1%Q23Q4S71%Q33Q5J1%Q43Q6M1%Q53Q7Q01%Q63Q8Q31%Q73Q9Q61%Q93Q:SB1r3r2%SM221r@%SO213%T13T931p071pTJQB1%RN2QD1%RO2QK1qU2T=1%R<2T>1p0R>1p0RG1p0RN1p0S61p0S=1p0SA1p0SL1p0T41pT:TA1pUHTB1pU6TD1pQ2TE1pU0TK1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sb) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sb) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sb) 2%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sb) 3%nat 0%nat).
Variable hb : ltac:(sec_ty2 constr:(SEC_T_art_cbr_sb) 4%nat 0%nat).
Lemma art_cbr_sb : ltac:(sec_stmt2 constr:(SEC_T_art_cbr_sb) 5%nat 0%nat).
Proof using Type regs M rom spb hb.
intros H10 H19 H20 Hspb Hspb' Hhb Hsec Cspb.
destruct (Z_lt_le_dec hb spb) as [Lo|Hi].
- eexists. split.
{ zstep (ltac:(oF' 0x5423c%Z)) (ltac:(oD' 0x5423c%Z)).
zld (ltac:(oF' 0x54240%Z)) (ltac:(oD' 0x54240%Z)) (1283032 + 32) Cspb.
zstep (ltac:(oF' 0x54244%Z)) (ltac:(oD' 0x54244%Z)).
zbft (ltac:(oF' 0x54248%Z)) (ltac:(oD' 0x54248%Z)).
stepn (ltac:(oF' 0x5424c%Z)) (ltac:(oD' 0x5424c%Z)).
apply mst_refl. }
split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
- eexists. split.
{ zstep (ltac:(oF' 0x5423c%Z)) (ltac:(oD' 0x5423c%Z)).
zld (ltac:(oF' 0x54240%Z)) (ltac:(oD' 0x54240%Z)) (1283032 + 32) Cspb.
zstep (ltac:(oF' 0x54244%Z)) (ltac:(oD' 0x54244%Z)).
zbtk (ltac:(oF' 0x54248%Z)) (ltac:(oD' 0x54248%Z)).
zbtk (ltac:(oF' 0x542b4%Z)) (ltac:(oD' 0x542b4%Z)).
apply mst_refl. }
split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
End FPX.
Lemma art_cbr_stats_mem_facts : ltac2:(TCodec.tc2 tcn__JbtRecycle4 "R1'RNyR0%211'4y8%511%311p051'=&Q=+Q0r5%3221&Q?r6&QC+2+R0%3221%6251z%<217&Q:r7+TP0%3221%=218'9&Q6r:&Or9r8%36421:CF%6251&I(1'6%12NN(5&QD%12:O%34Q2Q21Q0+Rg@%F2<1+Q8%H221+@%94Q8Q821(3%11<%?3=31%@3>:1%B31HD%K2D1p0M1p0Q31p0Q61p0Q>1pSLQC1pSJQD1pTFQE1pV6QF1pUFQG1pQ2QI1").
Proof. intros M sp1 t n f1 f2 H1 H2 H3 H4. unfold art_cbr_stats_mem. split; [zgrows|]. eapply art_agree_sub; [zagree|]. zsub. Qed.
Lemma art_poison_mem_facts : ltac2:(TCodec.tc2 tcn__JbtRecycle4 "R?'RNyR0%211'4y8%511%311p051'='2&Q=+R0r;%3221&Q?r<&QC+2%2217%5241zr5%<221&Q:r6&QB%115%4231%>21:&B&Kr@r?r>r=r:r9r8%897654GJ321r7%;421@C'9&Q6rAr1%3221&I(1'6%12Q9Q9(5&QD%12EQ9%34Q=Q=1Q:%M1?%54Q?Q?B1(3%118%;3931%<3:61%>31A@%D2@1tQ4QGF1p0Q31p0Q:1p0Q>1p0QE1pV<QK1pT>QK1pS<QM1pUBQN1pU@QO1pU>R01pU<R11pU:R21pU8R31pTLR41pUDR51pQ2R71").
Proof.
intros M sp ra s0 s1 s2 s3 s4 s5 a k v H1 H2 H3 H4 M'. unfold M', art_poison_frame. split; [zgrows|].
eapply art_agree_sub; [eapply art_agree_trans; [|apply art_agree_Wf; [exact H3|exact H4]]; zagree|]. zsub.
Qed.
