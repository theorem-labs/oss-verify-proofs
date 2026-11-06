(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtAllocG JbtRefill1 JbtRefill2 JbtRefill3 JbtInitCache.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRefillCold () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInitCache."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRefill1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRefill2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1list"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"]; ["7art_ic_mc"; "7art_ic_mem"; "8art_gfa_frame"; "9art_gfa_mem"; ":getr"; ":mkst"; ";loaded_segments"; "<In"; "=add"; "=div"; "=le"; "=lt"; "=mul"; "=pow"; "=sub"; "0c"]; ["0ca"; "0chp"; "0fx"; "0ia"; "0na"; "0nf"; "0r"; "0r1"; "0r2"; "0rA"; "0raw"; "0regs"; "0rom"; "0sp"; ">BV"; ">Z_to_bv"]; [">bv"; ">bv_unsigned"; "0ws"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Definition art_refill_cold_rA (regs : bvmap 5 word) (sp ca c ia n : Z) : bvmap 5 word :=
(regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x56d9c : bv 64)%bv) 2 (Z_to_bv 64 (sp - 32))) 8 (Z_to_bv 64 (ca + 80 * c))) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (ca + 2560))) 12 (Z_to_bv 64 c)) 13 (Z_to_bv 64 (ca + 80 * c + 16))) 14 (Z_to_bv 64 n)).
Definition art_refill_cold_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ca c ia r nf na : Z) (ws : list Z) : word -> option byte :=
let n := Z.of_nat (length ws) in
let M3 := Wn 8 (Wn 8 (Wn 8 M (sp - 8) (bv_unsigned raw)) (sp - 16) (bv_unsigned (getr regs 8))) (sp - 24) (bv_unsigned (getr regs 9)) in
Wn 4 (art_gfa_mem (art_ic_mem M3 ca 31) (sp - 32) (0x56d9c : bv 64)%bv (art_refill_cold_rA regs sp ca c ia n) r (ca + 80 * c + 16) nf na ws) (ca + 80 * c) n.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_refill_a_cold := (ltac2:(TCodec.tc2 tcn__JbtRefillCold "X@&9y5'Q@yR0%211%5241'3y8%611%311p061'8'6&Dr8(Q>+1(4%33A21%6251r5%93A21r9+2%93G17%<231&Q?%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231&Hr6&L+R@%221F%5241%B2Q91%Q13Q981r<+<%Q13Q?1O%Q4231%Q63Q>1Gr=+=%Q63QD1Q4%Q9231r7%N2QE1%Q=3QE31&J+Q0%221O&K&M+R0%22Q91%42O1+Vb\P0%M218%:21F+TP0%<21H%Q12D2%;218'5%@2QJG+O%B2I1%4231z%E21L%C2M@%8221&<&NrA%221Jr@%542L1B&>&FrErB%921Q1%54431Q2rF+Ra0%847251&=rGrC%QL2QK9%QO221+4%R1221u4%85@721K'7'?&EvQ2rJ+ZkZL%S13S=1RO/01S=rIrH%8576321r1+ZkbL%S83SD1S6/01SD&A&;u8+8%Q:2O1&QA%12SLM%645>31+@%Q?2Q41%SD3T27SB%SG2F1%72T21%<4;641+H%QE2Q:1+9%SK3T91SI%SN2M1%>2T91%C4B751uO%F32QE1%Q45Q3KH1M%Q63QHM1%T52MT0+Zk\L%T53TA1T3/01TA%T:3TB41%T:2Q2SO%R52QJRM%SO2TF1%T>3TF31%T>2Q6HrD%SE2SD1%SH2R41%T52TL1%TD3TL51%TD2Q<G&I&@%118%321T>%T<2U31%TK3U361%TK2QCT9%T?2U6R6%TN3U621%TN2QFT7+R`0%T72RC1%TD2U;1%U33U;41%U32QKT0%TG2U>E%U63U>21%U62QNSN%T>2FQC%TK2UB1%U:3UB31+>%U93UG1U7%U<2R41%U>3UF1D%UI1UJ&G(0+3%U@3UN1U>%UA3UORJU?+B%UC3V11UA+C%UE3V31UC+D%UG3V51UE+E%UI3V71UG+F%UK3V91UI+G%UM3V;1UK%UN3V<R6UL+I%V03V>1UN+J%V23V@1V0+K%V43VB1V2(2%11J%I3K31%J3L61%K3M91%L3N<1%M3O>1%N3Q0A1%O3Q1D1%Q03Q2G1%Q13Q3J1%Q23Q4M1%Q33Q5Q01%Q43Q6Q21%Q63Q7S=1r3r2%VH221rL%VJ213%VL3W431p071pR>Q?1%U22QA1%U32QF1%U42QK1%U52QO1%U62R51%U72R91%U82RA1%U92RH1%U:2RM1%U;2S31qRDW@1%T<2WA1p0T>1p0TH1p0TL1p0U31p0U:1p0U?1p0UE1p0UH1p0UK1p0UO1p0V51p0V91p0VA1p0VG1p0W41p0W:1p0WB1pR8WM1pR0WN1pR2WO1pRLX01pRFX81pRJX31pFX41pRHX:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_cold) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_cold) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_cold) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_cold) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_cold) 4%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_cold) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_cold) 6%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_refill_a_cold) 7%nat 0%nat).
Lemma art_refill_a_cold : ltac:(sec_stmt2 constr:(SEC_T_art_refill_a_cold) 8%nat 0%nat).
Proof using Type regs M rom raw sp ca c ia.
intros H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hca Hca' Hc Hia A W Wca Cmc.
pose proof (art_ic_mc_range c Hc) as Hmc.
assert (RUN1 : exists r1 M1, msteps ASEGS (mkst regs (0x56d5c : word) M rom) (mkst r1 (0x56e00 : word) M1 rom)
/\ M1 = Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))
/\ getr r1 11 = Z_to_bv 64 (ca + 88) /\ getr r1 13 = Z_to_bv 64 32 /\ getr r1 15 = Z_to_bv 64 18446744073709551601
/\ getr r1 16 = Z_to_bv 64 15 /\ getr r1 17 = Z_to_bv 64 1024 /\ getr r1 5 = Z_to_bv 64 16 /\ getr r1 6 = Z_to_bv 64 17 /\ getr r1 7 = Z_to_bv 64 512
/\ getr r1 2 = Z_to_bv 64 (sp - 32) /\ getr r1 8 = Z_to_bv 64 (ca + 80 * c) /\ getr r1 10 = Z_to_bv 64 ca /\ getr r1 12 = Z_to_bv 64 ia /\ getr r1 14 = Z_to_bv 64 c
/\ (forall r : reg, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r)).
{ eexists. eexists. split.
- zstep (ltac:(oF' 0x56d5c%Z)) (ltac:(oD' 0x56d5c%Z)).
zsd (ltac:(oF' 0x56d60%Z)) (ltac:(oD' 0x56d60%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x56d64%Z)) (ltac:(oD' 0x56d64%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x56d68%Z)) (ltac:(oD' 0x56d68%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zstep (ltac:(oF' 0x56d6c%Z)) (ltac:(oD' 0x56d6c%Z)). zstep (ltac:(oF' 0x56d70%Z)) (ltac:(oD' 0x56d70%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 0) by (unfold apart in A; zcell) end.
zlw (ltac:(oF' 0x56d74%Z)) (ltac:(oD' 0x56d74%Z)) (ca + 80 * c + 4) Cmc'.
zbtk (ltac:(oF' 0x56d78%Z)) (ltac:(oD' 0x56d78%Z)).
zstep (ltac:(oF' 0x56db8%Z)) (ltac:(oD' 0x56db8%Z)). zstep (ltac:(oF' 0x56dbc%Z)) (ltac:(oD' 0x56dbc%Z)). zstep (ltac:(oF' 0x56dc0%Z)) (ltac:(oD' 0x56dc0%Z)). zstep (ltac:(oF' 0x56dc4%Z)) (ltac:(oD' 0x56dc4%Z)). zstep (ltac:(oF' 0x56dc8%Z)) (ltac:(oD' 0x56dc8%Z)). zstep (ltac:(oF' 0x56dcc%Z)) (ltac:(oD' 0x56dcc%Z)).
zstep (ltac:(oF' 0x56dd0%Z)) (ltac:(oD' 0x56dd0%Z)). zstep (ltac:(oF' 0x56dd4%Z)) (ltac:(oD' 0x56dd4%Z)).
stepn (ltac:(oF' 0x56dd8%Z)) (ltac:(oD' 0x56dd8%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]].
- split; [reflexivity|]. repeat (split; [kept_solve|]).
intros r Hr. cbn [In] in Hr. repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; kept_solve. }
destruct RUN1 as (r1 & M1 & RUN1 & EM1 & A11 & A13 & A15 & A16 & A17 & A5 & A6 & A7 & B2 & B8 & B10 & B12 & B14 & K1).
assert (W1 : wrA M1 ca 2592). { rewrite EM1. do 3 apply wr_Wn. exact Wca. }
destruct (art_ic_loop r1 M1 rom ca A11 A13 A15 A16 A17 A5 A6 A7 Hca Hca' W1) as (r2 & RUN2 & K2).
#[local] Ltac ick := unfold art_ic_kept; repeat split; intros E; discriminate E.
assert (C2 : cellA (art_ic_mem M1 ca 31) (ca + 80 * c + 4) 4 (art_ic_mc c)). { apply cell_ic_mc; [lia|lia|lia|cbn; lia]. }
assert (P2 : getr r2 2 = Z_to_bv 64 (sp - 32)) by (rewrite (K2 2%bv) by ick; exact B2).
assert (P8 : getr r2 8 = Z_to_bv 64 (ca + 80 * c)) by (rewrite (K2 8%bv) by ick; exact B8).
assert (P10 : getr r2 10 = Z_to_bv 64 ca) by (rewrite (K2 10%bv) by ick; exact B10).
assert (P12 : getr r2 12 = Z_to_bv 64 ia) by (rewrite (K2 12%bv) by ick; exact B12).
assert (P14 : getr r2 14 = Z_to_bv 64 c) by (rewrite (K2 14%bv) by ick; exact B14).
assert (RUN3 : exists rA, msteps ASEGS (mkst r2 (0x56e54 : word) (art_ic_mem M1 ca 31) rom) (mkst rA (0x56e5c : word) (art_ic_mem M1 ca 31) rom)
/\ getr rA 1 = (0x56d9c : bv 64)%bv /\ getr rA 2 = Z_to_bv 64 (sp - 32) /\ getr rA 8 = Z_to_bv 64 (ca + 80 * c) /\ getr rA 9 = Z_to_bv 64 (art_ic_mc c / 2)
/\ getr rA 10 = Z_to_bv 64 ia /\ getr rA 11 = Z_to_bv 64 (ca + 2560) /\ getr rA 12 = Z_to_bv 64 c /\ getr rA 13 = Z_to_bv 64 (ca + 80 * c + 16) /\ getr rA 14 = Z_to_bv 64 (art_ic_mc c / 2)
/\ (forall r : reg, In r [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rA r = getr r2 r)).
{ eexists. split.
- zlw (ltac:(oF' 0x56e54%Z)) (ltac:(oD' 0x56e54%Z)) (ca + 80 * c + 4) C2.
stepn (ltac:(oF' 0x56e58%Z)) (ltac:(oD' 0x56e58%Z)).
stepn (ltac:(oF' 0x56d7c%Z)) (ltac:(oD' 0x56d7c%Z)). rwH. rewrite art_srliw_small by lia. change (2 ^ 1) with 2.
zstep (ltac:(oF' 0x56d80%Z)) (ltac:(oD' 0x56d80%Z)). zstep (ltac:(oF' 0x56d84%Z)) (ltac:(oD' 0x56d84%Z)). zstep (ltac:(oF' 0x56d88%Z)) (ltac:(oD' 0x56d88%Z)). zstep (ltac:(oF' 0x56d8c%Z)) (ltac:(oD' 0x56d8c%Z)). zstep (ltac:(oF' 0x56d90%Z)) (ltac:(oD' 0x56d90%Z)). zstep (ltac:(oF' 0x56d94%Z)) (ltac:(oD' 0x56d94%Z)).
stepn (ltac:(oF' 0x56d98%Z)) (ltac:(oD' 0x56d98%Z)).
first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]].
- split; [gres; rwH; zval|]. repeat (split; [kept_solve|]).
intros r Hr. cbn [In] in Hr. repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; kept_solve. }
destruct RUN3 as (rA & RUN3 & Q1 & Q2 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & K3).
exists rA. split.
{ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. rewrite <- EM1. exact RUN3. }
repeat (split; [assumption|]).
intros r Hr. rewrite (K3 r Hr). pose proof Hr as Hr'. cbn [In] in Hr.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] | False => destruct Hr end; (rewrite K2 by ick; apply K1; cbn; tauto).
Qed.
End SE.
#[using="Type"] Lemma art_gfa_frame_ext : ltac2:(TCodec.tc2 tcn__JbtRefillCold "R?'Q@yR0%211'3y8%511%311p051'8&9y5%2219%<12&Gr1(0(Q>+8(4%33921+9%53;13+B%73=15+C%93?17+D%;3A19+E%=3C1;+F%?3E1=+G%A3G1?+H%C3I1A+I%E3K1C+J%G3M1E+K%I3O1G(2%11O%M3Q031%N3Q161%O3Q291%Q03Q3<1%Q13Q4?1%Q23Q5B1%Q33Q6E1%Q43Q7H1%Q53Q8K1%Q63Q9N1%Q73Q:Q11%Q83Q;Q41%Q;3Q<Q:1'6&Dr4r2%3221r3%5213%73QN31p091pR>QF1&Br6r5%3421;8%4432<;%?3R121p071pRBQO1pR@R01pRFR:1pRLR51pFR71").
Proof.
intros M sp raw r1 r2 H. unfold art_gfa_frame.
rewrite (H 8%bv), (H 9%bv), (H 18%bv), (H 19%bv), (H 20%bv), (H 21%bv), (H 22%bv), (H 23%bv), (H 24%bv), (H 25%bv), (H 26%bv), (H 27%bv) by (cbn; tauto).
reflexivity.
Qed.
#[using="Type"] Lemma art_gfa_mem_ext : ltac2:(TCodec.tc2 tcn__JbtRefillCold "RK'Q@yR0%211'3y8%511%311p051'8&9y5%2219'1%115%>14&Gr1(0(Q>+8(4%33;21+9%53=13+B%73?15+C%93A17+D%;3C19+E%=3E1;+F%?3G1=+G%A3I1?+H%C3K1A+I%E3M1C+J%G3O1E+K%I3Q11G(2%11O%M3Q031%N3Q161%O3Q291%Q03Q3<1%Q13Q4?1%Q23Q5B1%Q33Q6E1%Q43Q7H1%Q53Q8K1%Q63Q9N1%Q73Q:Q11%Q83Q;Q41%Q;3Q<Q:1'6&Dr9r2%3221r8%5213%73R031p091pS8QF1&Cr;r:r6r5r4r3%7965?<4321>r7%9987A16543@%D3R831p0<1pS6R41pR:R:1pR<R;1pR4R<1pR>R=1pRBR;1pR@R<1pRFRF1pRLRA1pFRC1").
Proof. intros. unfold art_gfa_mem. rewrite (art_gfa_frame_ext M sp raw r1 r2) by assumption. reflexivity. Qed.
End FPX.
