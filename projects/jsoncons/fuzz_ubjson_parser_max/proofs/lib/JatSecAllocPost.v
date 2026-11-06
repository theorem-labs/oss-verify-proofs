(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac JatLeaf JatAllocG JatDepotA JatSecAlloc ArtSizeLog JatPoison JatPoisonRun JatPoison2 JatFp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatSecAllocPost () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatSecAllocPost.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0C"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0D"; "0F"; "4bvmap"; "0M"; "0M'"; "0M1"; "0M2"]; ["5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_tsd"; "9SB"; "9art_layout"; "9kHighMemBeg"; ":appmem"; ":sec_b1_mem"; ":sec_hm"; ":sec_mx"; ":sec_postA_mem"; ":sec_postB_mem"]; [":sec_tail_mem"; ";getr"; ";mkst"; ";regupd"; "<mem_grows"; "=loaded_segments"; ">add"; ">div"; ">le"; ">log2"; ">lt"; ">modulo"; ">mul"; ">pow"; ">sub"; "0a"]; ["0b"; "0bsl"; "0ctx"; "0cur"; "0fx"; "0key"; "0lg"; "0msz"; "0mx"; "0n"; "0na"; "0nch"; "0nres"; "0pab"; "0pab2"; "0q"]; ["0r"; "0r7"; "0regs"; "0regs'"; "0rg"; "0rom"; "0s"; "0sec"; "0st16"; "0st24"; "0stat"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_unsigned"; "0t"]; ["0thr"; "0tp"; "0tsd"; "0x"; "0x1"; "0x18"; "0x19"; "0x20"; "0x21"; "0x22"; "0x23"; "0x24"; "0x25"; "0x8"; "0x9"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma zdiv8_mul : ltac2:(TCodec.tc2 tcn__JatSecAllocPost "@'8'4&Q;r1+8%3221z%63721&Q<&Q7r2%2217%4218%<3=13p071pU8?1").
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). lia. Qed.
Lemma zdiv8_up7 : ltac2:(TCodec.tc2 tcn__JatSecAllocPost "C'8'4&Q;r1+8%3221z%63721&Q<&Q7&Q6r2+7%3221%521:%721;%?3@15p0:1pU8B1").
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)). lia. Qed.
Lemma mod8_add : ltac2:(TCodec.tc2 tcn__JatSecAllocPost "B'8'4&Q;r2+8%3221z%63721&Q6r4r3%3221%:218%<3=17p071p081pS2@1pS0A1").
Proof. intros a b Ha Hb. rewrite Z.add_mod, Ha, Hb by lia. reflexivity. Qed.
Ltac mod8 := first [ assumption | reflexivity | apply mod8_add; mod8 ].
Lemma mod8_of_4096 : ltac2:(TCodec.tc2 tcn__JatSecAllocPost ">'8'4&Q;r1+TP0%3221z%63721r2+8%8221%:3;15p051pT2=1").
Proof. intros r Hr4. apply (proj2 (Z.mod_divide r 8 ltac:(lia))). apply (Z.divide_trans 8 4096 r); [exists 512; reflexivity | apply (proj1 (Z.mod_divide r 4096 ltac:(lia))); exact Hr4]. Qed.
Ltac zdef u e RNG :=
let E := fresh "E" u in let R := fresh "R" u in
pose (u := e); assert (E : u = e) by reflexivity; clearbody u;
assert (R : 0 <= u < 2 ^ 64) by (rewrite E; RNG).
Ltac divfacts x d := pose proof (Z.div_mod x d ltac:(lia)); pose proof (Z.mod_pos_bound x d ltac:(lia)).
Ltac gresH H := repeat first [ rewrite getr_same in H by reg_neq_tac | rewrite getr_other in H by reg_neq_tac ]; rewrite ?getr_zero in H.
Ltac nlit := let E := fresh in intros E; discriminate E.
Ltac pk := unfold art_poison_kept; repeat split; nlit.
Section SE.
Variables (M M' : word -> option byte).
Lemma art_layout_agree : (forall x : word, U x < 0x691000 -> M' x = M x) -> art_layout M -> art_layout M'.
Proof.
intros AG L.
unfold art_layout in *.
zsplit;
match goal with |- cell _ _ ?c ?m _ => apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | tauto] end.
Qed.
End SE.
Lemma art_tsd_agree : ltac2:(TCodec.tc2 tcn__JatSecAllocPost "R2'R=yR0%211'1y8%511%311p051'8&Q:&R>r1%22;1+VbTP0%5221'4r8r2%211r9%113%63?31p081pU8E1'3&Q8&Q6r4+TH%3221%521B+U0%6251%H2E1%:241r:%11C%F3OA1p041pU8Q51r7%Q021Lr6&Q<+8%2215%D241%E213%G21Q3&Fr;r5%362Q1Q4<:1%463BQ2Q5=;p021p071p0?1p0B1p0Q31pU0QC1pS6QD1pU6QE1pS<QF1pU4QG1pLQI1pJQJ1").
Proof.
intros M M' tp key tsd ctx t AG AGc Htp Htsd T. unfold art_tsd in *.
destruct T as (C1 & C2 & C3 & C4 & C5 & REST).
zsplit; try lia.
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C1].
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C2].
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C3].
- apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C4].
- apply (cell_agree M M'); [intros x Hx; apply AGc; cbn in Hx; lia | lia | cbn; lia | exact C5].
Qed.
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_sec_h1_fn := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "WN&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1r:(R;+1(2%33A21%6251&R<+acSH%22C1%;3C41r;+2%;3I19%>231&Q>r8+T@%3221%<2M1%E3M61r<+:%E3Q31C%H231r4%C2Q41%L3Q431r=+C%L3Q:1J%O231r6%J2Q;1%Q33Q;31r>+E%Q33QA1Q1%Q6231+8%Q12QB1%Q:3QB31r?+H%Q:3QH1Q8%Q=231+7%Q82QI1%QA3QI31&Q8+VbTP0+^@%Q52H1%4231&Q:&Q=+Q?%22Q=1%42G1z%;21QA&Q;%12Q9G%R03R114+<%:2QE1%A21O&Q6+TP0%22Q21%E21L%F23Q4%;2N4%R:3R;1>r@rB%9221%G21D+RPP0rE%O221rF+QP0%@221%N21Q2%Q4274rG+R0%E221%Q321Q7rD%Q:2=1+`0%J2>1%Q821Q<&C&Q5rNrL%RD21Q@%54431QA&BrOrM+S8%RJ221u8+Zif@%75<6321rQ0+S@%S02>1%;5@316>rQ1+SH%S42=1%?5D31:CrQ2+T0%S82:1%C5H31>ArQ3%E5J1=@QFrQ4+QVYa8%H5M21CKrQ5%QL2HS>%K5Q021FR5'D&Q2vQDrQ7+a\i<%T43T@1T2/01T@rQ6%756521;&Q3+Zii8%T52TF1%339T81+S0%T02D1%T92TJ1%734T41%T@3TNS;T>%T<2TMN%:3321+9%TD3U21TB%T@2U1N%>3421%TB2U3QC%@32T31+;%TJ3U81TH%TF2U7RI%D3421%TM3U;ROTK+WJ%TJ2U;1%H3431+=%U23U@1U0+_ooooooooolP1%TO2U@1%M3531+B%U73UE1U5%U32UDQI%Q13421+D%U;3UI1U9%Q4331E%S<2S;R9%S=21R3%U:2UK1%Q834T=1+F%UB3V01U@%SB2R4R?%U?2V01%Q=3531+G%UG3V51UE%Q@3319+I%UJ3V81UH%UF2V7>%QD3421+_X_0%UN3V:1UL/01V:&@u4+T8%UF2R:1+_oooooneZeZe:%544QO21%R65R5:71R:%R83S9R01p0R:1p0R>1p0RB1p0RE1p0RJ1p0RO1p0S41p0S=1p0SD1p0SH1p0SK1p0T01p0T21p0T71p0T;1p0T@1p0TC1p0TE1p0TJ1p0TN1p0U21p0U51p0U;1p0UA1p0UI1p0V11p0V91p0VA1p0VL1pFW91pT2W:1pSDW;1pS@W<1pTFW=1pT@W>1pT>W?1pT<WA1pJWB1pT6WH1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 3%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 4%nat 0%nat).
Variable stat : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 5%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 7%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 8%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_sec_h1_fn) 9%nat 0%nat).
Lemma sec_h1_fn : ltac:(sec_stmt2 constr:(SEC_T_sec_h1_fn) 10%nat 0%nat).
Proof using Type regs M rom s sec stat msz n r F.
intros H1 H2 H10 H19 H21 H24 Hs Hs' Hn Hn8 Hm Hnm Hr Hr4 Hrm Hsec Hsec' Hst Hst' HF HF' W C104 C112 C120 C128 Cpg C38 C144.
pose proof (mod8_of_4096 r Hr4) as Hr8.
stepret (ltac:(oF' 0x8b32c%Z)) (ltac:(oD' 0x8b32c%Z)) (Z_to_bv 64 0x8cc78 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8cc78%Z)) (ltac:(oD' 0x8cc78%Z)).
zstep (ltac:(oF' 0x8cc7c%Z)) (ltac:(oD' 0x8cc7c%Z)).
stepn (ltac:(oF' 0x8cc80%Z)) (ltac:(oD' 0x8cc80%Z)).
zstep (ltac:(oF' 0x8b304%Z)) (ltac:(oD' 0x8b304%Z)). zstep (ltac:(oF' 0x8b308%Z)) (ltac:(oD' 0x8b308%Z)).
zbtk (ltac:(oF' 0x8b30c%Z)) (ltac:(oD' 0x8b30c%Z)).
zstep (ltac:(oF' 0x8b31c%Z)) (ltac:(oD' 0x8b31c%Z)).
stepret (ltac:(oF' 0x8b320%Z)) (ltac:(oD' 0x8b320%Z)) (Z_to_bv 64 0x8cc84 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8cc84%Z)) (ltac:(oD' 0x8cc84%Z)). zstep (ltac:(oF' 0x8cc88%Z)) (ltac:(oD' 0x8cc88%Z)).
zsw (ltac:(oF' 0x8cc8c%Z)) (ltac:(oD' 0x8cc8c%Z)) (s - 136) 18446744072277895850 ltac:(rewok W).
zstep (ltac:(oF' 0x8cc90%Z)) (ltac:(oD' 0x8cc90%Z)). zstep (ltac:(oF' 0x8cc94%Z)) (ltac:(oD' 0x8cc94%Z)).
stepn (ltac:(oF' 0x8cc98%Z)) (ltac:(oD' 0x8cc98%Z)).
zstep (ltac:(oF' 0x8b304%Z)) (ltac:(oD' 0x8b304%Z)). zstep (ltac:(oF' 0x8b308%Z)) (ltac:(oD' 0x8b308%Z)).
zbtk (ltac:(oF' 0x8b30c%Z)) (ltac:(oD' 0x8b30c%Z)).
zstep (ltac:(oF' 0x8b31c%Z)) (ltac:(oD' 0x8b31c%Z)).
stepret (ltac:(oF' 0x8b320%Z)) (ltac:(oD' 0x8b320%Z)) (Z_to_bv 64 0x8cc9c : word) ltac:(rwH; reflexivity).
zbft (ltac:(oF' 0x8cc9c%Z)) (ltac:(oD' 0x8cc9c%Z)).
stepn (ltac:(oF' 0x8cca0%Z)) (ltac:(oD' 0x8cca0%Z)).
stepn (ltac:(oF' 0x8cca4%Z)) (ltac:(oD' 0x8cca4%Z)).
zstep (ltac:(oF' 0x871ec%Z)) (ltac:(oD' 0x871ec%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0x132628 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
zld (ltac:(oF' 0x871f0%Z)) (ltac:(oD' 0x871f0%Z)) 0x132628 C38'.
zld (ltac:(oF' 0x871f4%Z)) (ltac:(oD' 0x871f4%Z)) (F + 144) C144'.
zbtk (ltac:(oF' 0x871f8%Z)) (ltac:(oD' 0x871f8%Z)).
stepret (ltac:(oF' 0x87214%Z)) (ltac:(oD' 0x87214%Z)) (Z_to_bv 64 0x8cca8 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8cca8%Z)) (ltac:(oD' 0x8cca8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (R1 : cellA X (s - 104) 8 0x566d0) by zcell; assert (R2 : cellA X (s - 112) 8 stat) by zcell;
assert (R3 : cellA X (s - 120) 8 sec) by zcell; assert (R4 : cellA X (s - 128) 8 msz) by zcell; assert (Cpg' : cellA X sec 8 4096) by zcell end.
zld (ltac:(oF' 0x8ccac%Z)) (ltac:(oD' 0x8ccac%Z)) (s - 104) R1. zld (ltac:(oF' 0x8ccb0%Z)) (ltac:(oD' 0x8ccb0%Z)) (s - 112) R2. zld (ltac:(oF' 0x8ccb4%Z)) (ltac:(oD' 0x8ccb4%Z)) (s - 120) R3. zld (ltac:(oF' 0x8ccb8%Z)) (ltac:(oD' 0x8ccb8%Z)) (s - 128) R4.
zstep (ltac:(oF' 0x8ccbc%Z)) (ltac:(oD' 0x8ccbc%Z)).
stepret (ltac:(oF' 0x8ccc0%Z)) (ltac:(oD' 0x8ccc0%Z)) (Z_to_bv 64 0x566d0 : word) ltac:(rwH; reflexivity).
zbft (ltac:(oF' 0x566d0%Z)) (ltac:(oD' 0x566d0%Z)).
zstep (ltac:(oF' 0x566d4%Z)) (ltac:(oD' 0x566d4%Z)).
zld (ltac:(oF' 0x566d8%Z)) (ltac:(oD' 0x566d8%Z)) sec Cpg'.
zstep (ltac:(oF' 0x566dc%Z)) (ltac:(oD' 0x566dc%Z)).
stepn (ltac:(oF' 0x566e0%Z)) (ltac:(oD' 0x566e0%Z)). rwH. rewrite art_zb_and by lia.
replace (Z.land 4095 r) with 0 by (rewrite Z.land_comm; rewrite Z.land_ones with (n := 12); [|lia]; change (2 ^ 12) with 4096; lia).
zbft (ltac:(oF' 0x566e4%Z)) (ltac:(oD' 0x566e4%Z)).
zstep (ltac:(oF' 0x566e8%Z)) (ltac:(oD' 0x566e8%Z)). zstep (ltac:(oF' 0x566ec%Z)) (ltac:(oD' 0x566ec%Z)).
stepn (ltac:(oF' 0x566f0%Z)) (ltac:(oD' 0x566f0%Z)). rwH. rewrite art_zb_and by lia.
replace (Z.land (4096 + r) 7) with 0 by (rewrite Z.land_ones with (n := 3); [|lia]; change (2 ^ 3) with 8; rewrite Z.add_mod, Hr8 by lia; reflexivity).
zstep (ltac:(oF' 0x566f4%Z)) (ltac:(oD' 0x566f4%Z)). zstep (ltac:(oF' 0x566f8%Z)) (ltac:(oD' 0x566f8%Z)). zstep (ltac:(oF' 0x566fc%Z)) (ltac:(oD' 0x566fc%Z)).
zstep (ltac:(oF' 0x56700%Z)) (ltac:(oD' 0x56700%Z)).
zstep (ltac:(oF' 0x56704%Z)) (ltac:(oD' 0x56704%Z)). zstep (ltac:(oF' 0x56708%Z)) (ltac:(oD' 0x56708%Z)). zstep (ltac:(oF' 0x5670c%Z)) (ltac:(oD' 0x5670c%Z)).
stepn (ltac:(oF' 0x56710%Z)) (ltac:(oD' 0x56710%Z)). rwH. unfold v_andi. rewrite (art_u_lit (4096 + r + n)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
rewrite zdiv8_mul by mod8.
stepn (ltac:(oF' 0x56714%Z)) (ltac:(oD' 0x56714%Z)). rwH. unfold v_andi. rewrite (art_u_lit (4096 + r + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
rewrite zdiv8_up7 by mod8.
zstep (ltac:(oF' 0x56718%Z)) (ltac:(oD' 0x56718%Z)). zstep (ltac:(oF' 0x5671c%Z)) (ltac:(oD' 0x5671c%Z)). zstep (ltac:(oF' 0x56720%Z)) (ltac:(oD' 0x56720%Z)).
stepn (ltac:(oF' 0x56724%Z)) (ltac:(oD' 0x56724%Z)).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_sec_h3_run := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "Z@&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1r<(R;+2(2%33A21%6251&R<&Q>r9+S0%3221%52F1%>3F71r=+9%>3L1<%A231%;2L9%D3L21r>+:%D3Q21B%G231r6%B2Q31%K3Q331r?+B%K3Q91I%N231r:%I2Q:1%Q23Q:31r@+C%Q23Q@1Q0%Q5231%Q73Q?16rA+D%Q73QE1Q5%Q:231%Q<3QD1;rB+E%Q<3QJ1Q:%Q?231&Q6+TP0r;%3221%421QC%Q>2QO1%QG3QO71rC+F%QG3R51QE%QJ231%;2Q7QJ%QE2R61%QN3R631rD+H%QN3R<1QL%R1231+7%QL2R=1%R53R=31rE+I%R53RC1R3%R8231%I2HQE%R32RD1%R<3RD31&Q8z%221Q<&Q;+8%22Q:1%RC3RD15&Q=+<%22RB1%:21O%Q72Q0Q6%<21J%=2Q8Q2%;2LQ9%RL3RM1>&Q:rG%Q>2I1+Q?%=2RM1%5231+RPP0rI%H221rJ+QP0%QG221+VbTP0%=221rK+c8%QL221+4%O221%S@3SA1Q2rH%Q52R01%R22?R1+R0%Q12SA1%I231%Q:2Q9C%K2B3%Q<2Q;C%M2?5'3%Q?2Q>A%Q92SIRD%Q12C1%4231&ArO+R8%RB221+@rQ0+Q0%744321%RG236rQ4%:4261Q3rQ2%QO2Q31&B&Q5rQ9%RO25>u8rQ1%6554321rQ:rQ3+R@%S6221%;5:4176rQ;rQ8%>5=21:S9rQ<%S<2>QAu4%B5A321RArQ=+QH%SA2>1%F5E31B>&CrQ>rQ7%SF21Q5%44J31Q4rQ?%64L1KQ4rQ@%SK2<R0%94O21QO'5'D&Q2vQDrQC+ZiiL%UA3UM1U?/01UMrQBrQA%8576321r1+Zin<%UH3V41UF/01V4&@%T=2Q5QL+1%T?2Q<1%44Q@;31%TA2Q9Q<%TB2QDN%74QC321%84QD1Q9Q9%TE2Q:SE%:4QF21Q2%TG2Q<R4%<4QH21Q9%TI2Q1RN%>4Q=21<%L5KC@1E%N3QOE1%V=2EUG%TN2TMQC%V82VI1%VA3VI31+=%V@3VN1V>%VC2K1%V=2VNQK%VF3VN21%VF2NU8%V@2W1QL%VI3W121%VI2Q1VD%VB2Q@V@%VD2W51%VM3W531%W81W9&6%W032Q7V9%211r2+;%W13W?1VO%W53731%711r3%W53WCTCW3%W93;21%;11r4%W<3>1I%>11r5+>%W=3WK1W;%WA3C31%C11+?%WA3WO1W?%WE3GVL1%G11r7%WE3X3SDWC%WI3K21%K11r8%WL3N1V=%N11%WM2VNWDrQL%WO21WF%X13X931p051p091p0>1p0C1p0I1p0M1p0Q21p0Q81pT:Q<1%T@2Q>1%TA2QC1%TB2QG1%TC2QM1%TD2R21qT8XG1%S32XH1p0S51p0S91p0S<1p0SB1p0SG1p0SL1p0T01p0T61p0T>1p0TA1p0TE1p0TN1p0U41p0U61p0U81p0U:1p0U<1p0UA1p0UD1p0UK1p0V11p0V51p0V<1p0V?1p0VA1p0VD1p0VI1p0VN1p0W21p0W:1p0WB1p0WJ1p0X61p0X<1p0XB1p0XJ1p0Y21p0Y91pSHYI1pDYJ1p2YK1pU2YL1pT2YM1pSDYN1pS@YO1pT@Z01pT>Z11pT<Z31pJZ41pT6Z:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 3%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 4%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 6%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 7%nat 0%nat).
Variable thr : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 8%nat 0%nat).
Variable C : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 9%nat 0%nat).
Variable D : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 10%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_sec_h3_run) 11%nat 0%nat).
Lemma sec_h3_run : ltac:(sec_stmt2 constr:(SEC_T_sec_h3_run) 12%nat 0%nat).
Proof using Type regs M rom s sec msz n r thr C D nch.
intros H2 H9 H10 H18 H19 H20 H21 H22 H24 H25 Hn Hn8 Hm Hnm Hr Hr4 Hrm Hsec Hsec' Hsec8 Ht Ht' HC HC' HD HD' Hnch A1 A2 Hri
CC CD Cpg Clk Cnch WT WR WL.
pose proof (mod8_of_4096 r Hr4) as Hr8.
eexists. split; [|split; [|split; [|split; [|split]]]].
- zld (ltac:(oF' 0x5673c%Z)) (ltac:(oD' 0x5673c%Z)) (thr + 72) CC.
zld (ltac:(oF' 0x56740%Z)) (ltac:(oD' 0x56740%Z)) (thr + 80) CD.
stepn (ltac:(oF' 0x56744%Z)) (ltac:(oD' 0x56744%Z)). rwH. rewrite art_zb_and by lia.
replace (Z.land (4096 + r) 7) with 0 by (rewrite Z.land_ones with (n := 3); [|lia]; change (2 ^ 3) with 8; rewrite Z.add_mod, Hr8 by lia; reflexivity).
zstep (ltac:(oF' 0x56748%Z)) (ltac:(oD' 0x56748%Z)). zstep (ltac:(oF' 0x5674c%Z)) (ltac:(oD' 0x5674c%Z)).
zsd (ltac:(oF' 0x56750%Z)) (ltac:(oD' 0x56750%Z)) (thr + 72) (C + 1) ltac:(rewok WT).
zsd (ltac:(oF' 0x56754%Z)) (ltac:(oD' 0x56754%Z)) (thr + 80) (D + msz) ltac:(rewok WT).
zbft (ltac:(oF' 0x56758%Z)) (ltac:(oD' 0x56758%Z)).
zstep (ltac:(oF' 0x5675c%Z)) (ltac:(oD' 0x5675c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X sec 8 4096) by zcell end.
zld (ltac:(oF' 0x56760%Z)) (ltac:(oD' 0x56760%Z)) sec Cpg'.
zstep (ltac:(oF' 0x56764%Z)) (ltac:(oD' 0x56764%Z)).
stepn (ltac:(oF' 0x56768%Z)) (ltac:(oD' 0x56768%Z)). rwH. rewrite art_zb_and by lia.
replace (Z.land 4095 (4096 + r)) with 0 by (rewrite Z.land_comm; rewrite Z.land_ones with (n := 12); [|lia]; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hr4 by lia; reflexivity).
zbft (ltac:(oF' 0x5676c%Z)) (ltac:(oD' 0x5676c%Z)).
zbft (ltac:(oF' 0x56770%Z)) (ltac:(oD' 0x56770%Z)).
zbft (ltac:(oF' 0x56774%Z)) (ltac:(oD' 0x56774%Z)).
zstep (ltac:(oF' 0x56778%Z)) (ltac:(oD' 0x56778%Z)).
replace (4096 + r - 4096) with r by lia.
zsd (ltac:(oF' 0x5677c%Z)) (ltac:(oD' 0x5677c%Z)) r r ltac:(rewok WR).
zsd (ltac:(oF' 0x56780%Z)) (ltac:(oD' 0x56780%Z)) (r + 8) msz ltac:(rewok WR).
zsd (ltac:(oF' 0x56784%Z)) (ltac:(oD' 0x56784%Z)) (r + 16) n ltac:(rewok WR).
zbft (ltac:(oF' 0x56788%Z)) (ltac:(oD' 0x56788%Z)).
zstep (ltac:(oF' 0x5678c%Z)) (ltac:(oD' 0x5678c%Z)). zstep (ltac:(oF' 0x56790%Z)) (ltac:(oD' 0x56790%Z)).
stepn (ltac:(oF' 0x56794%Z)) (ltac:(oD' 0x56794%Z)). rwH. unfold v_andi. rewrite (art_u_lit (sec + 616)) by lia. change (bv_wrap 64 (-4)) with 18446744073709551612.
change 18446744073709551612 with (2 ^ 64 - 2 ^ 2). rewrite sa_land_down by lia. change (2 ^ 2) with 4. rewrite Hsec8, Z.sub_0_r.
zstep (ltac:(oF' 0x56798%Z)) (ltac:(oD' 0x56798%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (sec + 616) 4 0) by zcell; assert (WL' : wokA X (sec + 616) 4) by (rewok WL) end.
chain_step; [reflexivity
| eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (sec + 616)) _ (Z_to_bv 64 0));
[exact (ltac:(oF' 0x5679c%Z)) | reflexivity | exact (ltac:(oD' 0x5679c%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hsec8
| exact Clk' | apply art_bytes4; lia ]
| ]. wpc. rewrite art_v_lw_small by lia.
chain_step; [reflexivity | eapply art_step_addi_r; [exact (ltac:(oF' 0x567a0%Z)) | reflexivity | exact (ltac:(oD' 0x567a0%Z)) | reflexivity] | ]. wpc. gres. rwH.
match goal with |- context [v_addi ?x (bv_signed ?i)] => replace (v_addi x (bv_signed i)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
chain_step; [reflexivity | eapply art_step_xor_r; [exact (ltac:(oF' 0x567a4%Z)) | reflexivity | exact (ltac:(oD' 0x567a4%Z)) | reflexivity] | ]. wpc. gres. rewrite art_zb_xor by lia. change (Z.lxor 0 1) with 1.
chain_step; [reflexivity | eapply art_step_and_r; [exact (ltac:(oF' 0x567a8%Z)) | reflexivity | exact (ltac:(oD' 0x567a8%Z)) | reflexivity] | ]. wpc. gres. rwH. rewrite art_zb_and by lia. change (Z.land 1 255) with 1.
chain_step; [reflexivity | eapply art_step_xor_r; [exact (ltac:(oF' 0x567ac%Z)) | reflexivity | exact (ltac:(oD' 0x567ac%Z)) | reflexivity] | ]. wpc. gres. rewrite art_zb_xor by lia. change (Z.lxor 0 1) with 1.
chain_step; [reflexivity
| eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (sec + 616)));
[exact (ltac:(oF' 0x567b0%Z)) | reflexivity | exact (ltac:(oD' 0x567b0%Z)) | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hsec8 | gres; reflexivity
| exact WL' ]
| ]. wpc.
change (wbytes ?M0 (Z_to_bv 64 (sec + 616)) (word_to_le_bytes 4 (Z_to_bv 64 1))) with (Wn 4 M0 (sec + 616) 1).
zbft (ltac:(oF' 0x567b4%Z)) (ltac:(oD' 0x567b4%Z)).
zstep (ltac:(oF' 0x567b8%Z)) (ltac:(oD' 0x567b8%Z)).
zbft (ltac:(oF' 0x567bc%Z)) (ltac:(oD' 0x567bc%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cnch' : cellA X (sec + 56) 8 nch) by zcell end.
zld (ltac:(oF' 0x567c0%Z)) (ltac:(oD' 0x567c0%Z)) (sec + 56) Cnch'.
stepn (ltac:(oF' 0x567c4%Z)) (ltac:(oD' 0x567c4%Z)). rwH. rewrite art_zb_srli by lia.
replace (nch / 2 ^ 20) with 0 by (symmetry; apply Z.div_small; lia).
zbft (ltac:(oF' 0x567c8%Z)) (ltac:(oD' 0x567c8%Z)).
apply mst_refl.
- kept_solve. - kept_solve. - kept_solve. - kept_solve.
- intros rg N10 N11 N12 N13 N14 N15 N16 N21. kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_sec_sl_run := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "TC&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1r6(R;+B(2%33A21%6251&R<r3%22C1%;3C41r7+9%;3I19%>231%@3H16'3&Q8&Q=+2+<%3221r5%6221&Q:+Q?%8271%3251%<251+TP0%=218&Q6+QP0%22Q01+R0%A2@1%<231z%E21Q5%?2Q64%H221&B&Q5r;r8+Q@%?221u8%756521Q5'5'D&Q2vQDr>+Zin<%QE3R11QC/01R1r=r<%8576321r1+ZjSD%QL3R81QJ/01R8%=5<4176%?3G61+C%R13R?1QO%R4281&Q>+QO&Q9%11M%4231%R32RD1%R<3RD71+>%R;3RI1R9%R>2B1r9%R92RJ1%RB3RJ31%RM1RN&6+;%RC3S11RA%RG34J1%411r2%RG3S5R5RE%RK3821%811%RM3:RD?%:11r4+?%RN3S<1RL%S23?31%?11+@%S23S@1S0%S63CR?1%C11%S83ES6Q4%E11%S92QMRNrE%S;21S0%S=3SE31p051p081p0=1p0C1p0F1p0K1pT:Q11%S42Q31%S52Q:1%S62QE1qT8SO1%R72T01p0R91p0RB1p0RG1p0RN1p0S11p0S?1p0SE1pSJT21pT@T31pS@T41pT<T61pJT71pT6T=1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sec_sl_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_sec_sl_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sec_sl_run) 2%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_sec_sl_run) 3%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_sec_sl_run) 4%nat 0%nat).
Variable nres : ltac:(sec_ty2 constr:(SEC_T_sec_sl_run) 5%nat 0%nat).
Lemma sec_sl_run : ltac:(sec_stmt2 constr:(SEC_T_sec_sl_run) 6%nat 0%nat).
Proof using Type regs M rom msz sec nres.
intros H18 H9 Hm Hs Hs' Hn C48.
assert (HL : 12 <= Z.log2 msz <= 46).
{ split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
divfacts msz (2 ^ 1). zdef S1 (Z.lor msz (msz / 2 ^ 1)) ltac:(apply lor_range64; lia).
divfacts S1 (2 ^ 2). zdef S2 (Z.lor S1 (S1 / 2 ^ 2)) ltac:(apply lor_range64; lia).
divfacts S2 (2 ^ 4). zdef S3 (Z.lor S2 (S2 / 2 ^ 4)) ltac:(apply lor_range64; lia).
divfacts S3 (2 ^ 8). zdef S4 (Z.lor S3 (S3 / 2 ^ 8)) ltac:(apply lor_range64; lia).
divfacts S4 (2 ^ 16). zdef S5 (Z.lor S4 (S4 / 2 ^ 16)) ltac:(apply lor_range64; lia).
divfacts S5 (2 ^ 32). zdef S6 (Z.lor S5 (S5 / 2 ^ 32)) ltac:(apply lor_range64; lia).
assert (SM : S6 = 2 ^ (Z.log2 msz + 1) - 1).
{ rewrite <- smear_eq by lia. unfold smear, smear5, smear4, smear3, smear2, smear1. cbv zeta. subst S1 S2 S3 S4 S5 S6. reflexivity. }
zdef y (2 ^ 64 - 1 - S6) ltac:(lia).
pose proof (slpop_ranges y ltac:(lia)) as PR. cbv zeta in PR. unfold C55, C33, C0F in PR.
destruct PR as (PR1 & PR2 & PR3 & PR4 & PR5 & PR6 & PR7 & PR8 & PR9 & PR10).
zdef t2 (Z.land (y / 2 ^ 1) 6148914691236517205) ltac:(lia). rewrite <- Et2 in *.
zdef t3 (y - t2) ltac:(lia). rewrite <- Et3 in *.
zdef t5 (Z.land t3 3689348814741910323) ltac:(lia). rewrite <- Et5 in *.
zdef t6 (Z.land (t3 / 2 ^ 2) 3689348814741910323) ltac:(lia). rewrite <- Et6 in *.
zdef t7 (t5 + t6) ltac:(lia). rewrite <- Et7 in *.
zdef t9 (t7 + t7 / 2 ^ 4) ltac:(lia). rewrite <- Et9 in *.
zdef t10 (Z.land t9 1085102592571150095) ltac:(lia). rewrite <- Et10 in *.
zdef t11 ((t10 * 72340172838076673) mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia).
assert (SL : t11 / 2 ^ 56 = 63 - Z.log2 msz).
{ rewrite <- (slpop_tab (Z.log2 msz)) by lia. rewrite <- SM. unfold slpop, C55, C33, C0F, C01. cbv zeta. subst. reflexivity. }
eexists. split; [|split; [|split]].
- stepn (ltac:(oF' 0x567cc%Z)) (ltac:(oD' 0x567cc%Z)). rwH. rewrite art_zb_srli by lia.
zstep (ltac:(oF' 0x567d0%Z)) (ltac:(oD' 0x567d0%Z)). zstep (ltac:(oF' 0x567d4%Z)) (ltac:(oD' 0x567d4%Z)). zstep (ltac:(oF' 0x567d8%Z)) (ltac:(oD' 0x567d8%Z)).
stepn (ltac:(oF' 0x567dc%Z)) (ltac:(oD' 0x567dc%Z)). rwH. rewrite art_zb_or by lia. rewrite <- ES1.
zstep (ltac:(oF' 0x567e0%Z)) (ltac:(oD' 0x567e0%Z)). zstep (ltac:(oF' 0x567e4%Z)) (ltac:(oD' 0x567e4%Z)). zstep (ltac:(oF' 0x567e8%Z)) (ltac:(oD' 0x567e8%Z)).
stepn (ltac:(oF' 0x567ec%Z)) (ltac:(oD' 0x567ec%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x567f0%Z)) (ltac:(oD' 0x567f0%Z)). rwH. rewrite art_zb_or by lia. rewrite <- ES2.
zstep (ltac:(oF' 0x567f4%Z)) (ltac:(oD' 0x567f4%Z)). zstep (ltac:(oF' 0x567f8%Z)) (ltac:(oD' 0x567f8%Z)). zstep (ltac:(oF' 0x567fc%Z)) (ltac:(oD' 0x567fc%Z)). zstep (ltac:(oF' 0x56800%Z)) (ltac:(oD' 0x56800%Z)). zstep (ltac:(oF' 0x56804%Z)) (ltac:(oD' 0x56804%Z)). zstep (ltac:(oF' 0x56808%Z)) (ltac:(oD' 0x56808%Z)).
stepn (ltac:(oF' 0x5680c%Z)) (ltac:(oD' 0x5680c%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x56810%Z)) (ltac:(oD' 0x56810%Z)). rwH. rewrite art_zb_or by lia. rewrite <- ES3.
stepn (ltac:(oF' 0x56814%Z)) (ltac:(oD' 0x56814%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x56818%Z)) (ltac:(oD' 0x56818%Z)). rwH. rewrite art_zb_or by lia. rewrite <- ES4.
stepn (ltac:(oF' 0x5681c%Z)) (ltac:(oD' 0x5681c%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x56820%Z)) (ltac:(oD' 0x56820%Z)). rwH. rewrite art_zb_or by lia. rewrite <- ES5.
stepn (ltac:(oF' 0x56824%Z)) (ltac:(oD' 0x56824%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x56828%Z)) (ltac:(oD' 0x56828%Z)). rwH. rewrite art_zb_or by lia. rewrite <- ES6.
stepn (ltac:(oF' 0x5682c%Z)) (ltac:(oD' 0x5682c%Z)). rwH. rewrite art_zb_xori_m1 by lia. rewrite <- Ey.
stepn (ltac:(oF' 0x56830%Z)) (ltac:(oD' 0x56830%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x56834%Z)) (ltac:(oD' 0x56834%Z)). rwH. rewrite art_zb_and by lia. rewrite <- Et2.
zstep (ltac:(oF' 0x56838%Z)) (ltac:(oD' 0x56838%Z)).
stepn (ltac:(oF' 0x5683c%Z)) (ltac:(oD' 0x5683c%Z)). rwH. rewrite art_zb_sub. rewrite <- Et3.
stepn (ltac:(oF' 0x56840%Z)) (ltac:(oD' 0x56840%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x56844%Z)) (ltac:(oD' 0x56844%Z)). rwH. rewrite art_zb_and by lia. rewrite <- Et5.
stepn (ltac:(oF' 0x56848%Z)) (ltac:(oD' 0x56848%Z)). rwH. rewrite art_zb_and by lia. rewrite <- Et6.
zld (ltac:(oF' 0x5684c%Z)) (ltac:(oD' 0x5684c%Z)) (sec + 48) C48.
zstep (ltac:(oF' 0x56850%Z)) (ltac:(oD' 0x56850%Z)).
stepn (ltac:(oF' 0x56854%Z)) (ltac:(oD' 0x56854%Z)). rwH. rewrite art_zb_add. rewrite <- Et7.
stepn (ltac:(oF' 0x56858%Z)) (ltac:(oD' 0x56858%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x5685c%Z)) (ltac:(oD' 0x5685c%Z)). rwH. rewrite art_zb_add. rewrite <- Et9.
zstep (ltac:(oF' 0x56860%Z)) (ltac:(oD' 0x56860%Z)).
stepn (ltac:(oF' 0x56864%Z)) (ltac:(oD' 0x56864%Z)). rwH. rewrite art_zb_and by lia. rewrite <- Et10.
zstep (ltac:(oF' 0x56868%Z)) (ltac:(oD' 0x56868%Z)).
stepn (ltac:(oF' 0x5686c%Z)) (ltac:(oD' 0x5686c%Z)). rwH. rewrite art_zb_mul.
match goal with |- context [Z_to_bv 64 (t10 * ?c)] =>
replace (Z_to_bv 64 (t10 * c) : word) with (Z_to_bv 64 ((t10 * c) mod 2 ^ 64) : word) by (apply art_zb_eq; rewrite Z.mod_mod by lia; reflexivity) end.
rewrite <- Et11.
stepn (ltac:(oF' 0x56870%Z)) (ltac:(oD' 0x56870%Z)). rwH. rewrite art_zb_srli by lia. rewrite SL.
apply mst_refl.
- kept_solve. - kept_solve.
- intros rg N11 N12 N14 N15 N16 N19. kept_solve.
Qed.
End SE.
Definition sec_mx (mx cur msz : Z) : Z := if (cur + msz) mod 2 ^ 64 <? mx then mx else (cur + msz) mod 2 ^ 64.
Definition sec_tail_mem (M : word -> option byte) (sec stat r msz nch pab na cur mx lg bsl st16 st24 : Z) : word -> option byte :=
Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 8 (Wn 8 M
(r + 24) nch) (pab + 8 * nch) r) (sec + 56) (nch + 1)) (sec + 64) 0) (sec + 72) (na + 1)) (sec + 88) (cur + msz)) (sec + 96) (sec_mx mx cur msz))
(sec + 104 + 8 * lg) (bsl + 1)) (stat + 16) (st16 + msz)) (stat + 24) (st24 + msz)) (sec + 616) 0.
Section SE.
Local Abbreviation SEC_T_sec_tail_fn := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "\?&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1rL(R;+2(2%33A21%6251&R<&Q>r>+S0%3221%52F1%>3F71rM+8%>3L1<%A231r=%<2M1%E3M31rN+9%E3Q31C%H231r?%C2Q41%L3Q431rO+:%L3Q:1J%O231&Q6+TP0%221I%L2Q=1%Q53Q=51rQ0+=%Q53QC1Q3%Q8231%Q:3QB1FrQ1+B%Q:3QH1Q8%Q=231%Q?3QG1DrQ2+C%Q?3QM1Q=%QB231+QOr:%Q=221%Q?2R01%QH3R051rQ3+E%QH3R61QF%QK231rB%QF2R71%QO3R731&E%11F&Q8+VbTP0rG+^@%QM221%5241&Q:rH&Q=+Q?%22R81%5241+<%52R;1rE%?221%@2Q@>%QB2:?%<218rI%D2C1+RPP0%F21RF+c@%QI2R;1%I21RI+R0%QL2R>1%F21K&Q;%12R:R@z%S23S321'3%Q223S2+D%L2S21%O2S51%5241%Q72Q6S7&Q<%12RKRE%R;2RM1%R<21RM%Q621Q2%Q=2>S0%Q62S<D%Q92RK1%Q@2ARL%Q;2RF3%QB2CRG%B212%QD2RIR2%D231%Q@2RB8%QG2HRC%QB2R?:%QI2JR@%QD2R<<&ArQ:rQ;%F2S@1%S0231rQ=+Q0%743SD21rQ<%L2SF1%S6281rQA%T021R4%=43SJ1R5rQ?rQB%T421R8%A43;1R9&B&Q5rR0%SA26T2u8%554321BrR1rQC+R8%SG221%:59416GrR2rQD+RH%SL221%?5>41;LrR3rQE%T021TF%C5B31?Q0rR4rQF+S8%T5221%QM2TGQ5%T7221%J5I61FQ4rR5+@%T;281%N5M31JQ8rR6rQG+H%T@221%Q35Q241OQ=rR7rQJ%U<21U5&R>%12V0=%Q95Q853Q51rR8rQK%UB21@%Q=5Q<31Q95rR9rQL%UF21?%QA5Q@31Q=9rR:rQM%UJ21R0%QE5QD31QA=rR;rQN+Q8%UO221%QJ5QI41QFBrR<rQO+Q@%V4221%QO5QN41QKGrR=+QH%V82R01%R35R231QOKrR>%V;2QOSH%R65R521R2NrR?%V>2QMR0%R95R821R5Q1rR@+R@%VB2QL1%R=5R<31R9Q5rRA%VE2QKR2%R@5R?21R<Q8&CrRB%V12R8QB%34RC21VCrRC%SK2VER@%V52RE1%74RG31VGrRD%94RI1QKT@rRE%V:2QMR0%<4RL21R1'D&Q2vQDrRG+ZjSH%W?3WK1W=/01WKrRF%756521;&Q3+1%WE3X31WC%3391A%WB2X3QM%532WE1%631W;H%731W5L+;%WL3X:1WJ%VO2R=RE%WI2X:1%<3531%X03X>UEWN&M%13SDS@RK%WN2X?1%A3541%W72R2A%X12XB1%D33W21+>%X93XG1X7%W<2SCF%X62XG1%I3531+?%X>3XL1X<%X:2XKSM%M3421%XA3XOS9X?%WD2SBN%X>2XO1%Q13431%Q231W;QK%Q331W7R0%XG3Y5UEXE%Q5321R5%Q631W1R9+F%XK3Y91XI%Q9331R@+G%XN3Y<1XL%Q<331RH%Y03Y>SCXN%Q>321RO+I%Y33YA1Y1%QA331S6&Q0%1>QES@SFSKSOT6T:T?TDTHRNS3S7S;%QL5QK3R21R0%QN3TKQF1p0R01p0R41p0R71p0R<1p0RA1p0RE1p0RJ1p0RN1p0S21p0S71p0S=1p0SC1p0SH1p0SM1p0T21p0T91p0T?1p0TD1p0TL1p0U11p0U71p0U=1p0UD1p0UI1p0V01p0V91p0V;1p0V=1p0V?1p0VA1p0VF1p0VD1p0VG1p0VJ1p0VL1p0VN1p0W11p0W31p0W91p0W;1p0WB1p0WG1p0WK1p0WO1p0X21p0X51p0X81p0X:1p0X?1p0XF1p0XM1p0Y01p0Y81p0YB1p0YH1p0YN1p0Z81p0Z@1p0ZH1pTD[81pTB[91pS4[:1pS>[;1pSB[<1pS8[=1pSF[>1pSL[?1pSH[@1pS@[A1pT2[B1pTF[C1pT@[D1pT>[E1pUJ[M1pUH[N1pUF[O1pUD\01pUB\11pU@\21pU>\31pU<\41pUN\51pUL\61pU:\71pT<\21pJ\31pT6\91")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 2%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 3%nat 0%nat).
Variable x8 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 4%nat 0%nat).
Variable x9 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 5%nat 0%nat).
Variable x18 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 6%nat 0%nat).
Variable x19 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 7%nat 0%nat).
Variable x20 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 8%nat 0%nat).
Variable x21 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 9%nat 0%nat).
Variable x22 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 10%nat 0%nat).
Variable x23 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 11%nat 0%nat).
Variable x24 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 12%nat 0%nat).
Variable x25 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 13%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 14%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 15%nat 0%nat).
Variable stat : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 16%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 17%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 18%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 19%nat 0%nat).
Variable pab : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 20%nat 0%nat).
Variable na : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 21%nat 0%nat).
Variable cur : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 22%nat 0%nat).
Variable mx : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 23%nat 0%nat).
Variable lg : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 24%nat 0%nat).
Variable bsl : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 25%nat 0%nat).
Variable st16 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 26%nat 0%nat).
Variable st24 : ltac:(sec_ty2 constr:(SEC_T_sec_tail_fn) 27%nat 0%nat).
Lemma sec_tail_fn : ltac:(sec_stmt2 constr:(SEC_T_sec_tail_fn) 28%nat 0%nat).
Proof using Type regs M rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat r msz nch pab na cur mx lg bsl st16 st24.
intros
H2 H8 H9 H10 H13 H18 H19 H21 Hret Hs Hs' Hm Hr Hrm Hri Hsec Hss Hst Hst8 Hnch Hpi Hpab' Hna Hna' Hcur Hcur' Hmx Hlg Hbsl Hbsl' H16 H16' H24 H24'
A1 A2 A3 Cpab Cna Ccur Cmx Cbsl C16 C24 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 W1 W2 W3 W4.
unfold sec_tail_mem.
assert (M16 : (stat + 16) mod 8 = 0) by (rewrite Z.add_mod, Hst8 by lia; reflexivity).
assert (M24 : (stat + 24) mod 8 = 0) by (rewrite Z.add_mod, Hst8 by lia; reflexivity).
zld (ltac:(oF' 0x56878%Z)) (ltac:(oD' 0x56878%Z)) (sec + 8) Cpab.
stepn (ltac:(oF' 0x5687c%Z)) (ltac:(oD' 0x5687c%Z)); rwH; unfold v_xori; rewrite (art_u_lit (63 - lg)) by lia; change (bv_wrap 64 63) with 63; rewrite lxor_63 by lia.
replace (63 - (63 - lg)) with lg by lia.
zsd (ltac:(oF' 0x56880%Z)) (ltac:(oD' 0x56880%Z)) (r + 24) nch ltac:(rewok W1).
zstep (ltac:(oF' 0x56884%Z)) (ltac:(oD' 0x56884%Z)); zstep (ltac:(oF' 0x56888%Z)) (ltac:(oD' 0x56888%Z)).
zsd (ltac:(oF' 0x5688c%Z)) (ltac:(oD' 0x5688c%Z)) (pab + 8 * nch) r ltac:(rewok W2).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cna' : cellA X (sec + 72) 8 na) by zcell; assert (Ccur' : cellA X (sec + 88) 8 cur) by zcell; assert (Cmx' : cellA X (sec + 96) 8 mx) by zcell end.
zld (ltac:(oF' 0x56890%Z)) (ltac:(oD' 0x56890%Z)) (sec + 72) Cna'.
zld (ltac:(oF' 0x56894%Z)) (ltac:(oD' 0x56894%Z)) (sec + 88) Ccur'.
zstep (ltac:(oF' 0x56898%Z)) (ltac:(oD' 0x56898%Z)).
zld (ltac:(oF' 0x5689c%Z)) (ltac:(oD' 0x5689c%Z)) (sec + 96) Cmx'.
zstep (ltac:(oF' 0x568a0%Z)) (ltac:(oD' 0x568a0%Z)); zstep (ltac:(oF' 0x568a4%Z)) (ltac:(oD' 0x568a4%Z)).
zsd (ltac:(oF' 0x568a8%Z)) (ltac:(oD' 0x568a8%Z)) (sec + 56) (nch + 1) ltac:(rewok W3).
zsb (ltac:(oF' 0x568ac%Z)) (ltac:(oD' 0x568ac%Z)) (sec + 64) 0 ltac:(rewok W3).
zsd (ltac:(oF' 0x568b0%Z)) (ltac:(oD' 0x568b0%Z)) (sec + 72) (na + 1) ltac:(rewok W3).
zsd (ltac:(oF' 0x568b4%Z)) (ltac:(oD' 0x568b4%Z)) (sec + 88) (cur + msz) ltac:(rewok W3).
match goal with |- msteps _ ?S _ =>
assert (BR : msteps ASEGS S ltac:(match S with mkst ?R _ ?X _ => exact (mkst (regupd R 12 (Z_to_bv 64 (sec_mx mx cur msz))) (0x568c0 : word) X rom) end)) end.
{ pose proof (Z.mod_pos_bound (cur + msz) (2 ^ 64) ltac:(lia)) as Hcm.
unfold sec_mx. rewrite <- (art_zb_mod64 (cur + msz)).
destruct (Z.lt_ge_cases ((cur + msz) mod 2 ^ 64) mx) as [LT|GE].
- replace ((cur + msz) mod 2 ^ 64 <? mx) with true by (symmetry; apply Z.ltb_lt; lia). zbtk (ltac:(oF' 0x568b8%Z)) (ltac:(oD' 0x568b8%Z)). zret.
- replace ((cur + msz) mod 2 ^ 64 <? mx) with false by (symmetry; apply Z.ltb_ge; lia). zbft (ltac:(oF' 0x568b8%Z)) (ltac:(oD' 0x568b8%Z)). zstep (ltac:(oF' 0x568bc%Z)) (ltac:(oD' 0x568bc%Z)). zret. }
eapply msteps_trans; [exact BR|]. clear BR.
zstep (ltac:(oF' 0x568c0%Z)) (ltac:(oD' 0x568c0%Z)); zstep (ltac:(oF' 0x568c4%Z)) (ltac:(oD' 0x568c4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cbsl' : cellA X (sec + 104 + 8 * lg) 8 bsl) by zcell end.
zld (ltac:(oF' 0x568c8%Z)) (ltac:(oD' 0x568c8%Z)) (sec + 104 + 8 * lg) Cbsl'.
zstep (ltac:(oF' 0x568cc%Z)) (ltac:(oD' 0x568cc%Z)).
zsd (ltac:(oF' 0x568d0%Z)) (ltac:(oD' 0x568d0%Z)) (sec + 96) (sec_mx mx cur msz) ltac:(rewok W3).
zsd (ltac:(oF' 0x568d4%Z)) (ltac:(oD' 0x568d4%Z)) (sec + 104 + 8 * lg) (bsl + 1) ltac:(rewok W3).
zstep (ltac:(oF' 0x568d8%Z)) (ltac:(oD' 0x568d8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (stat + 16) 8 st16) by zcell; assert (C24' : cellA X (stat + 24) 8 st24) by zcell end.
zamoadd_d (ltac:(oF' 0x568dc%Z)) (ltac:(oD' 0x568dc%Z)) (stat + 16) st16 msz C16' ltac:(rewok W4).
zstep (ltac:(oF' 0x568e0%Z)) (ltac:(oD' 0x568e0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24'' : cellA X (stat + 24) 8 st24) by zcell end.
zamoadd_d (ltac:(oF' 0x568e4%Z)) (ltac:(oD' 0x568e4%Z)) (stat + 24) st24 msz C24'' ltac:(rewok W4).
stepfence (ltac:(oF' 0x568e8%Z)) (ltac:(oD' 0x568e8%Z)).
zsb (ltac:(oF' 0x568ec%Z)) (ltac:(oD' 0x568ec%Z)) (sec + 616) 0 ltac:(rewok W3).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (L1' : cellA X (s - 8) 8 (U x1)) by zcell; assert (L2' : cellA X (s - 16) 8 (U x8)) by zcell; assert (L3' : cellA X (s - 24) 8 (U x9)) by zcell;
assert (L4' : cellA X (s - 32) 8 (U x18)) by zcell; assert (L5' : cellA X (s - 40) 8 (U x19)) by zcell; assert (L6' : cellA X (s - 48) 8 (U x20)) by zcell;
assert (L7' : cellA X (s - 56) 8 (U x21)) by zcell; assert (L8' : cellA X (s - 64) 8 (U x22)) by zcell; assert (L9' : cellA X (s - 72) 8 (U x23)) by zcell;
assert (L10' : cellA X (s - 80) 8 (U x24)) by zcell; assert (L11' : cellA X (s - 88) 8 (U x25)) by zcell end.
zld (ltac:(oF' 0x568f0%Z)) (ltac:(oD' 0x568f0%Z)) (s - 8) L1'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x568f4%Z)) (ltac:(oD' 0x568f4%Z)) (s - 16) L2'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x568f8%Z)) (ltac:(oD' 0x568f8%Z)) (s - 24) L3'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x568fc%Z)) (ltac:(oD' 0x568fc%Z)) (s - 32) L4'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56900%Z)) (ltac:(oD' 0x56900%Z)) (s - 40) L5'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56904%Z)) (ltac:(oD' 0x56904%Z)) (s - 48) L6'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56908%Z)) (ltac:(oD' 0x56908%Z)) (s - 56) L7'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x5690c%Z)) (ltac:(oD' 0x5690c%Z)) (s - 64) L8'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56910%Z)) (ltac:(oD' 0x56910%Z)) (s - 72) L9'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56914%Z)) (ltac:(oD' 0x56914%Z)) (s - 80) L10'; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56918%Z)) (ltac:(oD' 0x56918%Z)) (s - 88) L11'; rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x5691c%Z)) (ltac:(oD' 0x5691c%Z)).
stepret (ltac:(oF' 0x56920%Z)) (ltac:(oD' 0x56920%Z)) x1 ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
Definition sec_b1_mem (M : word -> option byte) (s stat sec msz lg r pab2 nch : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
(s - 104) 0x56a70) (s - 112) stat) (s - 120) sec) (s - 128) msz) (s - 136) lg) (s - 144) (4096 + r)) (s - 192) 50)
(s - 200) 0x8d0cc) (s - 208) 131072) (s - 216) 0) (s - 224) (pab2 + 8 * nch)) (s - 232) 0) (s - 240) 0x1ca7a0) (s - 248) r.
Section SE.
Local Abbreviation SEC_T_sec_b1_fn := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "WN&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1r;(R;+2(2%33A21%6251&R<&Q>r8+S0%3221%52F1%>3F71r<+8%>3L1<%A231r7%<2M1%E3M31r=+9%E3Q31C%H231r9%C2Q41%L3Q431r>+:%L3Q:1J%O231&Q6+TP0r5%3221%M2Q>1%Q63Q>61r?+=%Q63QD1Q4%Q9231%Q32QDQ1%Q<3QD21r@+>%Q<3QJ1Q:%Q?231%QA3QI1FrA+B%QA3QO1Q?%QD231%QF3QN1Q2rB+C%QF3R41QD%QI231%QC2R4Q<%QL3R421rC+E%QL3R:1QJ%QO231r:%QJ2R;1%R33R;31&Q8+VbTP0+^@%QN2E1%4231&Q:&Q=+Q?%22R81%42F1%:2Q<QH%62QB3'3z%>21QE%3214rD%A241+R0%=2RC1%?241%9241+QO%G271%<271+RPP0rG%K221rH+QP0%R1221%J21NrF%Q12D1+D%M2S31%O241%I241%Q62R86&Q<%12RL<%R<2?1+TPP0%R>221%Q721Q4&Q;rI%82S31%RC2D1%421RC%SF3SG1Q5&C&Q5rQ0rN%SB21QE%54431QF&BrQ1+@%RO261u8rJ%65;5321rQ2+QVY`H+QiYm0%:5?3261rQ3%<5A138S7'D&Q2vQDrQ5+ZjSD%T<3TH1T:/01THrQ4%756521:&Q3+1%TB3U01T@+adW8%T?2U01%53;31+V0%TA2F1%TC2U41%934TF1%TE2U6Q?%;32T=1%TG2U8R>%=32T81rM%QG2TBQ8%T2221%TL2U=1%B35T61+;%U43UB1U2%E331;+<%U73UE1U5+3%U42UE1%J3531+QB%U72UH1%M33T71+_oooooooooooO%U:2UK1%Q033T41+?%UB3V01U@%Q3331G+A%UE3V31UC+VN%UB2V31%Q83531%Q931T8H%Q:31T4N%UK3V9RHUI%UG2V8QI%Q=3321rL%UJ2V;1%Q@33T41+a\i8%V23V>1V0/01V>&KrKrO%39QIR6RAR<219Q9R@%R05QO851R3%R23RDQJ1p0R41p0R71p0R<1p0RD1p0RK1p0S21p0S91p0S;1p0SB1p0SG1p0SK1p0SO1p0T61p0T;1p0T=1p0T?1p0TE1p0TK1p0U31p0U:1p0U@1p0UF1p0UM1p0V81p0V@1p0VH1pS@W81pT2W91pSNW:1pSHW;1pS>W<1pTFW=1pT@W>1pT>W?1pT<WA1pJWB1pT6WH1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 3%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 4%nat 0%nat).
Variable stat : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 5%nat 0%nat).
Variable lg : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 6%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 7%nat 0%nat).
Variable pab2 : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 8%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 9%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_sec_b1_fn) 10%nat 0%nat).
Lemma sec_b1_fn : ltac:(sec_stmt2 constr:(SEC_T_sec_b1_fn) 11%nat 0%nat).
Proof using Type regs M rom s sec stat lg nch pab2 r msz.
intros H2 H8 H9 H10 H13 H14 H18 H19 H21 Hs Hs' Hr Hr' Hm Hst Hlg Hsec Hsec' Hnch Hpab Hpab' Hal W C16 Cg28 Cpc.
unfold sec_b1_mem.
zbtk (ltac:(oF' 0x56874%Z)) (ltac:(oD' 0x56874%Z)).
zld (ltac:(oF' 0x56a4c%Z)) (ltac:(oD' 0x56a4c%Z)) (sec + 16) C16.
zstep (ltac:(oF' 0x56a50%Z)) (ltac:(oD' 0x56a50%Z)). zstep (ltac:(oF' 0x56a54%Z)) (ltac:(oD' 0x56a54%Z)). zstep (ltac:(oF' 0x56a58%Z)) (ltac:(oD' 0x56a58%Z)).
zstep (ltac:(oF' 0x56a5c%Z)) (ltac:(oD' 0x56a5c%Z)). zstep (ltac:(oF' 0x56a60%Z)) (ltac:(oD' 0x56a60%Z)). zstep (ltac:(oF' 0x56a64%Z)) (ltac:(oD' 0x56a64%Z)). zstep (ltac:(oF' 0x56a68%Z)) (ltac:(oD' 0x56a68%Z)).
stepn (ltac:(oF' 0x56a6c%Z)) (ltac:(oD' 0x56a6c%Z)).
zstep (ltac:(oF' 0x953c0%Z)) (ltac:(oD' 0x953c0%Z)). zstep (ltac:(oF' 0x953c4%Z)) (ltac:(oD' 0x953c4%Z)). zstep (ltac:(oF' 0x953c8%Z)) (ltac:(oD' 0x953c8%Z)).
stepn (ltac:(oF' 0x953cc%Z)) (ltac:(oD' 0x953cc%Z)).
zstep (ltac:(oF' 0x8d030%Z)) (ltac:(oD' 0x8d030%Z)). zstep (ltac:(oF' 0x8d034%Z)) (ltac:(oD' 0x8d034%Z)).
stepn (ltac:(oF' 0x8d038%Z)) (ltac:(oD' 0x8d038%Z)).
zstep (ltac:(oF' 0x8d03c%Z)) (ltac:(oD' 0x8d03c%Z)).
zsd (ltac:(oF' 0x8d040%Z)) (ltac:(oD' 0x8d040%Z)) (s - 104) 0x56a70 ltac:(rewok W).
zsd (ltac:(oF' 0x8d044%Z)) (ltac:(oD' 0x8d044%Z)) (s - 112) stat ltac:(rewok W).
zsd (ltac:(oF' 0x8d048%Z)) (ltac:(oD' 0x8d048%Z)) (s - 120) sec ltac:(rewok W).
zsd (ltac:(oF' 0x8d04c%Z)) (ltac:(oD' 0x8d04c%Z)) (s - 128) msz ltac:(rewok W).
zsd (ltac:(oF' 0x8d050%Z)) (ltac:(oD' 0x8d050%Z)) (s - 136) lg ltac:(rewok W).
zsd (ltac:(oF' 0x8d054%Z)) (ltac:(oD' 0x8d054%Z)) (s - 144) (4096 + r) ltac:(rewok W).
zstep (ltac:(oF' 0x8d058%Z)) (ltac:(oD' 0x8d058%Z)). zstep (ltac:(oF' 0x8d05c%Z)) (ltac:(oD' 0x8d05c%Z)). zstep (ltac:(oF' 0x8d060%Z)) (ltac:(oD' 0x8d060%Z)).
zstep (ltac:(oF' 0x8d064%Z)) (ltac:(oD' 0x8d064%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0x132618 8 0x1ca7a0) by zcell; assert (Cpc' : cellA X 0x1ca7a0 8 4096) by zcell end.
zld (ltac:(oF' 0x8d068%Z)) (ltac:(oD' 0x8d068%Z)) 0x132618 Cg28'. zld (ltac:(oF' 0x8d06c%Z)) (ltac:(oD' 0x8d06c%Z)) 0x1ca7a0 Cpc'.
zstep (ltac:(oF' 0x8d070%Z)) (ltac:(oD' 0x8d070%Z)).
zbtk (ltac:(oF' 0x8d074%Z)) (ltac:(oD' 0x8d074%Z)).
zstep (ltac:(oF' 0x8d084%Z)) (ltac:(oD' 0x8d084%Z)). zstep (ltac:(oF' 0x8d088%Z)) (ltac:(oD' 0x8d088%Z)).
zbft (ltac:(oF' 0x8d08c%Z)) (ltac:(oD' 0x8d08c%Z)).
zstep (ltac:(oF' 0x8d090%Z)) (ltac:(oD' 0x8d090%Z)). zstep (ltac:(oF' 0x8d094%Z)) (ltac:(oD' 0x8d094%Z)). zstep (ltac:(oF' 0x8d098%Z)) (ltac:(oD' 0x8d098%Z)).
zstep (ltac:(oF' 0x8d09c%Z)) (ltac:(oD' 0x8d09c%Z)).
zbtk (ltac:(oF' 0x8d0a0%Z)) (ltac:(oD' 0x8d0a0%Z)).
stepn (ltac:(oF' 0x8d0b0%Z)) (ltac:(oD' 0x8d0b0%Z)). rwH. rewrite art_zb_and by lia.
change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
replace (nch * 2 ^ 3 + pab2) with (pab2 + 8 * nch) by lia. rewrite Hal, Z.sub_0_r.
zstep (ltac:(oF' 0x8d0b4%Z)) (ltac:(oD' 0x8d0b4%Z)).
zsw (ltac:(oF' 0x8d0b8%Z)) (ltac:(oD' 0x8d0b8%Z)) (s - 192) 50 ltac:(rewok W).
zstep (ltac:(oF' 0x8d0bc%Z)) (ltac:(oD' 0x8d0bc%Z)). zstep (ltac:(oF' 0x8d0c0%Z)) (ltac:(oD' 0x8d0c0%Z)). zstep (ltac:(oF' 0x8d0c4%Z)) (ltac:(oD' 0x8d0c4%Z)).
stepn (ltac:(oF' 0x8d0c8%Z)) (ltac:(oD' 0x8d0c8%Z)).
zstep (ltac:(oF' 0x8d6d0%Z)) (ltac:(oD' 0x8d6d0%Z)).
zsd (ltac:(oF' 0x8d6d4%Z)) (ltac:(oD' 0x8d6d4%Z)) (s - 200) 0x8d0cc ltac:(rewok W).
zsd (ltac:(oF' 0x8d6d8%Z)) (ltac:(oD' 0x8d6d8%Z)) (s - 208) 131072 ltac:(rewok W).
zsd (ltac:(oF' 0x8d6dc%Z)) (ltac:(oD' 0x8d6dc%Z)) (s - 216) 0 ltac:(rewok W).
zsd (ltac:(oF' 0x8d6e0%Z)) (ltac:(oD' 0x8d6e0%Z)) (s - 224) (pab2 + 8 * nch) ltac:(rewok W).
zsd (ltac:(oF' 0x8d6e4%Z)) (ltac:(oD' 0x8d6e4%Z)) (s - 232) 0 ltac:(rewok W).
zsd (ltac:(oF' 0x8d6e8%Z)) (ltac:(oD' 0x8d6e8%Z)) (s - 240) 0x1ca7a0 ltac:(rewok W).
zsd (ltac:(oF' 0x8d6ec%Z)) (ltac:(oD' 0x8d6ec%Z)) (s - 248) r ltac:(rewok W).
zstep (ltac:(oF' 0x8d6f0%Z)) (ltac:(oD' 0x8d6f0%Z)).
zstep (ltac:(oF' 0x8d6f4%Z)) (ltac:(oD' 0x8d6f4%Z)).
zbtk (ltac:(oF' 0x8d6f8%Z)) (ltac:(oD' 0x8d6f8%Z)).
stepn (ltac:(oF' 0x8d820%Z)) (ltac:(oD' 0x8d820%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (R1 : cellA X (s - 200) 8 0x8d0cc) by zcell; assert (R2 : cellA X (s - 208) 8 131072) by zcell;
assert (R3 : cellA X (s - 216) 8 0) by zcell; assert (R4 : cellA X (s - 224) 8 (pab2 + 8 * nch)) by zcell;
assert (R5 : cellA X (s - 232) 8 0) by zcell; assert (R6 : cellA X (s - 240) 8 0x1ca7a0) by zcell;
assert (R7 : cellA X (s - 248) 8 r) by zcell; assert (R8 : cellA X (s - 192) 4 50) by zcell end.
zld (ltac:(oF' 0x8d824%Z)) (ltac:(oD' 0x8d824%Z)) (s - 200) R1. zld (ltac:(oF' 0x8d828%Z)) (ltac:(oD' 0x8d828%Z)) (s - 208) R2. zld (ltac:(oF' 0x8d82c%Z)) (ltac:(oD' 0x8d82c%Z)) (s - 216) R3. zld (ltac:(oF' 0x8d830%Z)) (ltac:(oD' 0x8d830%Z)) (s - 224) R4.
zld (ltac:(oF' 0x8d834%Z)) (ltac:(oD' 0x8d834%Z)) (s - 232) R5. zld (ltac:(oF' 0x8d838%Z)) (ltac:(oD' 0x8d838%Z)) (s - 240) R6. zld (ltac:(oF' 0x8d83c%Z)) (ltac:(oD' 0x8d83c%Z)) (s - 248) R7.
zstep (ltac:(oF' 0x8d840%Z)) (ltac:(oD' 0x8d840%Z)).
stepret (ltac:(oF' 0x8d844%Z)) (ltac:(oD' 0x8d844%Z)) (Z_to_bv 64 0x8d0cc : word) ltac:(rwH; reflexivity).
zlw (ltac:(oF' 0x8d0cc%Z)) (ltac:(oD' 0x8d0cc%Z)) (s - 192) R8.
zstep (ltac:(oF' 0x8d0d0%Z)) (ltac:(oD' 0x8d0d0%Z)). zstep (ltac:(oF' 0x8d0d4%Z)) (ltac:(oD' 0x8d0d4%Z)). zstep (ltac:(oF' 0x8d0d8%Z)) (ltac:(oD' 0x8d0d8%Z)). zstep (ltac:(oF' 0x8d0dc%Z)) (ltac:(oD' 0x8d0dc%Z)). zstep (ltac:(oF' 0x8d0e0%Z)) (ltac:(oD' 0x8d0e0%Z)).
stepn (ltac:(oF' 0x8d0e4%Z)) (ltac:(oD' 0x8d0e4%Z)).
zstep (ltac:(oF' 0x8b324%Z)) (ltac:(oD' 0x8b324%Z)).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_sec_b2_fn := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "X8&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1r=(R;+1(2%33A21%6251&R<+adW8%22C1%;3C41r>+2%;3I19%>231&Q>r;+V0%3221%<2M1%E3M61r?+8%E3Q31C%H231+TPP0%C2Q41%L3Q431r@+:%L3Q:1J%O231r5%J2Q;1%Q33Q;31&Q8+VbTP0+^@%G2K1%4231&Q:&Q=+Q?%22O1%42G1+TP0r9%<221r:%9216'3z%A21O%3219%C23Q6+R0%?2Q<1+SoO%Q;221%C2Q;1%:261+RPP0rC%L221&Q6rD+QP0%3221%L21Q0%Q2284rE%721@%Q021Q4%Q62F;+D%Q22QO1%Q42>1%K241+Q8%Q62R31%Q82B1%O281rF%Q@2Q01+QO%QB231%Q4231rB%QE2K1+`0%J2L1%QC21QG&C&Q5rOrM%RA21QK%54431QLrQ0+c@%847251&BrQ1+S8%RI2:1u8+Zjc@%65>5321rQ2+S@%RO2<1rN%;5C4271rQ3+SH%S42=1%?5G31;BrQ4+T0%S82;1%C5K31?JrQ5+T8%S<2:1%G5O31CNrQ6+T@%S@2:1%R02RCQ1%L5Q442H1rQ7+QVYa8rL%Q05Q832L1rQ8%R72Q89%Q35Q;21ORErQ9+Q@%R;2>1%Q75Q?31Q3Q6rQ:+QH%R?2=1%Q;5QC31Q7O'D&Q2vQDrQ<+a\i<%TD3U01TB/01U0rQ;%756521<&Q3%TD2U5QA%238TG1+S0%T?2E1%TH2U91%634TC1%TJ2U;O%832T;1+9%U23U@1U0%TN2U?O%<3421%S72SJQK%U12UB1%?33T;1+;%U93UG1U7+`P0%S=2QL1%U72UH1%E3641+<%U?3UM1U=%U;2UL6%I3421+=%UC3V11UA%U?2V0R1%M3421+B%UG3V51UE%UC2V4QM%Q13421+C%UK3V91UI%UG2V8R5%Q53421%UN3V<SFUL%Q7321I+ZjSH%V13V=1UO/01V=&@u4+TD%UI2QO1+_oooooneZeZe:%544QB21%T;2R5R1%74S321O%QK5QJ<91R0%QM3SAQE1p0QO1p0R41p0R91p0R=1p0RB1p0RH1p0RM1p0S21p0S71p0S=1p0SE1p0SI1p0T01p0T41p0T71p0T=1p0TB1p0TH1p0TL1p0TN1p0U41p0U81p0U@1p0UE1p0UH1p0UL1p0V21p0V81p0V@1p0VH1p0W31pFW@1pT0WA1pT2WB1pSJWC1pSHWD1pS>WE1pS@WF1pTFWG1pT@WH1pT>WI1pT<WK1pJWL1pT6X21")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 3%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 4%nat 0%nat).
Variable stat : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 5%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 6%nat 0%nat).
Variable lg : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 7%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 8%nat 0%nat).
Variable nres : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 9%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 10%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 11%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_sec_b2_fn) 12%nat 0%nat).
Lemma sec_b2_fn : ltac:(sec_stmt2 constr:(SEC_T_sec_b2_fn) 13%nat 0%nat).
Proof using Type regs M rom s sec stat msz lg nch nres r q F.
intros H1 H2 H8 H10 Hs Hs' Hr Hr' Hm Hq Hsec Hsec' Hst Hst' Hnch Hnres Hlg HF HF' W W5
C104 C112 C120 C128 C136 C144 C38 C144' Cnres Cnch.
stepret (ltac:(oF' 0x8b32c%Z)) (ltac:(oD' 0x8b32c%Z)) (Z_to_bv 64 0x8d0e8 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8d0e8%Z)) (ltac:(oD' 0x8d0e8%Z)).
zstep (ltac:(oF' 0x8d0ec%Z)) (ltac:(oD' 0x8d0ec%Z)).
stepn (ltac:(oF' 0x8d0f0%Z)) (ltac:(oD' 0x8d0f0%Z)).
zstep (ltac:(oF' 0x8b304%Z)) (ltac:(oD' 0x8b304%Z)). zstep (ltac:(oF' 0x8b308%Z)) (ltac:(oD' 0x8b308%Z)).
zbtk (ltac:(oF' 0x8b30c%Z)) (ltac:(oD' 0x8b30c%Z)).
zstep (ltac:(oF' 0x8b31c%Z)) (ltac:(oD' 0x8b31c%Z)).
stepret (ltac:(oF' 0x8b320%Z)) (ltac:(oD' 0x8b320%Z)) (Z_to_bv 64 0x8d0f4 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8d0f4%Z)) (ltac:(oD' 0x8d0f4%Z)). zstep (ltac:(oF' 0x8d0f8%Z)) (ltac:(oD' 0x8d0f8%Z)).
zsw (ltac:(oF' 0x8d0fc%Z)) (ltac:(oD' 0x8d0fc%Z)) (s - 148) 18446744072277895850 ltac:(rewok W).
zstep (ltac:(oF' 0x8d100%Z)) (ltac:(oD' 0x8d100%Z)). zstep (ltac:(oF' 0x8d104%Z)) (ltac:(oD' 0x8d104%Z)).
stepn (ltac:(oF' 0x8d108%Z)) (ltac:(oD' 0x8d108%Z)).
zstep (ltac:(oF' 0x8b304%Z)) (ltac:(oD' 0x8b304%Z)). zstep (ltac:(oF' 0x8b308%Z)) (ltac:(oD' 0x8b308%Z)).
zbtk (ltac:(oF' 0x8b30c%Z)) (ltac:(oD' 0x8b30c%Z)).
zstep (ltac:(oF' 0x8b31c%Z)) (ltac:(oD' 0x8b31c%Z)).
stepret (ltac:(oF' 0x8b320%Z)) (ltac:(oD' 0x8b320%Z)) (Z_to_bv 64 0x8d10c : word) ltac:(rwH; reflexivity).
zbft (ltac:(oF' 0x8d10c%Z)) (ltac:(oD' 0x8d10c%Z)).
zstep (ltac:(oF' 0x8d110%Z)) (ltac:(oD' 0x8d110%Z)).
stepn (ltac:(oF' 0x8d114%Z)) (ltac:(oD' 0x8d114%Z)).
zstep (ltac:(oF' 0x871ec%Z)) (ltac:(oD' 0x871ec%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0x132628 8 F) by zcell; assert (C144'' : cellA X (F + 144) 8 0) by zcell end.
zld (ltac:(oF' 0x871f0%Z)) (ltac:(oD' 0x871f0%Z)) 0x132628 C38'. zld (ltac:(oF' 0x871f4%Z)) (ltac:(oD' 0x871f4%Z)) (F + 144) C144''.
zbtk (ltac:(oF' 0x871f8%Z)) (ltac:(oD' 0x871f8%Z)).
stepret (ltac:(oF' 0x87214%Z)) (ltac:(oD' 0x87214%Z)) (Z_to_bv 64 0x8d118 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8d118%Z)) (ltac:(oD' 0x8d118%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (R1 : cellA X (s - 104) 8 0x56a70) by zcell; assert (R2 : cellA X (s - 112) 8 stat) by zcell; assert (R3 : cellA X (s - 120) 8 sec) by zcell;
assert (R4 : cellA X (s - 128) 8 msz) by zcell; assert (R5 : cellA X (s - 136) 8 lg) by zcell; assert (R6 : cellA X (s - 144) 8 (4096 + r)) by zcell;
assert (Cnres' : cellA X (sec + 48) 8 nres) by zcell; assert (Cnch' : cellA X (sec + 56) 8 nch) by zcell end.
zld (ltac:(oF' 0x8d11c%Z)) (ltac:(oD' 0x8d11c%Z)) (s - 104) R1. zld (ltac:(oF' 0x8d120%Z)) (ltac:(oD' 0x8d120%Z)) (s - 112) R2. zld (ltac:(oF' 0x8d124%Z)) (ltac:(oD' 0x8d124%Z)) (s - 120) R3. zld (ltac:(oF' 0x8d128%Z)) (ltac:(oD' 0x8d128%Z)) (s - 128) R4.
zld (ltac:(oF' 0x8d12c%Z)) (ltac:(oD' 0x8d12c%Z)) (s - 136) R5. zld (ltac:(oF' 0x8d130%Z)) (ltac:(oD' 0x8d130%Z)) (s - 144) R6.
zstep (ltac:(oF' 0x8d134%Z)) (ltac:(oD' 0x8d134%Z)).
stepret (ltac:(oF' 0x8d138%Z)) (ltac:(oD' 0x8d138%Z)) (Z_to_bv 64 0x56a70 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x56a70%Z)) (ltac:(oD' 0x56a70%Z)).
zld (ltac:(oF' 0x56a74%Z)) (ltac:(oD' 0x56a74%Z)) (sec + 48) Cnres'. zld (ltac:(oF' 0x56a78%Z)) (ltac:(oD' 0x56a78%Z)) (sec + 56) Cnch'.
zstep (ltac:(oF' 0x56a7c%Z)) (ltac:(oD' 0x56a7c%Z)). zstep (ltac:(oF' 0x56a80%Z)) (ltac:(oD' 0x56a80%Z)).
zsd (ltac:(oF' 0x56a84%Z)) (ltac:(oD' 0x56a84%Z)) (sec + 48) (nres + 16384) ltac:(rewok W5).
stepn (ltac:(oF' 0x56a88%Z)) (ltac:(oD' 0x56a88%Z)).
zret.
Qed.
End SE.
Definition sec_pm1 (M1 : word -> option byte) (s stat sec msz n r : Z) : word -> option byte :=
Wf (art_poison_frame (Wn 4 M1 (s - 136) 18446744072277895850) (s - 96) 0x56728 stat sec msz n r (4096 + r + n)) (SB + r / 8) (Z.to_nat (4096 / 8)) 250.
Definition sec_pm2 (M1 : word -> option byte) (s stat sec msz n r : Z) : word -> option byte :=
Wf (art_poison_frame (sec_pm1 M1 s stat sec msz n r) (s - 96) 0x56738 stat sec msz n r (4096 + r + n)) (SB + (4096 + r + n) / 8) (Z.to_nat ((msz - 4096 - n) / 8)) 250.
Definition sec_hm (M1 : word -> option byte) (s stat sec msz n r t C D : Z) : word -> option byte :=
Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (sec_pm2 M1 s stat sec msz n r) (s - 104) 0x5673c) (s - 120) 0x82164)
(t + 2800 + 72) (C + 1)) (t + 2800 + 80) (D + msz)) r r) (r + 8) msz) (r + 16) n) (sec + 616) 1.
Definition sec_postA_mem (M1 : word -> option byte) (s stat sec msz n r t C D nch pab na cur mx bsl st16 st24 : Z) : word -> option byte :=
sec_tail_mem (sec_hm M1 s stat sec msz n r t C D) sec stat r msz nch pab na cur mx (Z.log2 msz) bsl st16 st24.
Definition appmem (a n : Z) : Prop := a + n <= SB - 4096 \/ kHighMemBeg <= a.
Section SE.
Local Abbreviation SEC_T_sec_head_run := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "^;&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1rC(R;+1(2%33A21%6251&R<+acSH%22C1%;3C41rD+2%;3I19%>231&Q>rA+T@%3221%<2M1%E3M61rE+4%E3Q31C%H231r;%C2Q41%L3Q431rF+:%L3Q:1J%O231r>%J2Q;1%Q33Q;31rG+C%Q33QA1Q1%Q6231r@%Q12QB1%Q:3QB31rH+E%Q:3QH1Q8%Q=231+8%Q82QI1%QA3QI31rI+H%QA3QO1Q?%QD231+7%Q?2R01%QH3R031&Q8&I+^@%Q<2H1%4231&Q:&Q=+Q?%22QD1%42G1z%;21Q>&Q;%12Q9G%R73R814+<%:2QL1%A21O+TP0%72J1%R=3R>1:&Q6%12M4rJ%H221%I27Q0%>238%RD3RE1ArKrM%9221%J21G+VbTP0rL%Q2221&JrO%2281&ArNrQ0rQ3%RC21Q8%54431Q9+RPP0%Q=214rQ4+QP0%K221%Q<21ArQ5+c@%O221%QE217+R0%Q2251%QC21HrQ7+c8%Q6221%Q@21RN%SF3SG1QC%QB25R8%SH3SI1QE%R02DB+`0%Q=2@1%QN21Q3'7'3rQ1%R72QE1%QC22QF%R921M%5231%R;2Q;5%8221rQ2%QI21QL%R:21R7%Q=2Q7QN+RiH%QM2Q41+@rQ:+Q0%Q@44321%R22Q56rQ@%T221RG%QD4371RHrQ6%R721;+TH%R92Q51%QI43<1S9%S02RF5%RK2T=Q;%RM2Q91%S32RIQ:rQ8%S0214rQ<%R421RErQ=%RD21<rQB%R542SE1FrQ>%RH21@rQH%TH21S=%R:43SJ1S>+RH%TK281%SC2S11rQC%S@21RE%SF2S4<&Q<rQD%22T31%S5261%S621T5%SL21RL&C&Q5rQOrQM%U:21SO%54431T0rR0rQI%84721Q@rR1&G&Q7rQJ%221TD%SF241rQL%521TG%A4@831rR2rQE%SL21R0%E4D31QOrR3%G4F1AS1&BrR4+S8%V1291u8+Zif@%65M5321rR5+S@%V72;1%:5Q1316IrR6+SH%V;2<1%>5Q531:@rR7+T0%V?2:1%B5Q931>HrR8%D5Q;1=@TGrR9+QVYa8%G5Q>21CQ6rR:%TI2OVE%J5QA21FU5&HrR;%211&FrR<%261Q2Q6Q?QBQFrR=%U22QDS6%Q35QJ21OQIrR>+Rj0%U62QE1%Q75QN31Q3QMrR?%U92:T4u4%Q;5R2321UFrR@+QH%U>2=1%Q?5R631Q;R1rRA+Q@%UB2>1%QC5R:31Q?R5%V92UOQJ+D%V52WG1%V72QM1%T8241%V92QOS=%T:261'5'D&Q2vQDrRF+a\i<%X<3XH1X:/01XHrRErRD%8576321r1+ZjSD%XC3XO1XA/01XO&LrRCrRB%3::2M1Q1Q5Q9QJQNR2%A5@851:%C3S6:1%XM2:X@+S0%X@271%XI2Y:1%Y23Y:41%Y22?X;%XL2Y=QG%Y53Y=21%Y33YAWGY1%Y62C1%Y02YAQ:%Y93YA21+9%Y83YF1Y6%Y;2H1%Y52YFC%Y>3YF21%Y>2KX@%W22W5QN%Y92YJ1%YB3YJ31+=%YA3YO1Y?%YD2Q11%Y>2YOS1%YG3YO21+>%YF3Z41YD%YI2Q61%YC2Z4S<%YL3Z421+B%YK3Z91YI%YN2Q;1%YH2Z9R6%Z13Z921%Z12Q>XL+QO&Q9%11R;%YF231%YO2Z@1%Z83Z@61%Z82QEXL%Z22ZCRH%Z;3ZC21+3%Z:3ZH1Z8%Z=2QJ1%Z>2R22%Z@3ZH21+J%Z?3ZM1Z=%ZB2QO1%ZC2R72%ZE3ZM21+K%ZD3[21ZB%ZG2R41%ZH2R<2%ZJ3[221%VM261%VN2<1%VO2B1%W02F1%W12N1%W22Q41%W32Q:1%W42Q@1%W52QE1%W62QK1%W72R01%W82R41%W92R:1qT4[?1%S02[@1p0S21p0S51p0S;1p0S@1p0SE1p0SJ1p0SO1p0T31p0T71p0T;1p0T?1p0TC1p0TF1p0TK1p0U01p0U51p0U=1p0U@1p0UE1p0UO1p0V31p0V:1p0VA1p0VC1p0VF1p0VJ1p0W01p0W51p0W81p0W;1p0W=1p0W@1p0WB1p0WH1p0WM1p0X41p0X61p0X:1p0XD1p0XH1p0XJ1p0XM1p0Y31p0Y71p0Y<1p0YA1p0YD1p0YK1p0YO1p0Z31p0Z81p0Z;1p0Z=1p0ZB1p0ZF1p0ZJ1p0ZN1p0[11p0[71p0[=1p0[E1p0[M1p0\51p0\=1p0\E1p0]01pSJ]=1pSH]>1pD]?1p2]@1pU0]A1pS6]B1pU6]C1pS<]D1pU4]E1pF]F1pT2]G1pSD]H1pS@]I1pTF]J1pT@]K1pT>]L1pT<]N1pN]O1pT6^51")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 0%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 3%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 4%nat 0%nat).
Variable stat : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 5%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 7%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 8%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 9%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 10%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 11%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 12%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 13%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 14%nat 0%nat).
Variable C : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 15%nat 0%nat).
Variable D : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 16%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 17%nat 0%nat).
Variable nres : ltac:(sec_ty2 constr:(SEC_T_sec_head_run) 18%nat 0%nat).
Lemma sec_head_run : ltac:(sec_stmt2 constr:(SEC_T_sec_head_run) 19%nat 0%nat).
Proof using Type regs M1 rom s sec stat msz n r F tp key tsd ctx t C D nch nres.
intros H1 H2 H4 H10 H19 H21 H24.
intros Hs Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm Hri APr ARs Hsec Hsec' Hss Hst Hsec4 Hst8 HF HF'.
intros Ht Ht' APt ATr ATs ATc HC HC' HD HD'.
intros APc ACr ACs Htp Htp' Htsd Htsd'.
intros W1 W2 W3 W4 W5 C104 C112 C120 C128 Cpg C38 C144 LAY TSD CC CD Clk Cnch Cnres Hnch Hnres.
unfold kHighMemBeg in *.
assert (ESB : SB = 2147450880) by reflexivity.
pose proof (mod8_of_4096 r Hr4) as Hr8. pose proof (mod8_of_4096 msz Hm4) as Hm8.
divfacts r 8. divfacts n 8. divfacts msz 8.
pose proof TSD as (Tc1 & Tc2 & Tc3 & Tc4 & Tc5 & Ttp & Ttp' & Tkey & Ttsd & Ttsd' & Tctx & Tctx' & Tt).
assert (HL : 12 <= Z.log2 msz <= 46).
{ split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
assert (K512 : Z.of_nat (Z.to_nat (4096 / 8)) = 512) by reflexivity.
assert (E512 : 4096 / 8 = 512) by reflexivity.
assert (HT8 : 0 <= (msz - 4096 - n) / 8) by (apply Z.div_pos; lia). divfacts (msz - 4096 - n) 8.
assert (MT8 : (msz - 4096 - n) mod 8 = 0) by (replace (msz - 4096 - n) with ((msz / 8 - 512 - n / 8) * 8) by lia; apply Z_mod_mult).
assert (KT : Z.of_nat (Z.to_nat ((msz - 4096 - n) / 8)) = (msz - 4096 - n) / 8) by (apply Z2Nat.id; lia).
assert (MU8 : (4096 + r + n) mod 8 = 0) by mod8. divfacts (4096 + r + n) 8.
unfold appmem, kHighMemBeg in APr, APt, APc.
assert (PO1 : art_poison_lo_ok r 4096 \/ art_poison_hi_ok r 4096).
{ clear APt APc. unfold art_poison_lo_ok, art_poison_hi_ok, kHighMemBeg, kHighMemEnd. destruct APr; [left; lia | right; lia]. }
assert (PO2 : art_poison_lo_ok (4096 + r + n) (msz - 4096 - n) \/ art_poison_hi_ok (4096 + r + n) (msz - 4096 - n)).
{ clear APt APc. unfold art_poison_lo_ok, art_poison_hi_ok, kHighMemBeg, kHighMemEnd. destruct APr; [left; lia | right; lia]. }
assert (ASr : apart (SB + r / 8) (msz / 8) r 32) by (clear APt APc; unfold apart; lia).
assert (ASt : apart (SB + r / 8) (msz / 8) (t + 2872) 16) by (clear APr APc; unfold apart; lia).
assert (ASc : apart (SB + r / 8) (msz / 8) (ctx + 152) 8) by (clear APr APt; unfold apart; lia).
clear APr APt APc.
pose proof (sec_h1_fn regs M1 rom s sec stat msz n r F H1 H2 H10 H19 H21 H24 ltac:(lia) Hs' Hn Hn8 Hm Hnm Hr Hr4 Hrm Hsec Hsec' ltac:(lia) Hst HF HF'
W1 C104 C112 C120 C128 Cpg C38 C144) as RUN1.
match type of RUN1 with msteps _ _ (mkst ?R _ ?X _) => set (r1 := R) in RUN1; set (M2 := X) in RUN1 end.
assert (AG2 : forall x : word, ~ (s - 464 <= U x < s - 96) -> M2 x = M1 x).
{ intros x X1. pose proof (u64_range x). unfold M2. rewrite Wn_outside by (first [lia | cbn; lia]). reflexivity. }
assert (LAY2 : art_layout M2) by (apply (art_layout_agree M1 M2); [intros x Hx; apply AG2; lia | exact LAY]).
destruct (art_poison_run r1 M2 rom (Z_to_bv 64 0x56728) (s - 96) r 4096 250
ltac:(unfold r1; gres; reflexivity) ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(unfold M2; apply wr_Wn; apply (wr_sub _ _ _ _ _ _ W1); lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
LAY2 PO1 Hr8 ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(rewrite E512; unfold M2; apply wr_Wn; apply (wr_sub _ _ _ _ _ _ W3); lia))
as (r2 & RUN2 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & K2).
match type of RUN2 with msteps _ _ (mkst _ _ ?X _) => assert (EQ2 : X = sec_pm1 M1 s stat sec msz n r) end.
{ unfold sec_pm1, r1, M2. gres. rewrite H19. rewrite !art_u_lit by lia. reflexivity. }
rewrite EQ2 in RUN2. clear EQ2.
set (PM1 := sec_pm1 M1 s stat sec msz n r) in RUN2.
assert (AG3 : forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> PM1 x = M1 x).
{ intros x X1 X2. pose proof (u64_range x). unfold PM1, sec_pm1, art_poison_frame.
rewrite Wf_outside; [ | lia | rewrite K512; lia | rewrite K512; lia ].
rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity. }
assert (G3 : mem_grows M1 PM1).
{ unfold PM1, sec_pm1, art_poison_frame, M2. eapply mem_grows_trans; [ | apply Wf_grows ]. do 8 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl. }
assert (Q22 : getr r2 22 = Z_to_bv 64 (msz + r)) by (rewrite (K2 22%bv) by pk; unfold r1; gres; reflexivity).
assert (Q23 : getr r2 23 = Z_to_bv 64 (4096 + r + n)) by (rewrite (K2 23%bv) by pk; unfold r1; gres; reflexivity).
assert (Q24 : getr r2 24 = Z_to_bv 64 7) by (rewrite (K2 24%bv) by pk; unfold r1; gres; exact H24).
assert (Q25 : getr r2 25 = Z_to_bv 64 (4096 + r)) by (rewrite (K2 25%bv) by pk; unfold r1; gres; reflexivity).
assert (Q3x : getr r2 3 = getr regs 3) by (rewrite (K2 3%bv) by pk; unfold r1; gres; reflexivity).
assert (Q26x : getr r2 26 = getr regs 26) by (rewrite (K2 26%bv) by pk; unfold r1; gres; reflexivity).
assert (Q27x : getr r2 27 = getr regs 27) by (rewrite (K2 27%bv) by pk; unfold r1; gres; reflexivity).
assert (Q4 : getr r2 4 = Z_to_bv 64 tp) by (rewrite (K2 4%bv) by pk; unfold r1; gres; exact H4).
assert (Q8 : getr r2 8 = Z_to_bv 64 stat) by (rewrite P8; unfold r1; gres; reflexivity).
assert (Q9 : getr r2 9 = Z_to_bv 64 sec) by (rewrite P9; unfold r1; gres; reflexivity).
assert (Q18 : getr r2 18 = Z_to_bv 64 msz) by (rewrite P18; unfold r1; gres; reflexivity).
assert (Q19 : getr r2 19 = Z_to_bv 64 n) by (rewrite P19; unfold r1; gres; exact H19).
assert (Q20 : getr r2 20 = Z_to_bv 64 r) by (rewrite P20; unfold r1; gres; reflexivity).
assert (Q21 : getr r2 21 = Z_to_bv 64 (4096 + r + n)) by (rewrite P21; unfold r1; gres; reflexivity).
clear P8 P9 P18 P19 P20 P21 P10 P1 K2.
assert (S3 : exists r3, msteps ASEGS (mkst r2 (Z_to_bv 64 0x56728) PM1 rom) (mkst r3 (0x7a1e0 : word) PM1 rom)
/\ r3 = regupd (regupd (regupd (regupd r2 11 (Z_to_bv 64 (msz - 4096 - n))) 12 (Z_to_bv 64 250)) 10 (Z_to_bv 64 (4096 + r + n))) 1 (Z_to_bv 64 0x56738)).
{ eexists. split; [|reflexivity]. wpc.
zstep (ltac:(oF' 0x56728%Z)) (ltac:(oD' 0x56728%Z)). replace (msz + r - (4096 + r + n)) with (msz - 4096 - n) by lia.
zstep (ltac:(oF' 0x5672c%Z)) (ltac:(oD' 0x5672c%Z)). zstep (ltac:(oF' 0x56730%Z)) (ltac:(oD' 0x56730%Z)).
stepn (ltac:(oF' 0x56734%Z)) (ltac:(oD' 0x56734%Z)).
wpc. apply mst_refl. }
destruct S3 as (r3 & RUN3 & Er3).
assert (LAY3 : art_layout PM1) by (apply (art_layout_agree M1 PM1); [intros x Hx; apply AG3; lia | exact LAY]).
destruct (art_poison_run r3 PM1 rom (Z_to_bv 64 0x56738) (s - 96) (4096 + r + n) (msz - 4096 - n) 250
ltac:(subst r3; gres; reflexivity) ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
ltac:(subst r3; gres; exact P2) ltac:(subst r3; gres; reflexivity) ltac:(subst r3; gres; reflexivity) ltac:(subst r3; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(apply (wr_grows _ M1 PM1 _ _ G3); apply (wr_sub _ _ _ _ _ _ W1); lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
LAY3 PO2 MU8 MT8 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (wr_grows _ M1 PM1 _ _ G3); apply (wr_sub _ _ _ _ _ _ W3); lia))
as (r4 & RUN4 & P10 & P1 & P2' & P8 & P9 & P18 & P19 & P20 & P21 & K4).
match type of RUN4 with msteps _ _ (mkst _ _ ?X _) => assert (EQ4 : X = sec_pm2 M1 s stat sec msz n r) end.
{ unfold sec_pm2. subst r3. gres. rewrite Q8, Q9, Q18, Q19, Q20, Q21. rewrite !art_u_lit by lia. reflexivity. }
rewrite EQ4 in RUN4. clear EQ4.
set (PM2 := sec_pm2 M1 s stat sec msz n r) in RUN4.
assert (AG4 : forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> PM2 x = M1 x).
{ intros x X1 X2. pose proof (u64_range x). unfold PM2, sec_pm2, art_poison_frame. fold PM1.
rewrite Wf_outside; [ | lia | rewrite KT; lia | rewrite KT; lia ].
rewrite !Wn_outside by (first [lia | cbn; lia]). apply AG3; assumption. }
assert (G4 : mem_grows M1 PM2).
{ unfold PM2, sec_pm2, art_poison_frame. fold PM1. eapply mem_grows_trans; [ | apply Wf_grows ]. do 7 (eapply mem_grows_trans; [ | apply Wn_grows ]). exact G3. }
subst r3.
assert (V4 : getr r4 4 = Z_to_bv 64 tp) by (rewrite (K4 4%bv) by pk; gres; exact Q4).
assert (V8 : getr r4 8 = Z_to_bv 64 stat) by (rewrite P8; gres; exact Q8).
assert (V9 : getr r4 9 = Z_to_bv 64 sec) by (rewrite P9; gres; exact Q9).
assert (V18 : getr r4 18 = Z_to_bv 64 msz) by (rewrite P18; gres; exact Q18).
assert (V19 : getr r4 19 = Z_to_bv 64 n) by (rewrite P19; gres; exact Q19).
assert (V20 : getr r4 20 = Z_to_bv 64 r) by (rewrite P20; gres; exact Q20).
assert (V21 : getr r4 21 = Z_to_bv 64 (4096 + r + n)) by (rewrite P21; gres; exact Q21).
assert (V22 : getr r4 22 = Z_to_bv 64 (msz + r)) by (rewrite (K4 22%bv) by pk; gres; exact Q22).
assert (V24 : getr r4 24 = Z_to_bv 64 7) by (rewrite (K4 24%bv) by pk; gres; exact Q24).
assert (V25 : getr r4 25 = Z_to_bv 64 (4096 + r)) by (rewrite (K4 25%bv) by pk; gres; exact Q25).
assert (V3x : getr r4 3 = getr regs 3) by (rewrite (K4 3%bv) by pk; gres; exact Q3x).
assert (V26x : getr r4 26 = getr regs 26) by (rewrite (K4 26%bv) by pk; gres; exact Q26x).
assert (V27x : getr r4 27 = getr regs 27) by (rewrite (K4 27%bv) by pk; gres; exact Q27x).
clear P8 P9 P18 P19 P20 P21 P10 P1 K4 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25.
assert (TSD4 : art_tsd PM2 tp key tsd ctx t).
{ apply (art_tsd_agree M1 PM2); [intros x Hx; apply AG4; lia | intros x Hx; apply AG4; [unfold apart in ACs; lia | unfold apart in ASc; lia] | lia | lia | exact TSD]. }
assert (S5 : exists r5 M5, msteps ASEGS (mkst r4 (Z_to_bv 64 0x56738) PM2 rom) (mkst r5 (0x5673c : word) M5 rom)
/\ M5 = Wn 8 (Wn 8 PM2 (s - 104) 0x5673c) (s - 120) 0x82164
/\ getr r5 10 = Z_to_bv 64 (t + 2800) /\ getr r5 2 = Z_to_bv 64 (s - 96)
/\ (forall rg : reg, rg <> 1%bv -> rg <> 2%bv -> rg <> 10%bv -> rg <> 11%bv -> getr r5 rg = getr r4 rg)).
{ eexists. eexists. split; [ | split; [ | split; [ | split ] ] ].
- wpc. stepn (ltac:(oF' 0x56738%Z)) (ltac:(oD' 0x56738%Z)).
eapply msteps_trans; [ eapply (art_thread_stats_fn _ _ _ _ (s - 96) tp key tsd ctx t);
lazymatch goal with
| |- getr _ _ = _ => gres; rwH; reflexivity
| |- ret_ok _ => unfold ret_ok; apply bv_eq; vm_compute; reflexivity
| |- art_tsd _ _ _ _ _ _ => exact TSD4
| |- apart _ _ (ctx + 152) _ => unfold apart; unfold apart in ACs; lia
| |- apart _ _ _ _ => unfold apart; lia
| |- wr _ _ _ _ => apply (wr_grows _ M1 PM2 _ _ G4); apply (wr_sub _ _ _ _ _ _ W1); lia
| |- _ => lia
end .. | ].
rnorm. norm_pc. apply mst_refl.
- zmem_eq.
- kept_solve. - kept_solve.
- intros rg N1 N2 N10 N11. kept_solve. }
destruct S5 as (r5 & M5 & RUN5 & EM5 & T10 & T2 & K5). subst M5.
set (TM := Wn 8 (Wn 8 PM2 (s - 104) 0x5673c) (s - 120) 0x82164) in RUN5.
assert (AG5 : forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> TM x = M1 x).
{ intros x X1 X2. pose proof (u64_range x). unfold TM. rewrite !Wn_outside by (first [lia | cbn; lia]). apply AG4; assumption. }
assert (G5 : mem_grows M1 TM) by (unfold TM; do 2 (eapply mem_grows_trans; [ | apply Wn_grows ]); exact G4).
assert (U9 : getr r5 9 = Z_to_bv 64 sec) by (rewrite (K5 9%bv) by nlit; exact V9).
assert (U18 : getr r5 18 = Z_to_bv 64 msz) by (rewrite (K5 18%bv) by nlit; exact V18).
assert (U19 : getr r5 19 = Z_to_bv 64 n) by (rewrite (K5 19%bv) by nlit; exact V19).
assert (U20 : getr r5 20 = Z_to_bv 64 r) by (rewrite (K5 20%bv) by nlit; exact V20).
assert (U21 : getr r5 21 = Z_to_bv 64 (4096 + r + n)) by (rewrite (K5 21%bv) by nlit; exact V21).
assert (U22 : getr r5 22 = Z_to_bv 64 (msz + r)) by (rewrite (K5 22%bv) by nlit; exact V22).
assert (U24 : getr r5 24 = Z_to_bv 64 7) by (rewrite (K5 24%bv) by nlit; exact V24).
assert (U25 : getr r5 25 = Z_to_bv 64 (4096 + r)) by (rewrite (K5 25%bv) by nlit; exact V25).
assert (U4 : getr r5 4 = Z_to_bv 64 tp) by (rewrite (K5 4%bv) by nlit; exact V4).
assert (U8 : getr r5 8 = Z_to_bv 64 stat) by (rewrite (K5 8%bv) by nlit; exact V8).
#[warnings="-ltac"]
assert (CC6 : cellA TM (t + 2800 + 72) 8 C) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; [unfold apart in ATs; cbn in Hx; lia | unfold apart in ASt; cbn in Hx; lia] | lia | cbn; lia | replace (t + 2800 + 72) with (t + 2872) by lia; exact CC]).
assert (CD6 : cellA TM (t + 2800 + 80) 8 D) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; [unfold apart in ATs; cbn in Hx; lia | unfold apart in ASt; cbn in Hx; lia] | lia | cbn; lia | replace (t + 2800 + 80) with (t + 2880) by lia; exact CD]).
assert (Cpg6 : cellA TM sec 8 4096) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; cbn in Hx; lia | lia | cbn; lia | exact Cpg]).
assert (Clk6 : cellA TM (sec + 616) 4 0) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; cbn in Hx; lia | lia | cbn; lia | exact Clk]).
assert (Cnch6 : cellA TM (sec + 56) 8 nch) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; cbn in Hx; lia | lia | cbn; lia | exact Cnch]).
destruct (sec_h3_run r5 TM rom s sec msz n r (t + 2800) C D nch T2 U9 T10 U18 U19 U20 U21 U22 U24 U25
Hn Hn8 Hm Hnm Hr Hr4 Hrm Hsec Hsec' Hsec4 ltac:(lia) ltac:(lia) HC HC' HD HD' ltac:(lia)
ltac:(unfold apart; unfold apart in ATr; lia) ltac:(unfold apart; lia) Hri CC6 CD6 Cpg6 Clk6 Cnch6
ltac:(replace (t + 2800 + 72) with (t + 2872) by lia; apply (wr_grows _ M1 TM _ _ G5 W4))
ltac:(apply (wr_grows _ M1 TM _ _ G5 W2)) ltac:(apply (wr_grows _ M1 TM _ _ G5); apply (wr_sub _ _ _ _ _ _ W5); lia))
as (r6 & RUN6 & X10 & X13 & X21 & X2 & K6).
match type of RUN6 with msteps _ _ (mkst _ _ ?X _) => set (HM := X) in RUN6 end.
assert (AG6 : forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) ->
~ (t + 2872 <= U x < t + 2888) -> ~ (r <= U x < r + 32) -> ~ (sec + 616 <= U x < sec + 620) -> HM x = M1 x).
{ intros x Y1 Y2 Y3 Y4 Y5. pose proof (u64_range x). unfold HM. rewrite !Wn_outside by (first [lia | cbn; lia]). apply AG5; assumption. }
assert (G6 : mem_grows M1 HM) by (unfold HM; do 6 (eapply mem_grows_trans; [ | apply Wn_grows ]); exact G5).
assert (Z18 : getr r6 18 = Z_to_bv 64 msz) by (rewrite (K6 18%bv) by nlit; exact U18).
assert (Z9 : getr r6 9 = Z_to_bv 64 sec) by (rewrite (K6 9%bv) by nlit; exact U9).
assert (Cnres6 : cellA HM (sec + 48) 8 nres) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cnres]).
destruct (sec_sl_run r6 HM rom msz sec nres Z18 Z9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cnres6) as (r7 & RUN7 & Y19 & Y14 & K7).
exists r7. split; [ | zsplit ].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. unfold sec_hm. subst HM TM PM2 PM1. exact RUN7.
- rewrite (K7 2%bv) by nlit. exact X2.
- rewrite (K7 4%bv) by nlit. rewrite (K6 4%bv) by nlit. exact U4.
- rewrite (K7 8%bv) by nlit. rewrite (K6 8%bv) by nlit. exact U8.
- rewrite (K7 9%bv) by nlit. exact Z9.
- rewrite (K7 10%bv) by nlit. exact X10.
- rewrite (K7 13%bv) by nlit. exact X13.
- exact Y14.
- rewrite (K7 18%bv) by nlit. exact Z18.
- exact Y19.
- rewrite (K7 21%bv) by nlit. exact X21.
- rewrite (K7 3%bv) by nlit. rewrite (K6 3%bv) by nlit. rewrite (K5 3%bv) by nlit. exact V3x.
- rewrite (K7 26%bv) by nlit. rewrite (K6 26%bv) by nlit. rewrite (K5 26%bv) by nlit. exact V26x.
- rewrite (K7 27%bv) by nlit. rewrite (K6 27%bv) by nlit. rewrite (K5 27%bv) by nlit. exact V27x.
Qed.
End SE.
Section SE.
Variables (M1 : word -> option byte).
Variables (s stat sec msz n r t C D : Z).
Lemma sec_hm_agree : 0x691000 <= s - 464 -> s < 2 ^ 47 -> 0 <= n -> n mod 8 = 0 -> 2 ^ 12 <= msz -> msz mod 4096 = 0 -> n + 4096 <= msz -> 4096 <= r -> r mod 4096 = 0 -> r + msz < 2 ^ 47 ->
0 <= t -> t + 4096 < 2 ^ 47 -> 0 <= sec -> sec + 1024 < 2 ^ 64 ->
forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) ->
~ (t + 2872 <= U x < t + 2888) -> ~ (r <= U x < r + 32) -> ~ (sec + 616 <= U x < sec + 620) -> sec_hm M1 s stat sec msz n r t C D x = M1 x.
Proof using Type M1 s stat sec msz n r t C D.
intros Hs Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm Ht Ht' Hsec Hsec' x Y1 Y2 Y3 Y4 Y5.
pose proof (u64_range x). assert (ESB : SB = 2147450880) by reflexivity.
pose proof (mod8_of_4096 r Hr4) as Hr8. pose proof (mod8_of_4096 msz Hm4) as Hm8.
divfacts r 8. divfacts n 8. divfacts msz 8. divfacts (msz - 4096 - n) 8. divfacts (4096 + r + n) 8.
assert (HT8 : 0 <= (msz - 4096 - n) / 8) by (apply Z.div_pos; lia).
assert (MT8 : (msz - 4096 - n) mod 8 = 0) by (replace (msz - 4096 - n) with ((msz / 8 - 512 - n / 8) * 8) by lia; apply Z_mod_mult).
assert (MU8 : (4096 + r + n) mod 8 = 0) by mod8.
assert (K512 : Z.of_nat (Z.to_nat (4096 / 8)) = 512) by reflexivity. assert (E512 : 4096 / 8 = 512) by reflexivity.
assert (KT : Z.of_nat (Z.to_nat ((msz - 4096 - n) / 8)) = (msz - 4096 - n) / 8) by (apply Z2Nat.id; lia).
unfold sec_hm, sec_pm2, sec_pm1, art_poison_frame.
rewrite Wn_outside; [ | lia | cbn; lia | clear Y1 Y2 Y3 Y4; cbn; lia ].
do 3 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y1 Y2 Y3 Y5; cbn; lia ]).
do 2 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y1 Y2 Y4 Y5; cbn; lia ]).
do 2 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y2 Y3 Y4 Y5; cbn; lia ]).
rewrite Wf_outside; [ | lia | rewrite KT; lia | rewrite KT; clear Y1 Y3 Y4 Y5; lia ].
do 7 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y2 Y3 Y4 Y5; cbn; lia ]).
rewrite Wf_outside; [ | lia | rewrite K512; lia | rewrite K512; clear Y1 Y3 Y4 Y5; lia ].
do 8 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y2 Y3 Y4 Y5; cbn; lia ]).
reflexivity.
Qed.
End SE.
#[using="Type"] Lemma sec_hm_grows : ltac2:(TCodec.tc2 tcn__JatSecAllocPost "Q1'R=yR0%211'1y8%511%311p051'8&Q4r:&Lr9r8r7r6r5r4r3r2r1%::;987654321%=2<1pD?1p2@1pU0A1pT2B1pSDC1pS@D1pT@E1pTFF1pT>G1pNI1").
Proof.
intros. unfold sec_hm, sec_pm2, sec_pm1, art_poison_frame.
do 8 (eapply mem_grows_trans; [ | apply Wn_grows ]). eapply mem_grows_trans; [ | apply Wf_grows ].
do 7 (eapply mem_grows_trans; [ | apply Wn_grows ]). eapply mem_grows_trans; [ | apply Wf_grows ].
do 8 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.
Section SE.
Local Abbreviation SEC_T_art_sec_postA_run := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "cK&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1rQ5(R;+1(2%33A21%6251&R<+acSH%22C1%;3C41rQ6+2%;3I19%>231&Q>rH+T@%3221%<2M1%E3M61rQ7+4%E3Q31C%H231rB%C2Q41%L3Q431rQ8+:%L3Q:1J%O231rE%J2Q;1%Q33Q;31rQ9+C%Q33QA1Q1%Q6231rG%Q12QB1%Q:3QB31rQ:+E%Q:3QH1Q8%Q=231+8%Q82QI1%QA3QI31rQ;+H%QA3QO1Q?%QD231+7%Q?2R01%QH3R031&E%11F&Q8&IrO+^@%Q?221%5241&Q:rQ0&Q=+Q?%22QH1%5241zrM%>221&Q;rN%221M%R=3R>16+<%<2R21%E21>rQ1+TP0%9221%RD3RE1=&Q6%1254rQ2%M221%N278%@238%RK3RL1DrQ3%821RK%M21I+VbTP0rQ4%Q6221&J%12S1R=&A%RE2QCQ7%24RJR91Q8+RPP0%Q=21QFrQ<+QP0%F221%Q;21=rQ=+c@%J221%QE217+R0%M251%QB21DrQ?+c8%Q1221%Q=21S0%SH3SI1QA%Q?25R:%SJ3SK1QC%R02DB+`0%Q82@1%QM21O'7'3%R62Q?RM%Q=2RNQ@%R821L%4231%R:2Q6S1%7221%QB2RLQE%R721R3%Q72RGQG+RiH%QF2Q21+@rQB+Q0%Q;44321%QK2Q36rQH%T221RD%Q?4371RErQ>%R021;+TH%R22Q31%QD43<1S9%RN2RB5%RG2T=Q9%RJ2Q71%S12REQ8rQ@%RM214%S42RH2+D%RN2TD1%S1251%Q3241%Q4256&6rQA%U73U8J1%311%S>2R:3&Q<rQD%22SM1%RH2Q01%RI21SO%S>21S:rQCrQE%82T31%RN231%RB21T5rQF%<2T71%S22<1rQO%RE42T:1Q;rQG%A2T<1%S72;1rR5%U>21T0%RK43T@1T1%F2TAQ?%S<2<1rQK%S>21QI%S043TE1QH%T:2SN@%T52<Q<%T<2T0=%T72QGQ>%T>2T2QH%R:212rQI%T;21QB%TB2T62rQJ%T>21QE%TE2T92%T@2?QGrR8%SA21T1rR9%T021QOrR>%SC42U81R9rR:%T421R3rRD%V;21TM%SH43U=1TN+RH%V>281%U42T=1rR?%U021T2%U72T@<rR@%QJ2UE1%T@251%TA21UG%U<21T8&C&Q5rS6rRI%VL21U>%54431U?rS7rRE%84721S2rS8&G&Q7rRF%221V6%U1241rRH%521V9%A4@831rS9rRA%U721SB%E4D31SArS:rRL%H4G21TBrS;%U=23SF%K4J21SGrS<%RK2VF:%UA2Q61%O4N31VH&BrS=rS0+S8%WL221u8+Zif@%75Q66321rS>rS1+S@%X3221rRO%=5Q<5281rS?rS2+SH%X9221%B5QA41=9rS@rS3+T0%X>221%G5QF41BErSArS4%XB21WC&R>%12Y=>%M5QL53H1rSBrS5%XH21TL%Q15R031L5rSC%XK2R1WH%Q45R321O8rSD%XN2R0U0%Q75R621Q2;rSE+Q8%Y22R11%Q;5R:31Q6?rSF+Q@%Y62QL1%Q?5R>31Q:CrSG+QH%Y:2QL1%QC5RB31Q>GrSH%Y=2QLV<%QF5RE21QAJrSI+R8%YA2QM1%QJ5RI31QENrSJ+R@%YE2QL1%QN5RM31QIQ2rSK%YH2QHS;%R15S021QLQ5rSL%R35S21QKQNWIrSM+QVYa8%R65S521R1R@rSN%WK2R?YN%R95S821R4X:&HrSO%211&FrT0%261RCRFRIRMS6rT1%X42ROV?%RB5SA21R=S9rT2+Rj0%X82RO1%RF5SE31RAS=rT3%X;2Q@W;u4%RJ5SI321XKrT4%X?2Q@Q;%RM5SL21RHS;rT5%XB2Q?QB%S05SO21RKS>rT6%XE2Q>YK%S35T221RNSArT7%XH2Q>Q=%S65T521S1SDrT8%XK2Q=TC%S95T821S4SGrT9+S0%XO2Q=1%S=5T<31S8SKrT:%Y22Q=S<&Q9%11QF%V@2Z;1%Y6241%SD5TC61S?T2rT;%Y92QDWB%SG5TF21SBT5rT<%Y<2QEZ>%SJ5TI21SET8'5'D&Q2vQDrT?+a\i<%\63\B1\4/01\BrT>rT=%8576321r1&N%1B5QHQMQJR1R4R6RLS0S3S6S@SESJT0T7T<T?%<5;3A15%>3U951%\B25[D%YO2Z2R:%\=2\N1%\F3\N31%\F29\9%\@2]1R0%\I3]121%\I2<\D%\K3]31K%\I3]7[=\G%\L2?1%\N3]61Q1+9%\M3];1\K%]02C1%]23]:1Q<+B%]13]?1\O%]42G1%]63]>1QD%]62I\1%]83]@1QI%]63]DX9]4%]92L1%];3]C1QO%];2N[O%]=3]E1R4+F%]<3]J1]:%]?2Q21%]A3]I1R;+G%]@3]N1]>%]C2Q61%]E3]M1RB%]E2Q8\2%]G3]O1RH+I%]F3^41]D%]I2Q<1%]K3^31S0%]K2Q>]4%]E2^6SJ%]N3^621+3%]M3^;1]K%^02QC1%^12QK2%^33^;21+J%^23^@1^0%^52QH1%^62R02%^83^@21+K%^73^E1^5%^:2QM1%^;2R52%^=3^E21%Z>261%Z?2<1%Z@2B1%ZA2F1%ZB2K1%ZC2N1%ZD2Q31%ZE2Q81%ZF2Q;1%ZG2Q?1%ZH2QB1%ZI2QG1%ZJ2QL1%ZK2R01%ZL2R31%ZM2R71%ZN2R<1qT8_61%RM2_71p0RO1p0S31p0S71p0S?1p0SD1p0SH1p0SL1p0T01p0T41p0T81p0T=1p0TB1p0TF1p0TJ1p0TN1p0U21p0U61p0U91p0U=1p0UB1p0UG1p0UK1p0V01p0V51p0V:1p0V>1p0VB1p0VG1p0VN1p0W41p0W:1p0WA1p0WJ1p0WO1p0X31p0X71p0X<1p0XF1p0XJ1p0Y11p0Y71p0Y91p0Y<1p0Y@1p0YF1p0YK1p0YN1p0Z01p0Z21p0Z51p0Z71p0Z;1p0Z;1p0Z>1p0Z@1p0ZB1p0ZD1p0ZF1p0ZL1p0[31p0[91p0[?1p0[F1p0[H1p0[M1p0[O1p0\51p0\81p0\:1p0\=1p0\?1p0\E1p0\J1p0]11p0]31p0]61p0]?1p0]C1p0]E1p0]H1p0]N1p0^21p0^71p0^<1p0^?1p0^C1p0^F1p0^J1p0^N1p0_11p0_31p0_81p0_=1p0_A1p0_F1p0_J1p0`11p0`81p0`;1p0`C1p0`K1p0a31p0a;1p0aC1p0aN1pTDb;1pTBb<1pS4b=1pSBb>1pS8b?1pSFb@1pSLbA1pSJbB1pSHbC1pDbD1p2bE1pU0bF1pS6bG1pU6bH1pS<bI1pU4bJ1pFbK1pT2bL1pSDbM1pS@bN1pTFbO1pT@c01pT>c11pUJc91pUHc:1pUFc;1pUDc<1pUBc=1pU@c>1pU>c?1pU<c@1pUNcA1pULcB1pU:cC1pT<c>1pNc?1pT6cE1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 0%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 2%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 3%nat 0%nat).
Variable x8 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 4%nat 0%nat).
Variable x9 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 5%nat 0%nat).
Variable x18 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 6%nat 0%nat).
Variable x19 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 7%nat 0%nat).
Variable x20 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 8%nat 0%nat).
Variable x21 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 9%nat 0%nat).
Variable x22 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 10%nat 0%nat).
Variable x23 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 11%nat 0%nat).
Variable x24 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 12%nat 0%nat).
Variable x25 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 13%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 14%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 15%nat 0%nat).
Variable stat : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 16%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 17%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 18%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 19%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 20%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 21%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 22%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 23%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 24%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 25%nat 0%nat).
Variable C : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 26%nat 0%nat).
Variable D : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 27%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 28%nat 0%nat).
Variable nres : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 29%nat 0%nat).
Variable pab : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 30%nat 0%nat).
Variable na : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 31%nat 0%nat).
Variable cur : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 32%nat 0%nat).
Variable mx : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 33%nat 0%nat).
Variable bsl : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 34%nat 0%nat).
Variable st16 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 35%nat 0%nat).
Variable st24 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postA_run) 36%nat 0%nat).
Theorem art_sec_postA_run : ltac:(sec_stmt2 constr:(SEC_T_art_sec_postA_run) 37%nat 0%nat).
Proof using Type regs M1 rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat msz n r F tp key tsd ctx t C D nch nres pab na cur mx bsl st16 st24.
intros H1 H2 H4 H10 H19 H21 H24 Hret.
intros Hs Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm Hri APr ARs Hsec Hsec' Hss Hst Hsec4 Hst8 HF HF'.
intros Ht Ht' APt ATr ATs ATc HC HC' HD HD' Hnch Hnres Hne Hpi Hpab' APp APPr APPs APPt.
intros Hna Hna' Hcur Hcur' Hmx Hbsl Hbsl' H16 H16' H24a H24a'.
intros APc ACr ACs Htp Htp' Htsd Htsd'.
intros W1 W2 W3 W4 W5 W6 W7 C104 C112 C120 C128 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 Cpg C38 C144 LAY TSD CC CD Clk Cnch Cnres Cpab Cna Ccur Cmx Cbsl C16 C24.
unfold kHighMemBeg in *.
assert (HL : 12 <= Z.log2 msz <= 46).
{ split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
assert (ESB : SB = 2147450880) by reflexivity.
pose proof (mod8_of_4096 r Hr4) as Hr8. pose proof (mod8_of_4096 msz Hm4) as Hm8. divfacts r 8. divfacts msz 8.
pose proof (sec_head_run regs M1 rom s sec stat msz n r F tp key tsd ctx t C D nch nres) as HEAD.
repeat lazymatch type of HEAD with
| ?P -> _ => let HP := fresh "HP" in assert (HP : P) by (first [assumption | lia]); specialize (HEAD HP); clear HP
end.
destruct HEAD as (r7 & RUNH & Y2 & Y4 & Y8 & Y9 & Y10 & Y13 & Y14 & Y18 & Y19 & Y21 & Y3x & Y26x & Y27x).
set (HM := sec_hm M1 s stat sec msz n r t C D) in RUNH.
pose proof (sec_hm_agree M1 s stat sec msz n r t C D ltac:(lia) Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm ltac:(lia) Ht' ltac:(lia) ltac:(lia)) as AG6. fold HM in AG6.
pose proof (sec_hm_grows M1 s stat sec msz n r t C D) as G6. fold HM in G6.
unfold appmem, kHighMemBeg in APt, APp.
assert (ASt : apart (SB + r / 8) (msz / 8) (t + 2872) 16) by (clear APp; unfold apart; lia).
assert (ASp : apart (SB + r / 8) (msz / 8) (pab + 8 * nch) 8) by (clear APt; unfold apart; lia).
clear APt APp APr APc.
assert (RUN8 : msteps ASEGS (mkst r7 (0x56874 : word) HM rom) (mkst r7 (0x56878 : word) HM rom)).
{ zbft (ltac:(oF' 0x56874%Z)) (ltac:(oD' 0x56874%Z)). apply mst_refl. }
assert (ARs' : apart r 32 (s - 464) 464) by (unfold apart in ARs |- *; lia).
assert (D1 : cellA HM (sec + 8) 8 pab) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cpab]).
assert (D2 : cellA HM (sec + 72) 8 na) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cna]).
assert (D3 : cellA HM (sec + 88) 8 cur) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Ccur]).
assert (D4 : cellA HM (sec + 96) 8 mx) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cmx]).
assert (D5 : cellA HM (sec + 104 + 8 * Z.log2 msz) 8 bsl) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cbsl]).
assert (D6 : cellA HM (stat + 16) 8 st16) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact C16]).
assert (D7 : cellA HM (stat + 24) 8 st24) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact C24]).
assert (E1 : cellA HM (s - 8) 8 (U x1)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L1]).
assert (E2 : cellA HM (s - 16) 8 (U x8)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L2]).
assert (E3 : cellA HM (s - 24) 8 (U x9)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L3]).
assert (E4 : cellA HM (s - 32) 8 (U x18)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L4]).
assert (E5 : cellA HM (s - 40) 8 (U x19)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L5]).
assert (E6 : cellA HM (s - 48) 8 (U x20)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L6]).
assert (E7 : cellA HM (s - 56) 8 (U x21)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L7]).
assert (E8 : cellA HM (s - 64) 8 (U x22)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L8]).
assert (E9 : cellA HM (s - 72) 8 (U x23)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L9]).
assert (E10 : cellA HM (s - 80) 8 (U x24)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L10]).
assert (E11 : cellA HM (s - 88) 8 (U x25)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L11]).
pose proof (sec_tail_fn r7 HM rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat r msz nch pab na cur mx (Z.log2 msz) bsl st16 st24
Y2 Y8 Y9 Y10 Y13 Y18 Y19 Y21 Hret ltac:(lia) Hs' Hm Hr Hrm Hri Hsec Hss Hst Hst8 ltac:(lia) Hpi Hpab'
Hna Hna' Hcur Hcur' Hmx ltac:(lia) Hbsl Hbsl' H16 H16' H24a H24a' APPr APPs ARs'
D1 D2 D3 D4 D5 D6 D7 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
ltac:(apply (wr_grows _ M1 HM _ _ G6); apply (wr_sub _ _ _ _ _ _ W2); lia) ltac:(apply (wr_grows _ M1 HM _ _ G6 W7))
ltac:(apply (wr_grows _ M1 HM _ _ G6 W5)) ltac:(apply (wr_grows _ M1 HM _ _ G6 W6))) as RUN9.
match type of RUN9 with msteps _ _ (mkst ?R _ _ _) => exists R end.
split; [ | zsplit ].
- eapply msteps_trans; [exact RUNH|]. eapply msteps_trans; [exact RUN8|]. unfold sec_postA_mem. subst HM. exact RUN9.
- gres. exact Y10.
- gres. reflexivity.
- gres. reflexivity.
- gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
- gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
- gres. exact Y4.
- gres. exact Y3x.
- gres. exact Y26x.
- gres. exact Y27x.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_sec_postB1_run := (ltac2:(TCodec.tc2 tcn__JatSecAllocPost "`=&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1rC(R;+1(2%33A21%6251&R<+acSH%22C1%;3C41rD+2%;3I19%>231&Q>rA+T@%3221%<2M1%E3M61rE+4%E3Q31C%H231r;%C2Q41%L3Q431rF+:%L3Q:1J%O231r>%J2Q;1%Q33Q;31rG+C%Q33QA1Q1%Q6231r@%Q12QB1%Q:3QB31rH+E%Q:3QH1Q8%Q=231+8%Q82QI1%QA3QI31rI+H%QA3QO1Q?%QD231+7%Q?2R01%QH3R031&Q8&I+^@%Q<2H1%4231&Q:&Q=+Q?%22QD1%42G1z%;21Q>&Q;%12Q9G%R73R814+<%:2QL1%A21O+TP0%72J1%R=3R>1:&Q6%12M4rJ%H221%I27Q0%>238%RD3RE1ArKrM%9221%J21G+VbTP0rL%Q2221&JrO%2281&ArNrQ0rQ3%RC21Q8%54431Q9+RPP0%Q=214rQ4+QP0%K221%Q<21ArQ5+c@%O221%QE217+R0%Q2251%QC21HrQ7+c8%Q6221%Q@21RN%SF3SG1QC%QB25R8%SH3SI1QE%R02DB+`0%Q=2@1%QN21Q3'7'3rQ1%R72QE1%QC22QF%R921M%5231%R;2Q;5%8221rQ2%QI21QL%R:21R7%Q=2Q7QN+RiH%QM2Q41+@rQ:+Q0%Q@44321%R22Q56rQ@%T221RG%QD4371RHrQ6%R721;+TH%R92Q51%QI43<1S9%S02RF5%RK2T=Q;%RM2Q91%S32RIQ:rQ8%S0214rQ<%R421RErQ=%RD21<rQB%R542SE1FrQ>%RH21@rQH%TH21S=%R:43SJ1S>+RH%TK281%SC2S11rQC%S@21RE%SF2S4<&Q<rQD%22T31%S5261%S621T5%SL21RL&C&Q5rQOrQM%U:21SO%54431T0rR0rQI%84721Q@rR1&G&Q7rQJ%221TD%SF241rQL%521TG%A4@831rR2rQE%SL21R0%E4D31QOrR3%G4F1AS1&BrR4+S8%V1291u8+Zif@%65M5321rR5+S@%V72;1%:5Q1316IrR6+SH%V;2<1%>5Q531:@rR7+T0%V?2:1%B5Q931>HrR8%D5Q;1=@TGrR9+QVYa8%G5Q>21CQ6rR:%TI2OVE%J5QA21FU5&HrR;%211&FrR<%261Q2Q6Q?QBQFrR=%U22QDS6%Q35QJ21OQIrR>+Rj0%U62QE1%Q75QN31Q3QMrR?%U92:T4u4%Q;5R2321UFrR@+QH%U>2=1%Q?5R631Q;R1rRA+Q@%UB2>1%QC5R:31Q?R2%V92UOQJ+D%V52WG1%V72QM1%T8241+QV\W0%V?21>%UK2;U1+QiYm0%VB221rRErRB%V021T2%R15RH31QMR0rRF+QVY`H%R45RK21R08rRG%R65RM1:R2V9%VL2V:QH%S62W7QC%V92QF1+TPP0%V;221%VL21VI%S;2W<QE%V>2QI1%VH21VB%XN3XO1VK'5'D&Q2vQDrRM+a\i<%Y23Y>1Y0/01Y>rRLrRK%8576321r1+a\i8%Y93YE1Y7/01YE&K&LrRJrRHrRI%4:<321Q0Q3Q7QMR1R4+QO&Q9%11Q3%Y7231%:95876Q51Q<R>R;%H5G?<1A%J3T3A1+A%YI3Z71YG%YL2C1+VN%YG2Z81%Z03Z831%Z02GY2%TB2XCRE%WE2RI1%YL2Z=1%Z53Z=41+;%Z43ZB1Z2%Z72N1%Z12ZBQA%Z:3ZB21%Z83ZFX3Z6%Z;2Q21+3%Z62ZG1%Z?3ZG31+=%Z>3ZL1Z<%ZA2Q81+QB%Z<2ZM1%ZE3ZM31+>%ZD3[21ZB%ZG2Q>1+_oooooooooooO%ZB2[31%ZK3[331+?%ZJ3[81ZH%ZM2QD1%ZG2[8XL%[03[821%[02QGZK+adW8%ZK2[<1%[43[<31%[42QKZG+V0%ZG2QG1%[02[A1%[93[A41%[73[EYK[5%[:2R11%[<3[D1Q3+9%[;3[I1[9%[>2R51%[@3[H1A+B%[?3[M1[=%[B2R91%[D3[L1Q@%[D2R;Z?%[F3[N1G%[D3\2SD[B%[G2R>1%[A2\2S?%[J3\221%[J2RAZ>%[D2\5S@%[M3\521%[M2RD[6rRC%[H2\91%\13\931%[O3\=QE[M%\22RI1%\32S12%\53\=21+J%\43\B1\2%\72RN1%\82S62%\:3\B21+K%\93\G1\7%\<2S31%\=2S;2%\?3\G21%XB261%XC2<1%XD2A1%XE2F1%XF2J1%XG2O1%XH2Q21%XI2Q71%XJ2Q<1%XK2Q@1%XL2QF1%XM2QK1%XN2R11%XO2R81%Y02R?1%Y12RE1%Y22RK1%Y32S11%Y42S81qT8]:1%T52];1p0T71p0T<1p0TB1p0TD1p0TG1p0TK1p0U01p0U41p0U71p0U=1p0UB1p0UG1p0UL1p0V11p0V51p0V91p0V=1p0VA1p0VE1p0VH1p0VM1p0W21p0W71p0W?1p0WB1p0WG1p0X11p0X51p0X<1p0XC1p0XE1p0XH1p0XL1p0Y21p0Y71p0Y:1p0Y=1p0Y?1p0YB1p0YD1p0YJ1p0YO1p0Z61p0Z81p0Z<1p0ZF1p0ZJ1p0ZL1p0ZO1p0[51p0[91p0[>1p0[C1p0[F1p0[M1p0\11p0\51p0\:1p0\=1p0\?1p0\D1p0\H1p0\L1p0]01p0]31p0]91p0]?1p0]G1p0]O1p0^71p0^?1p0^G1p0_21pSN_?1pSH_@1pD_A1p2_B1pU0_C1pS6_D1pU6_E1pS<_F1pU4_G1pF_H1pT2_I1pSD_J1pS@_K1pTF_L1pT@_M1pT>_N1pT<`01pN`11pT6`71")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 0%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 3%nat 0%nat).
Variable sec : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 4%nat 0%nat).
Variable stat : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 5%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 7%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 8%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 9%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 10%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 11%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 12%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 13%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 14%nat 0%nat).
Variable C : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 15%nat 0%nat).
Variable D : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 16%nat 0%nat).
Variable nch : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 17%nat 0%nat).
Variable pab2 : ltac:(sec_ty2 constr:(SEC_T_art_sec_postB1_run) 18%nat 0%nat).
Theorem art_sec_postB1_run : ltac:(sec_stmt2 constr:(SEC_T_art_sec_postB1_run) 19%nat 0%nat).
Proof using Type regs M1 rom s sec stat msz n r F tp key tsd ctx t C D nch pab2.
intros H1 H2 H4 H10 H19 H21 H24.
intros Hs Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm Hri APr ARs Hsec Hsec' Hss Hst Hsec4 Hst8 HF HF'.
intros Ht Ht' APt ATr ATs ATc HC HC' HD HD'.
intros APc ACr ACs Htp Htp' Htsd Htsd'.
intros W1 W2 W3 W4 W5 C104 C112 C120 C128 Cpg C38 C144 LAY TSD CC CD Clk Cnch Cnres Hnch Hsg Hsg' Cp2 Cg28 Cpc Hpab2 Hpab2' Hal.
unfold kHighMemBeg in *.
assert (HL : 12 <= Z.log2 msz <= 46).
{ split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
assert (ESB : SB = 2147450880) by reflexivity.
pose proof (mod8_of_4096 r Hr4) as Hr8. pose proof (mod8_of_4096 msz Hm4) as Hm8. divfacts r 8. divfacts msz 8.
pose proof (sec_head_run regs M1 rom s sec stat msz n r F tp key tsd ctx t C D nch nch) as HEAD.
repeat lazymatch type of HEAD with
| ?P -> _ => let HP := fresh "HP" in assert (HP : P) by (first [assumption | lia]); specialize (HEAD HP); clear HP
end.
destruct HEAD as (r7 & RUNH & Y2 & Y4 & Y8 & Y9 & Y10 & Y13 & Y14 & Y18 & Y19 & Y21 & Y3x & Y26x & Y27x).
set (HM := sec_hm M1 s stat sec msz n r t C D) in RUNH.
pose proof (sec_hm_agree M1 s stat sec msz n r t C D ltac:(lia) Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm ltac:(lia) Ht' ltac:(lia) ltac:(lia)) as AG6. fold HM in AG6.
pose proof (sec_hm_grows M1 s stat sec msz n r t C D) as G6. fold HM in G6.
clear APt APr APc.
assert (D1 : cellA HM (sec + 16) 8 pab2) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cp2]).
assert (D2 : cellA HM 0x132618 8 0x1ca7a0) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cg28]).
assert (D3 : cellA HM 0x1ca7a0 8 4096) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cpc]).
pose proof (sec_b1_fn r7 HM rom s sec stat (63 - Z.log2 msz) nch pab2 r msz Y2 Y8 Y9 Y10 Y13 Y14 Y18 Y19 Y21
ltac:(lia) Hs' Hr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsec Hsec' Hnch Hpab2 Hpab2' Hal
ltac:(apply (wr_grows _ M1 HM _ _ G6 W1)) D1 D2 D3) as RUNB.
match type of RUNB with msteps _ _ (mkst ?R _ _ _) => exists R end.
split; [ | zsplit ].
- eapply msteps_trans; [exact RUNH|]. subst HM. exact RUNB.
- gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
- gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
- gres. reflexivity.
- gres. exact Y4.
- gres. exact Y3x.
- gres. exact Y26x.
- gres. exact Y27x.
Qed.
End SE.
Definition sec_postB_mem (M2 : word -> option byte) (s stat sec msz r nch nres pab na cur mx bsl st16 st24 : Z) : word -> option byte :=
sec_tail_mem (Wn 8 (Wn 4 M2 (s - 148) 18446744072277895850) (sec + 48) (nres + 16384)) sec stat r msz nch pab na cur mx (Z.log2 msz) bsl st16 st24.
#[using="Type"] Theorem art_sec_postB2_run : ltac2:(TCodec.tc2 tcn__JatSecAllocPost "_A&;y5'R=yR0%211%5241'1y8%611%311p061'8'4&Q1rO(R;+1(2%33A21%6251&R<+adW8%22C1%;3C41rQ0+2%;3I19%>231&Q>rB+V0%3221%<2M1%E3M61rQ1+4%E3Q31C%H231r=%C2Q41%L3Q431rQ2+8%L3Q:1J%O231+TPP0%J2Q;1%Q33Q;31rQ3+:%Q33QA1Q1%Q6231r<%Q12QB1%Q:3QB31rQ4+E%Q:3QH1Q8%Q=231%Q72QHN%Q@3QH21&E%11E&Q8+VbTP0rH+^@%Q7221%5241&Q:rI&Q=+Q?%22Q@1%5241'3+<%62QD1rG%@221%;227%6221+TP0%D215&Q6%12D?%A21=%H2GAzrE%K221+R0%E2R31+SoO%R2221%J261%E261+RPP0rN%Q4221+QP0%A2RG1%Q121Q6+c@%D2R@1%Q:21RK%F2RB?%Q621Q;&Q;%12R;R3%S23S31F%Q@2>S1+`0%M2RI1%Q=21QB%QD2KS5+D%Q>2RL1%QA2S81%Q<241+Q8%QB2S01%QE2S<1%Q@281%QM2QLJ&Q<%12RDRE%Q;2SA1%Q<21RF%QL21QH&A%62RIRC%Q@2S<1rQ6+Q0%543RM21%;2RNRA%QE2S71rQ;%S?21R9%:43S21R:rQ8rQ<%SC21R=%>43:1R>%RB2QIS8%R=2S2QF%RD2QKS3%R?2RMQH%RF2QMRN%R;212rQ5%RC21QL%RJ2R12%RE2EQN%RL2R3FrQ7%RH21R1&C&Q5rR5rQH%T621S0%54431S1rR6%74614QNrR7+@%RD271%;4:312rR8rQG+H%RI221%@4?41T4rR9rQBrQE%QE2T81%RO231%F4E51T:&BrR:rQM+S8%TM221u8+Zjc@%75M6321rR;rQN+S@%U4221rQL%=5Q35281rR<rQO+SH%U:221%B5Q841=9rR=rR0+T0%U?221%G5Q=41BErR>rR1+T8%UD221+QO&Q9%11E%UH231%Q05QF85K1rR?rR2+T@%UM221%T62T8L%Q65QL52Q11rR@+QVYa8%Q95QO21Q4Q0rRA%T<2L8%Q<5R221Q7T9rRBrR4+Q@%TA221%QA5R741Q<Q?rRC+QH%TE2R91%QE5R;31Q@Q6rRD%TH2R8V2%QH5R>21QCQFrRE+R8%TL2R:1%QL5RB31QGQJrRF+RH%U02R:1%R05RF31QKQNrRG+S0%U42R91%R45RJ31QOR2rRH%U72R5R3%Q:1RB%T02VC1%U:231%R:5S051R5R8rRI%U=2R;RJ%R=5S321R8R;rRJ%U@2R7RH%R@5S621R;R>rRK%W;2QJVM&R>%12X69%RE5S;43R@1rRL%W@2QFS5%RH5S>21RC4rRM%WC2QCS3%RK5SA21RF7rRN%WF2QCT<%RN5SD21RI:rRO%WI2QCTM%S15SG21RL=rS0%WL2QAQD%S45SJ21RO@rS1%WO2Q@QC%S75SM21S2CrS2%X22Q@V3%S:5T021S5FrS3%X52Q?QB%S=5T321S8IrS4+R@%X92Q?1%SA5T731S<MrS5%X<2Q>QE%SD5T:21S?Q0'5'D&Q2vQDrS8+a\i<%Y13Y=1XO/01Y=rS7rS6%8576321r1&O%1?5QDQMQGR1R5R@RERKS1S:S?SDSJT1%<5;3A15%>3TJ51%Y=25X8%W72W9R9%Y82YI1%YA3YI31%YA29Y4%Y;2YLQL%YD3YL21%YD2<Y?%YF3YN1K%YF2>XH%YH3Z01Q1+9%YG3Z51YE%YJ2B1%YL3Z41Q8+B%YK3Z91YI%YN2F1%Z03Z81Q?+C%YO3Z=1YM%Z22J1%Z43Z<1QF%Z23Z@VMZ0%Z52M1%Z73Z?1QL%Z72OXK%Z93ZA1R1+F%Z83ZF1Z6%Z;2Q31%Z=3ZE1R8+G%Z<3ZJ1Z:%Z?2Q71%ZA3ZI1R?%Z?3ZMUBZ=%ZB2Q:1%ZD3ZL1RE+I%ZC3[11ZA%ZF2Q>1%ZH3[01RN%ZH2Q@Z1%ZB2[3SK%ZK3[321+3%ZJ3[81ZH%ZM2QE1%ZN2QM2%[03[821+J%ZO3[=1ZM%[22QJ1%[32R22%[53[=21+K%[43[B1[2%[72QO1%[82R72%[:3[B21%Y<261%Y=2<1%Y>2B1%Y?2F1%Y@2K1%YA2O1%YB2Q41%YC2Q91%YD2Q<1%YE2Q@1%YF2QE1%YG2QJ1%YH2QO1%YI2R21%YJ2R51%YK2R91%YL2R>1qT8\31%RO2\41p0S11p0S51p0S:1p0S>1p0SB1p0SF1p0SJ1p0SN1p0T21p0T61p0T:1p0T@1p0TD1p0TH1p0TO1p0U41p0U91p0U>1p0UB1p0UG1p0UM1p0V11p0V51p0V<1p0VF1p0VL1p0W21p0W91p0WB1p0WI1p0WO1p0X41p0X71p0X>1p0XA1p0XC1p0XE1p0XG1p0XK1p0XK1p0XN1p0Y01p0Y21p0Y41p0Y61p0Y;1p0YA1p0YH1p0YN1p0Z01p0Z51p0Z;1p0Z?1p0ZA1p0ZE1p0ZH1p0ZL1p0[01p0[41p0[>1p0[@1p0[D1p0[G1p0[O1p0\61p0\=1p0\@1p0\G1p0\O1p0]71p0]?1p0]J1pTD^71pTB^81pS4^91pSB^:1pS8^;1pSF^<1pSL^=1pT0^>1pSJ^?1pSH^@1pU4^A1pF^B1pT2^C1pS@^D1pTF^E1pT@^F1pT>^G1pUJ^O1pUH_01pUF_11pUD_21pUB_31pU@_41pU>_51pU<_61pUN_71pUL_81pU:_91pT<_41pQ0_51pT6_;1").
Proof.
intros regs M2 rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat msz r F tp nch nres q pab na cur mx bsl st16 st24.
intros H1 H2 H4 H8 H10 H21 Hret Hs Hs' Hm Hr Hrm Hri Hq Hsec Hsec' Hss Hst Hst8 HF HF' Hnch Hnres Hpi Hpab' APPr APPs ARs.
intros Hna Hna' Hcur Hcur' Hmx Hbsl Hbsl' H16 H16' H24a H24a' W1 W5 W6 W2 W7.
intros C104 C112 C120 C128 C136 C144 C38 CF Cnres Cnch Cpab Cna Ccur Cmx Cbsl C16 C24 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11.
assert (HL : 12 <= Z.log2 msz <= 46).
{ split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
pose proof (sec_b2_fn regs M2 rom s sec stat msz (63 - Z.log2 msz) nch nres r q F H1 H2 H8 H10 Hs Hs' Hr ltac:(lia) ltac:(lia) Hq
Hsec Hsec' ltac:(lia) Hst Hnch Hnres ltac:(lia) HF HF' W1 W5 C104 C112 C120 C128 C136 C144 C38 CF Cnres Cnch) as RUNB.
match type of RUNB with msteps _ _ (mkst ?R _ ?X _) => set (rb := R) in RUNB; set (MB := X) in RUNB end.
assert (AG : forall x : word, ~ (s - 148 <= U x < s - 144) -> ~ (sec + 48 <= U x < sec + 56) -> MB x = M2 x).
{ intros x Y1 Y2. pose proof (u64_range x). unfold MB. rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity. }
assert (G : mem_grows M2 MB) by (unfold MB; do 2 (eapply mem_grows_trans; [ | apply Wn_grows ]); apply mem_grows_refl).
assert (D1 : cellA MB (sec + 8) 8 pab) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cpab]).
assert (D2 : cellA MB (sec + 72) 8 na) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cna]).
assert (D3 : cellA MB (sec + 88) 8 cur) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Ccur]).
assert (D4 : cellA MB (sec + 96) 8 mx) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cmx]).
assert (D5 : cellA MB (sec + 104 + 8 * Z.log2 msz) 8 bsl) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cbsl]).
assert (D6 : cellA MB (stat + 16) 8 st16) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C16]).
assert (D7 : cellA MB (stat + 24) 8 st24) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C24]).
assert (E1 : cellA MB (s - 8) 8 (U x1)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L1]).
assert (E2 : cellA MB (s - 16) 8 (U x8)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L2]).
assert (E3 : cellA MB (s - 24) 8 (U x9)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L3]).
assert (E4 : cellA MB (s - 32) 8 (U x18)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L4]).
assert (E5 : cellA MB (s - 40) 8 (U x19)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L5]).
assert (E6 : cellA MB (s - 48) 8 (U x20)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L6]).
assert (E7 : cellA MB (s - 56) 8 (U x21)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L7]).
assert (E8 : cellA MB (s - 64) 8 (U x22)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L8]).
assert (E9 : cellA MB (s - 72) 8 (U x23)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L9]).
assert (E10 : cellA MB (s - 80) 8 (U x24)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L10]).
assert (E11 : cellA MB (s - 88) 8 (U x25)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L11]).
pose proof (sec_tail_fn rb MB rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat r msz nch pab na cur mx (Z.log2 msz) bsl st16 st24
ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity)
ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; exact H21)
Hret Hs Hs' ltac:(lia) Hr Hrm Hri Hsec Hss Hst Hst8 Hnch Hpi Hpab'
Hna Hna' Hcur Hcur' Hmx ltac:(lia) Hbsl Hbsl' H16 H16' H24a H24a' APPr APPs ARs
D1 D2 D3 D4 D5 D6 D7 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
ltac:(apply (wr_grows _ M2 MB _ _ G W2)) ltac:(apply (wr_grows _ M2 MB _ _ G W7))
ltac:(apply (wr_grows _ M2 MB _ _ G W5)) ltac:(apply (wr_grows _ M2 MB _ _ G W6))) as RUN9.
match type of RUN9 with msteps _ _ (mkst ?R _ _ _) => exists R end.
split; [ | zsplit ].
- eapply msteps_trans; [exact RUNB|]. unfold sec_postB_mem. subst MB rb. exact RUN9.
- unfold rb. gres. reflexivity.
- gres. reflexivity.
- gres. reflexivity.
- gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
- gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
- unfold rb. gres. exact H4.
- unfold rb. gres. reflexivity.
- unfold rb. gres. reflexivity.
- unfold rb. gres. reflexivity.
Qed.
End FPX.
