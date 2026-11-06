(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStepA PmStep PmParStep PmASrcKit PmCertKitG PmAImgGap PmAValP1 PmAValP2 PmAValP3 PmAValP4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAVal () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAVal.PMAVAL.Loop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "3Z"; "0HI"; "0KS"]; ["0L"; "4bvmap"; "0M"; "0Mv"; "0R"; "0R'"; "0R2"; "5msteps"; "6byte_at"; "7u8_at"; "8zeros_at"; "9KL"; "9VC"; "9goal_from"; "9vconst"; ":validate_spec"]; [";FPState"; ";getr"; ";mkst"; ";rdn"; ";seg_rom"; "<loaded_segments"; "0S"; "0SCFG_P"; "=eqb"; ">In"; ">existsb"; ">forallb"; "?add"; "?div"; "?land"; "?le"]; ["?lt"; "?modulo"; "?of_nat"; "?pow"; "?sub"; "0a"; "0ar"; "0b"; "0c"; "0c'"; "0d0"; "0e"; "0fx"; "0fx2"; "0k"; "0n"]; ["0nx"; "0p"; "0pc"; "0pc2"; "@Z_to_bv"; "@bv"; "0v"; "0w"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMAVAL.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmAVal "I'5'6%211';'3&Q;&Q:&Q8r1%211r2%53:21qSN;1%83<13(9%<3;21&Q9r4%23A:1%33B92p021pSND1p071pQ0E1p2F1").
Proof. intros A KS.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Ltac kin := apply sub_in; vm_compute; reflexivity.
Ltac kks KS := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; apply KS; revert k Hk; kin.
Lemma land7_le : ltac2:(TCodec.tc2 tcn__PmAVal "N'=':&Q?zr2%3221&Q@&QC+2+R0%3221%5271%;271&QAr3+8%3221%?21=&Q>r4%721:+7%4221%E2D1%F22:%H221p091p0?1pT@L1pTBM1").
Proof. intros x w.
intros H1 H2. rewrite (Z.mod_small x) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound x 8). lia.
Qed.
Lemma land7_le' : ltac2:(TCodec.tc2 tcn__PmAVal "F'=&Q?zr2%3221&QAr3+8%3221%8216':&Q>r4+7%3221%>2=1%?22:%7221p091p0?1pT@D1pTBE1").
Proof. intros x w. intros H1 H2. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. pose proof (Z.mod_pos_bound x 8). lia. Qed.
Lemma e6 : ltac2:(TCodec.tc2 tcn__PmAVal ":';'R5yR0%211&R4+_oooooooooomO%2241-R1%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Lemma e17 : ltac2:(TCodec.tc2 tcn__PmAVal ":';'R5yR0%211&R4+_oooooooooon2%2241-QN%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Lemma table_all : forallb (fun k => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (143869 + Z.of_nat k)) 1 with Some [_] => true | _ => false end) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma table_ok : ltac2:(TCodec.tc2 tcn__PmAVal "Q<'=':&Q?zr1%3221+WO%5231%7231'<'R5y8%211';'8'5%114%311&Q3&Q5yR0%;11(1%11;q031&R4&Q<+T\_Mr3%3221%52:1u1%>4=821(2(4(7%11H%33IQ11%52F1%J3F71qS@L1%Q02M1p0Q21pSNQ;1").
Proof. intros k.
intros Hk. pose proof table_all as T. rewrite forallb_forall in T. specialize (T (Z.to_nat k) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in T by lia. destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (143869 + k)) 1) as [[|b [|]]|]; try discriminate. exists b. reflexivity.
Qed.
Section Loop.
Variable Mv : word -> option byte.
Variables (S p e : Z).
Hypothesis IMG : L5.img_clear Mv 65536 1261568.
Hypothesis HS : 140735332487264 <= S <= 2 ^ 47.
Hypothesis Hp : 0 <= p.
Hypothesis Hpe : p <= e.
Hypothesis He : e <= 2 ^ 47.
Hypothesis Hn : e - p <= 2 ^ 26.
Hypothesis BY : forall c, p <= c < e -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS Mv c b.
Hypothesis SH : forall c, p <= c < e -> L5KA.zeros_at Mv (c / 8 + 2147450880) 1 \/ (exists v, 1 <= v <= 7 /\ L5.u8_at RSEGS Mv (c / 8 + 2147450880) v /\ c mod 8 < v).
Hypothesis GAP1 : L5KA.zeros_at Mv 2147468860 44.
Definition vconst (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 96) /\ getr R (reg 5) = Z_to_bv 64 245 /\ getr R (reg 6) = Z_to_bv 64 (-65) /\ getr R (reg 7) = Z_to_bv 64 239
/\ getr R (reg 8) = Z_to_bv 64 240 /\ getr R (reg 9) = Z_to_bv 64 144 /\ getr R (reg 14) = Z_to_bv 64 e /\ getr R (reg 15) = Z_to_bv 64 8
/\ getr R (reg 16) = Z_to_bv 64 1 /\ getr R (reg 17) = Z_to_bv 64 (-62) /\ getr R (reg 18) = Z_to_bv 64 2147450880 /\ getr R (reg 19) = Z_to_bv 64 244
/\ getr R (reg 20) = Z_to_bv 64 143 /\ getr R (reg 21) = Z_to_bv 64 2 /\ getr R (reg 22) = Z_to_bv 64 3 /\ getr R (reg 28) = Z_to_bv 64 224
/\ getr R (reg 29) = Z_to_bv 64 160 /\ getr R (reg 30) = Z_to_bv 64 237 /\ getr R (reg 31) = Z_to_bv 64 159.
Definition VC : list nat := [2; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31]%nat.
Lemma vconst_keep : ltac2:(TCodec.tc2 tcn__PmAVal "Q1&Ay5'R5yR0%211%5241&Nr2%211'6&Q9r1&L%33421';&Q1r4&R4&QB%11<%32C1%6251r5%8213%:3D31p0<1pSNA1r3%F11p031p0F1pQ<J1pQ:K1").
Proof. intros R R'.
intros (C2 & C5 & C6 & C7 & C8 & C9 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31) K.
unfold vconst. rewrite !K by (cbn; tauto). repeat split; assumption.
Qed.
Definition KL : list nat := [1; 3; 4; 27]%nat.
Definition goal_from (fx : FPState) (R : bvmap 5 word) (pc : Z) : Prop :=
exists fx' R', msteps RSEGS (L5SAR.st fx R pc Mv) (L5SAR.st fx' R' 0xafdb8 Mv) /\ getr R' (reg 2) = Z_to_bv 64 (S - 96)
/\ (forall k, In k KL -> getr R' (reg k) = getr R (reg k)).
Lemma goal_pre : ltac2:(TCodec.tc2 tcn__PmAVal "QG'Q0&Ay5'R5yR0%211%5241'='G&Q5&Q2r6r5&R4r4%22;1vC&Q4%119%9587431r3r2r1%:2C1%>543186%A3@61'6&Q9&K%23371';&Q1&QB%11<%E2Q01%42G1r8%6213%83Q131p0:1pSN>1&M%13NLFr9r7%43291p041p071p0G1pT8Q:1pQ>Q<1pSLQC1pT6Q=1pQ:Q?1pSJQF1").
Proof. intros fx R pc fx2 R2 pc2.
intros MS KS (fx3 & R3 & MS3 & SP3 & KS3). exists fx3, R3. split; [eapply msteps_trans; [exact MS| exact MS3]|]. split; [exact SP3|].
intros k Hk. rewrite (KS3 k Hk). apply KS. exact Hk.
Qed.
Lemma goal_epi : ltac2:(TCodec.tc2 tcn__PmAVal "QO'Q0&Ay5'R5yR0%211%5241'='G&Q5&Q2r5r4&R4r3%22;1vC&Q4%119%9587431r2r1+eo]H%:2C1%>543186%A3@61'6&Q9&K%23381';&Q1&QB%11=%E2Q01%42G1r7%6213%83Q131p0:1pSN>1u2%:11%N2Q91%=2N1&QDvQ6+S0%3221%Q42Q=1%D3Q=61&Mr8r6%332B1p051p0@1p0Q01pQ>QD1pSLQK1pT6QE1pQ:QG1pSJQN1").
Proof. intros fx R pc fx2 R2. intros MS KS SP. exists fx2, R2. split; [exact MS|]. split; [exact SP| exact KS]. Qed.
Ltac sc := first [ assumption | lia | (rewrite Zplus_minus; assumption) | (apply land7_le; lia) | (apply land7_le'; lia) ].
Ltac vfacts V := let C2 := fresh "C2" in
pose proof V as (C2 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C14 & ?C15 & ?C16 & ?C17 & ?C18 & ?C19 & ?C20 & ?C21 & ?C22 & ?C28 & ?C29 & ?C30 & ?C31).
Ltac runp X fx R VAL :=
let PP := fresh "PP" in let fx1 := fresh "fx" in let R1 := fresh "R" in let M1 := fresh "M" in let FR := fresh "FR" in
pose proof (X fx R Mv VAL) as PP; cbn beta iota in PP; L5SAR.feed PP ltac:(sc);
destruct PP as (fx1 & R1 & M1 & _ & FR & _ & EX); (assert (M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1.
Ltac runpk X fx R VAL K :=
let PP := fresh "PP" in let fx1 := fresh "fx" in let R1 := fresh "R" in let M1 := fresh "M" in let FR := fresh "FR" in let EX := fresh "EX" in
pose proof (X fx R Mv VAL) as PP; cbn beta iota in PP; L5SAR.feed PP ltac:(sc);
destruct PP as (fx1 & R1 & M1 & _ & FR & _ & EX); (assert (M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1; K EX.
Ltac epi_exit V := lazymatch goal with
| MS : msteps _ (L5SAR.st ?fx ?R _ _) (L5SAR.st ?fx1 ?R1 0xafdb8 _), KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x) |- goal_from ?fx ?R _ =>
apply (goal_epi fx R _ fx1 R1 MS); [kks KS| rewrite (KS 2%nat) by inl; exact (proj1 V)]
end.
Ltac msks EX := let MS := fresh "MS" in let KS := fresh "KS" in let EXR := fresh "EXR" in
lazymatch type of EX with
| _ /\ _ /\ _ => destruct EX as (MS & KS & EXR); lazymatch type of EXR with _ /\ _ => decompose [and] EXR; clear EXR | _ => idtac end
| _ /\ _ => destruct EX as (MS & KS)
end.
Ltac gpre := lazymatch goal with
| MS : msteps _ (L5SAR.st ?fx ?R _ _) (L5SAR.st ?fx1 ?R1 _ _), KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x) |- goal_from ?fx ?R _ =>
apply (goal_pre fx R _ fx1 R1 _ MS ltac:(kks KS))
end.
Ltac vk V := lazymatch goal with
| KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x), V0 : vconst ?R |- vconst ?R1 => exact (vconst_keep R R1 V0 ltac:(kks KS))
end.
Ltac kept k H := lazymatch goal with KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x) |- getr ?R1 _ = _ => rewrite (KS k) by inl; exact H end.
Ltac vsplit v Hv := let HV := fresh "HV" in assert (HV : v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) by lia;
destruct HV as [->|[->|[->|[->|[->|[->| ->]]]]]].
Section IH.
Variable c : Z.
Hypothesis IH : forall fx R c', c < c' < e -> vconst R -> getr R (reg 12) = Z_to_bv 64 c' -> goal_from fx R 0xafb14.
Lemma back_case : ltac2:(TCodec.tc2 tcn__PmAVal "Q>'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221&Q@r1%2241%8241r2vQK%:221&Nr4%211';&Q1r5&R4&QBu<%211%42L1%7261%62L;%:3L21&Mr7r6+eoWL%43321p061p0B1p0F1p0J1pSDQ41pQ:Q61pSJQ=1").
Proof using All. intros fx R c'.
intros Hc Hc' V R12. vfacts V.
runp PMAVALP1.avlB_conc fx R (fun j => match j with 2%nat => S | 33%nat => c' | 35%nat => e - c' | _ => 0 end).
destruct EX as [EX|EX]; msks EX.
- epi_exit V.
- lazymatch goal with NE : 1 <= _ |- _ =>
assert (LT : c' < e) by (rewrite Zplus_minus in NE; rewrite (Z.mod_small e) in NE by lia;
destruct (Z.eq_dec c' e) as [->|X]; [rewrite Z.sub_diag, Z.mod_0_l in NE by lia; lia| lia]) end.
gpre. apply (IH _ _ c' ltac:(lia)); [vk V| kept 12%nat R12].
Qed.
Local Ltac lexit V nx R12 := lazymatch goal with
| MS : msteps _ _ (L5SAR.st _ _ 0xafdb8 _) |- _ => epi_exit V
| _ => gpre; apply (back_case _ _ nx ltac:(lia) ltac:(lia)); [vk V| kept 12%nat R12]
end.
Lemma lead_case : ltac2:(TCodec.tc2 tcn__PmAVal "R9'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r3%5231%7231&Q@r4%2215vQK%;271%=231r5%7214z%@218+WO%B2:1%D231&Nr8%211';&Q1r9&R4&QBu:%211%42Q51%7261%62Q5;%:3Q521r:u<%911%;2Q<1%>241%@3Q;17r;uH%?11%A2QB1%D241%F3QA1=&Mr=r<+eoU@%43321p061p0=1p0D1p0Q01p0Q41p0Q:1p0Q=1p0QD1pS@QM1pT2QN1pSFQO1pQ:R11pSJR81").
Proof using All. intros fx R d0 nx b.
intros Hc Hnx Hd Hb V R10 R12 R24. vfacts V.
set (s7 := bv_unsigned (getr R (reg 23))). set (a1 := bv_unsigned (getr R (reg 11))).
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as Hs7. pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as Ha1. change (bv_modulus 64) with (2 ^ 64) in Hs7, Ha1.
assert (R23 : getr R (reg 23) = Z_to_bv 64 s7) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (R11 : getr R (reg 11) = Z_to_bv 64 a1) by (symmetry; apply Z_to_bv_bv_unsigned).
runp PMAVALP1.avlL_conc fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => nx | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | 39%nat => a1 | _ => 0 end).
repeat (destruct EX as [EX|EX]; [msks EX; lexit V nx R12|]); msks EX; lexit V nx R12.
Qed.
Local Ltac r1v X d0 nx b b1 s7 V R10 R12 R24 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => nx | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | 39%nat => b1 | _ => 0 end) ltac:(fun EX =>
destruct EX as [EX|EX]; msks EX;
[ epi_exit V
| gpre; apply (lead_case _ _ d0 nx b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10| kept 12%nat R12| kept 24%nat R24] ])
end.
Lemma r1_case : ltac2:(TCodec.tc2 tcn__PmAVal "RF'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r3%5231%7231&Q<r4+2%3221vQK%<221&Q@r5%2217%@285%B221z%C21;+WO%E2=1%G231&Nr8%211';&Q1r9&R4&QBu:%211%42Q81%7261%62Q8;%:3Q821r:u=%911%;2Q?1%>241%Q32>Q1%>2Q@1%B3Q@31r;u<%A11%C2QG1%F241%E2QGF%I3QG21r<uH%H11%J2QN1%M241%O3QM17&Mr>r=+eoTD%43321p061p0=1p0E1p0N1p0Q:1p0Q>1p0QD1p0QJ1p0R11pS@R:1pT2R;1pSFR<1pQ:R>1pSJRE1").
Proof using All. intros fx R d0 nx b.
intros Hc Hd Hnx Hb V R10 R13 R12 R24. vfacts V.
set (s7 := bv_unsigned (getr R (reg 23))). pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as Hs7. change (bv_modulus 64) with (2 ^ 64) in Hs7.
assert (R23 : getr R (reg 23) = Z_to_bv 64 s7) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (BY (d0 + 1) ltac:(lia)) as (b1 & Hb1 & U1).
destruct (SH (d0 + 1) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
- r1v PMAVALP4.avlR1Z_conc d0 nx b b1 s7 V R10 R12 R24.
- vsplit v Hv.
+ r1v PMAVALP4.avlR1P1_conc d0 nx b b1 s7 V R10 R12 R24.
+ r1v PMAVALP4.avlR1P2_conc d0 nx b b1 s7 V R10 R12 R24.
+ r1v PMAVALP4.avlR1P3_conc d0 nx b b1 s7 V R10 R12 R24.
+ r1v PMAVALP4.avlR1P4_conc d0 nx b b1 s7 V R10 R12 R24.
+ r1v PMAVALP4.avlR1P5_conc d0 nx b b1 s7 V R10 R12 R24.
+ r1v PMAVALP4.avlR1P6_conc d0 nx b b1 s7 V R10 R12 R24.
+ r1v PMAVALP4.avlR1P7_conc d0 nx b b1 s7 V R10 R12 R24.
Qed.
Local Ltac r2v X d0 nx b b2 s7 V R10 R12 R24 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => nx | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | 39%nat => b2 | _ => 0 end) ltac:(fun EX =>
destruct EX as [EX|EX]; msks EX;
[ epi_exit V
| gpre; apply (r1_case _ _ d0 nx b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10| assumption| kept 12%nat R12| kept 24%nat R24] ])
end.
Lemma r2_case : ltac2:(TCodec.tc2 tcn__PmAVal "RF'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r3%5231%7231&Q<r4+3%3221vQK%<221&Q@r5%2217%@285%B221z%C21;+WO%E2=1%G231&Nr8%211';&Q1r9&R4&QBu:%211%42Q81%7261%62Q8;%:3Q821r:uJ%911%;2Q?1%>241%Q32>Q1%>2Q@1%B3Q@31r;u<%A11%C2QG1%F241%E2QGF%I3QG21r<uH%H11%J2QN1%M241%O3QM17&Mr>r=+eoSH%43321p061p0=1p0E1p0N1p0Q:1p0Q>1p0QD1p0QJ1p0R11pS@R:1pT2R;1pSFR<1pQ:R>1pSJRE1").
Proof using All. intros fx R d0 nx b.
intros Hc Hd Hnx Hb V R10 R26 R12 R24. vfacts V.
set (s7 := bv_unsigned (getr R (reg 23))). pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as Hs7. change (bv_modulus 64) with (2 ^ 64) in Hs7.
assert (R23 : getr R (reg 23) = Z_to_bv 64 s7) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (BY (d0 + 2) ltac:(lia)) as (b2 & Hb2 & U2).
destruct (SH (d0 + 2) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
- r2v PMAVALP4.avlR2Z_conc d0 nx b b2 s7 V R10 R12 R24.
- vsplit v Hv.
+ r2v PMAVALP4.avlR2P1_conc d0 nx b b2 s7 V R10 R12 R24.
+ r2v PMAVALP4.avlR2P2_conc d0 nx b b2 s7 V R10 R12 R24.
+ r2v PMAVALP4.avlR2P3_conc d0 nx b b2 s7 V R10 R12 R24.
+ r2v PMAVALP4.avlR2P4_conc d0 nx b b2 s7 V R10 R12 R24.
+ r2v PMAVALP4.avlR2P5_conc d0 nx b b2 s7 V R10 R12 R24.
+ r2v PMAVALP4.avlR2P6_conc d0 nx b b2 s7 V R10 R12 R24.
+ r2v PMAVALP4.avlR2P7_conc d0 nx b b2 s7 V R10 R12 R24.
Qed.
Local Ltac r3v X d0 b b3 s7 V R10 R12 R24 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | 39%nat => b3 | _ => 0 end) ltac:(fun EX =>
destruct EX as [EX|EX]; msks EX;
[ epi_exit V
| gpre; apply (r2_case _ _ d0 (d0 + 4) b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10| assumption| kept 12%nat R12| kept 24%nat R24] ])
end.
Lemma r3_case : ltac2:(TCodec.tc2 tcn__PmAVal "RK'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r2%5231%7231&Q<r3+4%3221vQK%<221z%>216+WO%@281%B231&Nr6%211';&Q1r7&R4&QBu:%211%42Q31%7261%62Q3;%:3Q321r8u=%911%;2Q:1%>241+3%O2?1%?2Q<1%C3Q<41r9u<%B11%D2QC1%G241%Q72>Q5%G2QD1%K3QD31r:uJ%J11%L2QK1%O241%Q?2=Q=%O2QL1%Q33QL31r;uH%Q211%Q42R31%Q7241%Q62R3E%Q:3R321&Mr=r<+eoRL%43321p061p0>1p0G1p0Q01p0Q:1p0QF1p0QJ1p0R01p0R71pS@R@1pSFRA1pQ:RC1pSJRJ1").
Proof using All. intros fx R d0 b.
intros Hc Hd Hb V R10 R13 R12 R26 R24. vfacts V.
set (s7 := bv_unsigned (getr R (reg 23))). pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as Hs7. change (bv_modulus 64) with (2 ^ 64) in Hs7.
assert (R23 : getr R (reg 23) = Z_to_bv 64 s7) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (BY (d0 + 3) ltac:(lia)) as (b3 & Hb3 & U3).
destruct (SH (d0 + 3) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
- r3v PMAVALP4.avlR3Z_conc d0 b b3 s7 V R10 R12 R24.
- vsplit v Hv.
+ r3v PMAVALP4.avlR3P1_conc d0 b b3 s7 V R10 R12 R24.
+ r3v PMAVALP4.avlR3P2_conc d0 b b3 s7 V R10 R12 R24.
+ r3v PMAVALP4.avlR3P3_conc d0 b b3 s7 V R10 R12 R24.
+ r3v PMAVALP4.avlR3P4_conc d0 b b3 s7 V R10 R12 R24.
+ r3v PMAVALP4.avlR3P5_conc d0 b b3 s7 V R10 R12 R24.
+ r3v PMAVALP4.avlR3P6_conc d0 b b3 s7 V R10 R12 R24.
+ r3v PMAVALP4.avlR3P7_conc d0 b b3 s7 V R10 R12 R24.
Qed.
Definition L2 : list nat := [2; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31; 1; 3; 4; 27; 10; 23]%nat.
Lemma slow : ltac2:(TCodec.tc2 tcn__PmAVal "Q>'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r1%5231%7231&Q@r2vQK%3221&Nr4%211';&Q1r5&R4&QBu:%211%42L1%7261%62L;%:3L21&Mr7r6+eoP4%43321p061p0B1p0F1p0K1pSFQ41pQ:Q61pSJQ=1").
Proof using All. intros fx R d0.
intros Hc Hd V R10. vfacts V.
set (s7 := bv_unsigned (getr R (reg 23))). pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as Hs7. change (bv_modulus 64) with (2 ^ 64) in Hs7.
assert (R23 : getr R (reg 23) = Z_to_bv 64 s7) by (symmetry; apply Z_to_bv_bv_unsigned).
runp PMAVALP1.avlS_conc fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | _ => 0 end).
destruct EX as (MS1 & KS1 & A11 & A12 & A24).
lazymatch type of MS1 with msteps _ _ (L5SAR.st ?f ?r _ _) => rename f into fx1; rename r into R1 end.
set (b := Z.land s7 255) in *.
assert (Hb : 0 <= b <= 255).
{ pose proof (PMAVALP1.land_byte s7 255 ltac:(lia) ltac:(lia)) as X. unfold b. lia. }
rewrite Z.mod_small in A11 by lia.
destruct (table_ok b Hb) as (tb & TB).
assert (L1 : (25%bv : bv 5) <> 0%bv) by discriminate.
assert (LL2 : getr R1 (11%bv : bv 5) = Z_to_bv 64 (b + 143869)) by (rewrite <- A11; symmetry; apply Z_to_bv_bv_unsigned).
assert (L3 : rdn RSEGS Mv (Z_to_bv 64 (b + 143869 + bv_signed (0%bv : bv 12))) 1 = Some [tb]).
{ change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r, Z.add_comm. rewrite (PMCG.rdn_img RSEGS Mv 65536 1261568 _ 1 IMG) by lia. exact TB. }
pose proof (PMCG.lbu_img_run RSEGS fx1 R1 Mv 0xafc24 (ltac:(oW' 0xafc24%Z)) 25%bv 11%bv 0%bv (b + 143869) tb (ltac:(oF' 0xafc24%Z)) eq_refl (ltac:(oD' 0xafc24%Z)) L1 ltac:(lia) ltac:(lia) LL2 ltac:(lia)
ltac:(change (bv_signed (0%bv : bv 12)) with 0; lia) L3) as MSl.
set (R2 := regupd R1 25%bv (Z_to_bv 64 (bv_unsigned tb))) in MSl.
assert (RU : forall k, k <> 25%nat -> (k < 32)%nat -> getr R2 (reg k) = getr R1 (reg k)).
{ intros k Hk Hk32. unfold R2. replace (25%bv : bv 5) with (reg 25) by (apply bv_eq; reflexivity). apply PMPX.regupd_other_idx; lia. }
assert (R25 : getr R2 (reg 25) = Z_to_bv 64 (bv_unsigned tb)).
{ unfold R2. replace (25%bv : bv 5) with (reg 25) by (apply bv_eq; reflexivity). apply PMPX.regupd_same_idx. lia. }
pose proof (bv_unsigned_in_range 8 tb) as Htb. change (bv_modulus 8) with 256 in Htb.
assert (KS2 : forall k, In k L2 -> getr R2 (reg k) = getr R (reg k)).
{ intros k Hk. unfold L2 in Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite RU by lia; apply KS1; inl|]). destruct Hk. }
assert (V2 : vconst R2) by exact (vconst_keep R R2 V ltac:(kks KS2)).
assert (R2_10 : getr R2 (reg 10) = Z_to_bv 64 d0) by (rewrite KS2 by inl; exact R10).
assert (R2_23 : getr R2 (reg 23) = Z_to_bv 64 s7) by (rewrite KS2 by inl; exact R23).
assert (R2_24 : getr R2 (reg 24) = Z_to_bv 64 b) by (rewrite RU by lia; rewrite <- A24; symmetry; apply Z_to_bv_bv_unsigned).
apply (goal_pre fx R 0xafc04 fx1 R2 (0xafc24 + 4)).
{ eapply msteps_trans; [exact MS1| exact MSl]. }
{ kks KS2. }
change (0xafc24 + 4) with 0xafc28.
clear MS1 MSl KS1 KS2 A11 A12 A24 RU.
pose proof V2 as (D2 & D5 & D6 & D7 & D8 & D9 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D28 & D29 & D30 & D31).
set (t := bv_unsigned tb) in *.
assert (CASES : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ 4 <= t) by lia.
destruct CASES as [Et|[Et|[Et|[Et|Et]]]].
- rewrite Et in R25.
runp PMAVALP1.avlT0_conc fx1 R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | _ => 0 end).
destruct EX as [EX|[EX|EX]]; msks EX.
+ epi_exit V2.
+ gpre. apply (back_case _ _ (d0 + 1) ltac:(lia) ltac:(lia)); [vk V2| assumption].
+ epi_exit V2.
- rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 1) as [LE|GT].
+ runp PMAVALP1.avlT1a_conc fx1 R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | _ => 0 end).
msks EX. epi_exit V2.
+ runp PMAVALP1.avlT1b_conc fx1 R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | _ => 0 end).
msks EX. gpre.
apply (r1_case _ _ d0 (d0 + 2) b ltac:(lia) ltac:(lia) ltac:(lia) Hb); [vk V2| kept 10%nat R2_10| assumption| assumption| kept 24%nat R2_24].
- rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 2) as [LE|GT].
+ runp PMAVALP1.avlT2a_conc fx1 R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | _ => 0 end).
msks EX. epi_exit V2.
+ runp PMAVALP1.avlT2b_conc fx1 R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | _ => 0 end).
msks EX. gpre.
apply (r2_case _ _ d0 (d0 + 3) b ltac:(lia) ltac:(lia) ltac:(lia) Hb); [vk V2| kept 10%nat R2_10| assumption| assumption| kept 24%nat R2_24].
- rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 3) as [LE|GT].
+ runp PMAVALP1.avlT3a_conc fx1 R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | _ => 0 end).
msks EX. epi_exit V2.
+ runp PMAVALP1.avlT3b_conc fx1 R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | _ => 0 end).
msks EX. gpre.
apply (r3_case _ _ d0 b ltac:(lia) ltac:(lia) Hb); [vk V2| kept 10%nat R2_10| assumption| assumption| assumption| kept 24%nat R2_24].
- runp PMAVALP1.avlTbig_conc fx1 R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s7 | 37%nat => b | 38%nat => t | _ => 0 end).
destruct EX as [EX|EX]; msks EX; epi_exit V2.
Qed.
Local Ltac fv X k NEXT b V R12 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b | _ => 0 end) ltac:(fun EX =>
destruct EX as [EX|EX]; msks EX;
[ gpre; lazymatch goal with A10 : getr _ (reg 10) = Z_to_bv 64 (c + k) |- _ => apply (slow _ _ (c + k) ltac:(lia) ltac:(lia)); [vk V| exact A10] end
| NEXT ])
end.
Local Ltac fnext FN V R12 := gpre; apply (FN _ _ ltac:(lia) ltac:(lia)); [vk V| kept 12%nat R12].
Local Ltac fback V := gpre; apply (back_case _ _ (c + 8) ltac:(lia) ltac:(lia)); [vk V| assumption].
Local Ltac fcases Z P1 P2 P3 P4 P5 P6 P7 k NEXT :=
lazymatch goal with V : vconst ?R, R12 : getr ?R (reg 12) = _ |- goal_from _ ?R _ =>
vfacts V;
let b := fresh "b" in let Hb := fresh "Hb" in let U := fresh "U" in
destruct (BY (c + k) ltac:(lia)) as (b & Hb & U);
destruct (SH (c + k) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)];
[ fv Z k NEXT b V R12
| vsplit v Hv; [ fv P1 k NEXT b V R12 | fv P2 k NEXT b V R12 | fv P3 k NEXT b V R12 | fv P4 k NEXT b V R12
| fv P5 k NEXT b V R12 | fv P6 k NEXT b V R12 | fv P7 k NEXT b V R12 ] ]
end.
Lemma fast7 : ltac2:(TCodec.tc2 tcn__PmAVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu<%211%42H1%7261%62HC%:3H21&Mr6r5+ennL%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R12.
fcases PMAVALP3.avlF7Z_conc PMAVALP3.avlF7P1_conc PMAVALP3.avlF7P2_conc PMAVALP3.avlF7P3_conc PMAVALP3.avlF7P4_conc PMAVALP3.avlF7P5_conc
PMAVALP3.avlF7P6_conc PMAVALP3.avlF7P7_conc 7 ltac:(fback V).
Qed.
Lemma fast6 : ltac2:(TCodec.tc2 tcn__PmAVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu<%211%42H1%7261%62HC%:3H21&Mr6r5+enn0%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R12.
fcases PMAVALP3.avlF6Z_conc PMAVALP3.avlF6P1_conc PMAVALP3.avlF6P2_conc PMAVALP3.avlF6P3_conc PMAVALP3.avlF6P4_conc PMAVALP3.avlF6P5_conc
PMAVALP3.avlF6P6_conc PMAVALP3.avlF6P7_conc 6 ltac:(fnext fast7 V R12).
Qed.
Lemma fast5 : ltac2:(TCodec.tc2 tcn__PmAVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu<%211%42H1%7261%62HC%:3H21&Mr6r5+enm4%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R12.
fcases PMAVALP3.avlF5Z_conc PMAVALP3.avlF5P1_conc PMAVALP3.avlF5P2_conc PMAVALP3.avlF5P3_conc PMAVALP3.avlF5P4_conc PMAVALP3.avlF5P5_conc
PMAVALP3.avlF5P6_conc PMAVALP3.avlF5P7_conc 5 ltac:(fnext fast6 V R12).
Qed.
Lemma fast4 : ltac2:(TCodec.tc2 tcn__PmAVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu<%211%42H1%7261%62HC%:3H21&Mr6r5+enl8%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R12.
fcases PMAVALP2.avlF4Z_conc PMAVALP2.avlF4P1_conc PMAVALP2.avlF4P2_conc PMAVALP2.avlF4P3_conc PMAVALP2.avlF4P4_conc PMAVALP2.avlF4P5_conc
PMAVALP2.avlF4P6_conc PMAVALP2.avlF4P7_conc 4 ltac:(fnext fast5 V R12).
Qed.
Lemma fast3 : ltac2:(TCodec.tc2 tcn__PmAVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu<%211%42H1%7261%62HC%:3H21&Mr6r5+enk<%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R12.
fcases PMAVALP2.avlF3Z_conc PMAVALP2.avlF3P1_conc PMAVALP2.avlF3P2_conc PMAVALP2.avlF3P3_conc PMAVALP2.avlF3P4_conc PMAVALP2.avlF3P5_conc
PMAVALP2.avlF3P6_conc PMAVALP2.avlF3P7_conc 3 ltac:(fnext fast4 V R12).
Qed.
Lemma fast2 : ltac2:(TCodec.tc2 tcn__PmAVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu<%211%42H1%7261%62HC%:3H21&Mr6r5+enj@%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R12.
fcases PMAVALP2.avlF2Z_conc PMAVALP2.avlF2P1_conc PMAVALP2.avlF2P2_conc PMAVALP2.avlF2P3_conc PMAVALP2.avlF2P4_conc PMAVALP2.avlF2P5_conc
PMAVALP2.avlF2P6_conc PMAVALP2.avlF2P7_conc 2 ltac:(fnext fast3 V R12).
Qed.
Lemma fast1 : ltac2:(TCodec.tc2 tcn__PmAVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu<%211%42H1%7261%62HC%:3H21&Mr6r5+eniD%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R12.
fcases PMAVALP2.avlF1Z_conc PMAVALP2.avlF1P1_conc PMAVALP2.avlF1P2_conc PMAVALP2.avlF1P3_conc PMAVALP2.avlF1P4_conc PMAVALP2.avlF1P5_conc
PMAVALP2.avlF1P6_conc PMAVALP2.avlF1P7_conc 1 ltac:(fnext fast2 V R12).
Qed.
End IH.
Lemma granule0 : ltac2:(TCodec.tc2 tcn__PmAVal "G'=&Q?vR1r1%3221&Q<r2+8%3221vQK%9221&JvC&Q=r3%2218+QoooPP0%<221+1%83721p0:1p0A1pSBF1").
Proof using All. intros c.
intros H1 H2. set (a := c + (7 - c mod 8)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hm.
pose proof (Z.div_mod c 8 ltac:(lia)) as Dm.
assert (Ea : a / 8 = c / 8).
{ unfold a. replace (c + (7 - c mod 8)) with (7 + (c / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
assert (Ma : a mod 8 = 7).
{ unfold a. replace (c + (7 - c mod 8)) with (7 + (c / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
destruct (SH a ltac:(unfold a; lia)) as [Z0 | (v & Hv & _ & Hav)]; [rewrite Ea in Z0; exact Z0| lia].
Qed.
Local Ltac hs X c b0 V IH :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b0 | _ => 0 end) ltac:(fun EX =>
msks EX; gpre;
lazymatch goal with A10 : getr _ (reg 10) = Z_to_bv 64 c |- _ => apply (slow c IH _ _ c ltac:(lia) ltac:(lia)); [vk V| exact A10] end)
end.
Lemma loop_head : ltac2:(TCodec.tc2 tcn__PmAVal "QB'6'Q0&Ay5'R5yR0%211%5241'=';&QBr4%211&QDvQKr1%3221%83951':&Q?vR1r2%3221&Q@%123:%7231&N%11@&Q1r5&R4u<%F11%32N1%6251%52NH%K3N21&Mr7r6+enhD%43321p061p0@1p0C1p0L1pSBQ61pQ:Q81pSJQ?1pT0QA1").
Proof using All.
intros n. induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf). intros fx R c Hn' Hc V R12.
assert (IH : forall fx R c', c < c' < e -> vconst R -> getr R (reg 12) = Z_to_bv 64 c' -> goal_from fx R 0xafb14).
{ intros fx' R' c' Hc' V' R12'. apply (IHn (Z.to_nat (e - c')) ltac:(lia) fx' R' c'); [lia| lia| exact V'| exact R12']. }
vfacts V.
destruct (BY c ltac:(lia)) as (b0 & Hb0 & U0).
destruct (Z_le_gt_dec 8 (e - c)) as [GE|LT].
- pose proof (granule0 c ltac:(lia) ltac:(lia)) as Z0.
runp PMAVALP1.avlHf_conc fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b0 | _ => 0 end).
destruct EX as [EX|EX]; msks EX; gpre.
+ lazymatch goal with A10 : getr _ (reg 10) = Z_to_bv 64 c |- _ => apply (slow c IH _ _ c ltac:(lia) ltac:(lia)); [vk V| exact A10] end.
+ apply (fast1 c IH _ _ ltac:(lia) ltac:(lia)); [vk V| kept 12%nat R12].
- destruct (SH c ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
+ hs PMAVALP1.avlHsZ_conc c b0 V IH.
+ vsplit v Hv.
* hs PMAVALP1.avlHsP1_conc c b0 V IH.
* hs PMAVALP1.avlHsP2_conc c b0 V IH.
* hs PMAVALP1.avlHsP3_conc c b0 V IH.
* hs PMAVALP1.avlHsP4_conc c b0 V IH.
* hs PMAVALP1.avlHsP5_conc c b0 V IH.
* hs PMAVALP1.avlHsP6_conc c b0 V IH.
* hs PMAVALP1.avlHsP7_conc c b0 V IH.
Qed.
End Loop.
Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis GAP : PMAGAP.rt_img_gap HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma u8_of_byte : ltac2:(TCodec.tc2 tcn__PmAVal "F'R5yR0%211'8y8%511%311p051'=&Hr3r2r1%43321&I&Q5r4%342176p051pT>;1pS<<1pQ6>1").
Proof. intros M a v. intros B. unfold L5.u8_at. cbn [rdn]. unfold byte_at in B. rewrite B. reflexivity. Qed.
Theorem validate_ok : ltac2:(TCodec.tc2 tcn__PmAVal "6&OvQ7v@vQFv>%544321").
Proof.
unfold PMA.validate_spec, PMSPA.validate_spec, PMSPA.scan_spec. cbn [pa_validate PMA.AD ADDR_A].
intros fx R M model K LB FF LK Aw cr p n sp r HH AM K0 ENT FRM FRS A10 A11 Hn Hp Hp0 Hpn DEF ACC VIS LOC BASE KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
change (PMSPA.pm_scr 0) with 12288 in *.
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 12288 96 HH ASTK ltac:(lia)) as (SL96 & SH96 & V3).
pose proof (PMAGAP.gap_vis HI GAP LB FF LK cr Aw M model HH) as GZ.
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (V0' : L5.img_clear MV 1228800 1261568) by (intros i Hi; apply V0; lia).
cfeed PP (PMAVALP1.avlE_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | 35%nat => n | _ => 0 end)) ltac:(first [assumption | unfold PMAVALP1.aligned; lia | lia]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
set (P := fun a => sp - 96 <= a < sp - 96 + 96).
assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
assert (NPs : forall c, 0 <= c < 2 ^ 47 -> ~ P (c / 8 + 2147450880)).
{ intros c Hc. unfold P. assert (c / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). assert (0 <= c / 8) by (apply Z.div_pos; lia). lia. }
assert (NPb : forall c, p <= c < p + n -> ~ P c).
{ intros c Hc. unfold P. destruct LOC as [X|[X|X]]; lia. }
assert (IMG1 : L5.img_clear M1v 65536 1261568).
{ intros i Hi. rewrite AG1 by (unfold P; lia). apply V0. exact Hi. }
assert (BY1 : forall c, p <= c < p + n -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS M1v c b).
{ intros c Hc. destruct (VIS c Hc) as (Vc & _).
assert (DV : L5.defined MV c 1).
{ apply (proj2 (L5A.defined_vis H M c 1 ltac:(intros i Hi; replace (c + i) with c by lia; exact Vc))). apply (L5.defined_sub M p n); [exact DEF| lia| lia]. }
destruct (PMCG.u8_of_defined RSEGS MV c ltac:(lia) ltac:(lia) DV) as (b & Hb & Ub). exists b. split; [lia|].
apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; rewrite AG1; [reflexivity| lia| apply NPb; lia]| lia| lia| exact Ub]. }
assert (SH1 : forall c, p <= c < p + n -> L5KA.zeros_at M1v (c / 8 + 2147450880) 1
\/ (exists v, 1 <= v <= 7 /\ L5.u8_at RSEGS M1v (c / 8 + 2147450880) v /\ c mod 8 < v)).
{ intros c Hc. destruct (VIS c Hc) as (_ & Vs). unfold HeapIfaceA.S, HeapIfaceA.SB in Vs.
assert (AVs : L5A.avis H (c / 8 + 2147450880) 1) by (intros i Hi; replace (c / 8 + 2147450880 + i) with (c / 8 + 2147450880) by lia; exact Vs).
assert (Bc : 0 <= c / 8 + 2147450880 < 2 ^ 64) by (assert (c / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); assert (0 <= c / 8) by (apply Z.div_pos; lia); lia).
destruct (ACC c Hc) as [B0|(v & Bv & Hv & Hcv)]; unfold HeapIfaceA.S, HeapIfaceA.SB in *.
- left. intros j Hj. replace (c / 8 + 2147450880 + j) with (c / 8 + 2147450880) by lia. rewrite AG1 by (first [lia| apply NPs; lia]).
unfold MV. rewrite (mrestrict_visible H M (Z_to_bv 64 (c / 8 + 2147450880))) by (exact Vs). exact B0.
- right. exists v. split; [exact Hv|]. split; [|exact Hcv].
apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; replace i with (c / 8 + 2147450880) by lia; rewrite AG1; [reflexivity| lia| apply NPs; lia]| lia| lia|].
apply (proj2 (L5A.u8_at_vis H M _ v AVs ltac:(lia) ltac:(lia))). apply u8_of_byte. exact Bv. }
assert (GZ1 : L5KA.zeros_at M1v 2147468860 44).
{ intros j Hj. rewrite AG1 by (unfold P; lia). apply (GZ j Hj). }
assert (FIN : forall fx2 R2, msteps RSEGS (L5SAR.st fx R 0xafa88 MV) (L5SAR.st fx2 R2 0xafdec M1v) -> getr R2 (reg 1) = Z_to_bv 64 r ->
regs_preserved R R2 -> srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xafa88 M model) K).
{ intros fx2 R2 MSA B1 RP. unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx2 R 0xafa88 R2 0xafdec M1v P K HH AM MSA MG1 AG1).
{ intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
apply (PMASK.ret_exit L ar C HI LY HIok fx2 R2 M1 model1 K _ FF LK cr Aw 0xafdec r (ltac:(oW' 0xafdec%Z)) HH1 AM1 (ltac:(oF' 0xafdec%Z)) eq_refl (ltac:(oD' 0xafdec%Z)) B1 ltac:(lia) Hr2).
intros model2 MRT2 AM2 HH2.
apply (KONT fx2 R2 M1 model2).
- exact RP.
- intros x Ox. rewrite <- (Z_to_bv_bv_unsigned _ x). apply FR1; [apply bv_unsigned_in_range|].
intros Px. unfold P in Px. apply (Ox (sp - 12288, 12288)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. lia.
- exact MGM1.
- eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
- exact AM2.
- exact HH2. }
assert (EPIL : forall fx3 R3, getr R3 (reg 2) = Z_to_bv 64 (sp - 96) ->
L5.u64_at RSEGS M1v (sp - 96) (bv_unsigned (getr R (reg 26))) -> L5.u64_at RSEGS M1v (sp - 88) (bv_unsigned (getr R (reg 25))) ->
L5.u64_at RSEGS M1v (sp - 80) (bv_unsigned (getr R (reg 24))) -> L5.u64_at RSEGS M1v (sp - 72) (bv_unsigned (getr R (reg 23))) ->
L5.u64_at RSEGS M1v (sp - 64) (bv_unsigned (getr R (reg 22))) -> L5.u64_at RSEGS M1v (sp - 56) (bv_unsigned (getr R (reg 21))) ->
L5.u64_at RSEGS M1v (sp - 48) (bv_unsigned (getr R (reg 20))) -> L5.u64_at RSEGS M1v (sp - 40) (bv_unsigned (getr R (reg 19))) ->
L5.u64_at RSEGS M1v (sp - 32) (bv_unsigned (getr R (reg 18))) -> L5.u64_at RSEGS M1v (sp - 24) (bv_unsigned (getr R (reg 9))) ->
L5.u64_at RSEGS M1v (sp - 16) (bv_unsigned (getr R (reg 8))) -> L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1))) ->
(forall k, In k [3; 4; 27]%nat -> getr R3 (reg k) = getr R (reg k)) ->
msteps RSEGS (L5SAR.st fx R 0xafa88 MV) (L5SAR.st fx3 R3 0xafdb8 M1v) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xafa88 M model) K).
{ intros fx3 R3 R32 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8 K3 MS3.
cfeed PX (PMAVALP1.avlX_conc fx3 R3 M1v (fun j => match j with 2%nat => sp | 40%nat => bv_unsigned (getr R (reg 1)) | 41%nat => bv_unsigned (getr R (reg 8))
| 42%nat => bv_unsigned (getr R (reg 9)) | 43%nat => bv_unsigned (getr R (reg 18)) | 44%nat => bv_unsigned (getr R (reg 19)) | 45%nat => bv_unsigned (getr R (reg 20))
| 46%nat => bv_unsigned (getr R (reg 21)) | 47%nat => bv_unsigned (getr R (reg 22)) | 48%nat => bv_unsigned (getr R (reg 23)) | 49%nat => bv_unsigned (getr R (reg 24))
| 50%nat => bv_unsigned (getr R (reg 25)) | 51%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) ltac:(first [assumption | apply bv_unsigned_in_range | unfold PMAVALP1.aligned; lia | lia]).
destruct PX as (fx4 & R4 & M4 & _ & FR4 & _ & (MS4 & KS4 & X1 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26)).
assert (EM : M4 = M1v) by (apply functional_extensionality; exact FR4). subst M4.
apply (FIN fx4 R4 ltac:(eapply msteps_trans; [exact MS3| exact MS4])).
- rewrite X1, Z_to_bv_bv_unsigned. exact Rra.
- apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx. cbn [In] in Hx.
destruct Hx as [<-|Hx]; [rewrite X2, Rsp; reflexivity|].
destruct Hx as [<-|Hx]; [rewrite (KS4 3%nat) by inl; apply K3; cbn; tauto|].
destruct Hx as [<-|Hx]; [rewrite (KS4 4%nat) by inl; apply K3; cbn; tauto|].
destruct Hx as [<-|Hx]; [rewrite X8; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X9; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X18; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X19; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X20; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X21; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X22; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X23; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X24; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X25; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite X26; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite (KS4 27%nat) by inl; apply K3; cbn; tauto|].
destruct Hx. }
destruct EX as [(MS & KS & E2 & Hn0 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8)
|(MS & KS & E2 & E5 & E6 & E7 & E8 & E9 & E11 & E12 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E28 & E29 & E30 & E31 & Hn0
& S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8)].
-
apply (EPIL fx1 R1 E2 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8); [intros k Hk; apply KS; revert k Hk; kin| exact MS].
-
rewrite Z.sub_0_r, Z.mod_small in Hn0 by lia.
rewrite e6 in E6. rewrite e17 in E17.
assert (VC1 : vconst sp (p + n) R1) by (unfold vconst; repeat split; assumption).
destruct (loop_head M1v sp p (p + n) IMG1 ltac:(lia) Hp ltac:(lia) Hpn ltac:(lia) BY1 SH1 GZ1 (Z.to_nat n) fx1 R1 p ltac:(lia) ltac:(lia) VC1 E12)
as (fx2 & R2 & MS2 & SP2 & KS2).
apply (EPIL fx2 R2 SP2 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8).
+ intros k Hk. rewrite (KS2 k ltac:(revert k Hk; kin)). apply KS. revert k Hk. kin.
+ eapply msteps_trans; [exact MS| exact MS2].
Qed.
End Stage.
End PMAVAL.
