(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmCertKitG PmBImgGap PmBValP1 PmBValP2 PmBValP3 PmBValP4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBVal () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBVal.PMBVAL.Loop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "3Z"; "0HI"; "0KS"]; ["0L"; "4bvmap"; "0M"; "0Mv"; "0R"; "0R'"; "0R2"; "5msteps"; "6byte_at"; "7u8_at"; "8zeros_at"; "9KL"; "9VC"; "9goal_from"; "9vconst"; ":validate_spec"]; [";FPState"; ";getr"; ";mkst"; ";rdn"; ";seg_rom"; "<loaded_segments"; "0S"; "0SCFG_P"; "=eqb"; ">In"; ">existsb"; ">forallb"; "?add"; "?div"; "?land"; "?le"]; ["?lt"; "?modulo"; "?of_nat"; "?pow"; "?sub"; "0a"; "0ar"; "0b"; "0c"; "0c'"; "0d0"; "0e"; "0fx"; "0fx2"; "0k"; "0n"]; ["0nx"; "0p"; "0pc"; "0pc2"; "@Z_to_bv"; "@bv"; "0v"; "0w"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBVAL.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmBVal "I'5'6%211';'3&Q;&Q:&Q8r1%211r2%53:21qSN;1%83<13(9%<3;21&Q9r4%23A:1%33B92p021pSND1p071pQ0E1p2F1").
Proof. intros A KS.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Ltac kin := apply sub_in; vm_compute; reflexivity.
Ltac kks KS := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; apply KS; revert k Hk; kin.
Lemma land7_le : ltac2:(TCodec.tc2 tcn__PmBVal "N'=':&Q?zr2%3221&Q@&QC+2+R0%3221%5271%;271&QAr3+8%3221%?21=&Q>r4%721:+7%4221%E2D1%F22:%H221p091p0?1pT@L1pTBM1").
Proof. intros x w.
intros H1 H2. rewrite (Z.mod_small x) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound x 8). lia.
Qed.
Lemma land7_le' : ltac2:(TCodec.tc2 tcn__PmBVal "F'=&Q?zr2%3221&QAr3+8%3221%8216':&Q>r4+7%3221%>2=1%?22:%7221p091p0?1pT@D1pTBE1").
Proof. intros x w. intros H1 H2. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. pose proof (Z.mod_pos_bound x 8). lia. Qed.
Lemma e6 : ltac2:(TCodec.tc2 tcn__PmBVal ":';'R5yR0%211&R4+_oooooooooomO%2241-R1%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Lemma e17 : ltac2:(TCodec.tc2 tcn__PmBVal ":';'R5yR0%211&R4+_oooooooooon2%2241-QN%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Lemma e15 : ltac2:(TCodec.tc2 tcn__PmBVal ":';'R5yR0%211&R4+_oooooooooooO%2241-1%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Lemma e19 : ltac2:(TCodec.tc2 tcn__PmBVal ":';'R5yR0%211&R4+_ooooooookc]2%2241-T\bN%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Lemma table_all : forallb (fun k => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (143965 + Z.of_nat k)) 1 with Some [_] => true | _ => false end) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma table_ok : ltac2:(TCodec.tc2 tcn__PmBVal "Q<'=':&Q?zr1%3221+WO%5231%7231'<'R5y8%211';'8'5%114%311&Q3&Q5yR0%;11(1%11;q031&R4&Q<+T\bMr3%3221%52:1u1%>4=821(2(4(7%11H%33IQ11%52F1%J3F71qS@L1%Q02M1p0Q21pSNQ;1").
Proof. intros k.
intros Hk. pose proof table_all as T. rewrite forallb_forall in T. specialize (T (Z.to_nat k) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in T by lia. destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (143965 + k)) 1) as [[|b [|]]|]; try discriminate. exists b. reflexivity.
Qed.
Section Loop.
Variable Mv : word -> option byte.
Variables (S p e : Z).
Hypothesis IMG : L5.img_clear Mv 65536 1269760.
Hypothesis HS : 140735332487280 <= S <= 2 ^ 47.
Hypothesis Hp : 1 <= p.
Hypothesis Hpe : p <= e.
Hypothesis He : e <= 2 ^ 47.
Hypothesis Hn : e - p <= 2 ^ 26.
Hypothesis BY : forall c, p <= c < e -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS Mv c b.
Hypothesis SH : forall c, p <= c < e -> L5KA.zeros_at Mv (c / 8 + 2147450880) 1 \/ (exists v, 1 <= v <= 7 /\ L5.u8_at RSEGS Mv (c / 8 + 2147450880) v /\ c mod 8 < v).
Hypothesis GAP1 : L5KA.zeros_at Mv 2147468872 44.
Definition vconst (R : bvmap 5 word) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 112) /\ getr R (reg 5) = Z_to_bv 64 245 /\ getr R (reg 6) = Z_to_bv 64 2 /\ getr R (reg 7) = Z_to_bv 64 (-65)
/\ getr R (reg 8) = Z_to_bv 64 159 /\ getr R (reg 9) = Z_to_bv 64 240 /\ getr R (reg 13) = Z_to_bv 64 e /\ getr R (reg 14) = Z_to_bv 64 8
/\ getr R (reg 15) = Z_to_bv 64 (-1) /\ getr R (reg 16) = Z_to_bv 64 1 /\ getr R (reg 17) = Z_to_bv 64 (-62) /\ getr R (reg 18) = Z_to_bv 64 143965
/\ getr R (reg 19) = Z_to_bv 64 (-143966) /\ getr R (reg 20) = Z_to_bv 64 2147450880 /\ getr R (reg 21) = Z_to_bv 64 144 /\ getr R (reg 22) = Z_to_bv 64 244
/\ getr R (reg 23) = Z_to_bv 64 143 /\ getr R (reg 24) = Z_to_bv 64 3 /\ getr R (reg 28) = Z_to_bv 64 239 /\ getr R (reg 29) = Z_to_bv 64 224
/\ getr R (reg 30) = Z_to_bv 64 160 /\ getr R (reg 31) = Z_to_bv 64 237.
Definition VC : list nat := [2; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31]%nat.
Lemma vconst_keep : ltac2:(TCodec.tc2 tcn__PmBVal "Q1&Ay5'R5yR0%211%5241&Nr2%211'6&Q9r1&L%33421';&Q1r4&R4&QB%11<%32C1%6251r5%8213%:3D31p0<1pSNA1r3%F11p031p0F1pQ<J1pQ:K1").
Proof. intros R R'.
intros (C2 & C5 & C6 & C7 & C8 & C9 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C28 & C29 & C30 & C31) K.
unfold vconst. rewrite !K by (cbn; tauto). repeat split; assumption.
Qed.
Definition KL : list nat := [3; 4]%nat.
Definition goal_from (fx : FPState) (R : bvmap 5 word) (pc : Z) : Prop :=
exists fx' R', msteps RSEGS (L5SAR.st fx R pc Mv) (L5SAR.st fx' R' 0xb1574 Mv) /\ getr R' (reg 2) = Z_to_bv 64 (S - 112)
/\ (forall k, In k KL -> getr R' (reg k) = getr R (reg k)).
Lemma goal_pre : ltac2:(TCodec.tc2 tcn__PmBVal "QG'Q0&Ay5'R5yR0%211%5241'='G&Q5&Q2r6r5&R4r4%22;1vC&Q4%119%9587431r3r2r1%:2C1%>543186%A3@61'6&Q9&K%23371';&Q1&QB%11<%E2Q01%42G1r8%6213%83Q131p0:1pSN>1&M%13NLFr9r7%43291p041p071p0G1pT8Q:1pQ>Q<1pSLQC1pT6Q=1pQ:Q?1pSJQF1").
Proof. intros fx R pc fx2 R2 pc2.
intros MS KS (fx3 & R3 & MS3 & SP3 & KS3). exists fx3, R3. split; [eapply msteps_trans; [exact MS| exact MS3]|]. split; [exact SP3|].
intros k Hk. rewrite (KS3 k Hk). apply KS. exact Hk.
Qed.
Lemma goal_epi : ltac2:(TCodec.tc2 tcn__PmBVal "QO'Q0&Ay5'R5yR0%211%5241'='G&Q5&Q2r5r4&R4r3%22;1vC&Q4%119%9587431r2r1+fU[D%:2C1%>543186%A3@61'6&Q9&K%23381';&Q1&QB%11=%E2Q01%42G1r7%6213%83Q131p0:1pSN>1u2%:11%N2Q91%=2N1&QDvQ6+S@%3221%Q42Q=1%D3Q=61&Mr8r6%332B1p051p0@1p0Q01pQ>QD1pSLQK1pT6QE1pQ:QG1pSJQN1").
Proof. intros fx R pc fx2 R2. intros MS KS SP. exists fx2, R2. split; [exact MS|]. split; [exact SP| exact KS]. Qed.
Ltac sc := first [ assumption | lia | (rewrite Zplus_minus; assumption) | (apply land7_le; lia) | (apply land7_le'; lia) ].
Ltac vfacts V := let C2 := fresh "C2" in
pose proof V as (C2 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C13 & ?C14 & ?C15 & ?C16 & ?C17 & ?C18 & ?C19 & ?C20 & ?C21 & ?C22 & ?C23 & ?C24 & ?C28 & ?C29 & ?C30 & ?C31).
Ltac runp X fx R VAL :=
let PP := fresh "PP" in let fx1 := fresh "fx" in let R1 := fresh "R" in let M1 := fresh "M" in let FR := fresh "FR" in
pose proof (X fx R Mv VAL) as PP; cbn beta iota in PP; L5SAR.feed PP ltac:(sc);
destruct PP as (fx1 & R1 & M1 & _ & FR & _ & EX); (assert (M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1.
Ltac runpk X fx R VAL K :=
let PP := fresh "PP" in let fx1 := fresh "fx" in let R1 := fresh "R" in let M1 := fresh "M" in let FR := fresh "FR" in let EX := fresh "EX" in
pose proof (X fx R Mv VAL) as PP; cbn beta iota in PP; L5SAR.feed PP ltac:(sc);
destruct PP as (fx1 & R1 & M1 & _ & FR & _ & EX); (assert (M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1; K EX.
Ltac epi_exit V := lazymatch goal with
| MS : msteps _ (L5SAR.st ?fx ?R _ _) (L5SAR.st ?fx1 ?R1 0xb1574 _), KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x) |- goal_from ?fx ?R _ =>
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
Hypothesis IH : forall fx R c', c < c' < e -> vconst R -> getr R (reg 10) = Z_to_bv 64 c' -> goal_from fx R 0xb1278.
Lemma back_case : ltac2:(TCodec.tc2 tcn__PmBVal "Q>'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221&Q@r1%2241%8241r2vQK%:221&Nr4%211';&Q1r5&R4&QBuJ%211%42L1%7261%62L;%:3L21&Mr7r6+fUU8%43321p061p0B1p0F1p0J1pSDQ41pQ:Q61pSJQ=1").
Proof using All. intros fx R c'.
intros Hc Hc' V R26. vfacts V.
set (a0 := bv_unsigned (getr R (reg 10))). pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as Ha0. change (bv_modulus 64) with (2 ^ 64) in Ha0.
assert (R10 : getr R (reg 10) = Z_to_bv 64 a0) by (symmetry; apply Z_to_bv_bv_unsigned).
runp PMBVALP1.bvlB_conc fx R (fun j => match j with 2%nat => S | 10%nat => a0 | 33%nat => c' | 35%nat => e - c' | _ => 0 end).
destruct EX as [EX|EX]; msks EX.
- epi_exit V.
- assert (LT : c' < e).
{ destruct (Z.eq_dec c' e) as [Ec|Ec]; [| lia]. exfalso.
lazymatch goal with NE : 1 <= _ |- _ => rewrite Zplus_minus, (Z.mod_small e), Ec, Z.sub_diag, Z.mod_0_l in NE by lia; lia end. }
gpre. apply (IH _ _ c' ltac:(lia)); [vk V| assumption].
Qed.
Local Ltac lexit V nx R26 := lazymatch goal with
| MS : msteps _ _ (L5SAR.st _ _ 0xb1574 _) |- _ => epi_exit V
| _ => gpre; apply (back_case _ _ nx ltac:(lia) ltac:(lia)); [vk V| kept 26%nat R26]
end.
Lemma lead_case : ltac2:(TCodec.tc2 tcn__PmBVal "R9'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r3%5231%7231&Q@r4%2215vQK%;271%=231r5%7214z%@218+WO%B2:1%D231&Nr8%211';&Q1r9&R4&QBu:%211%42Q51%7261%62Q5;%:3Q521r:uJ%911%;2Q<1%>241%@3Q;17r;uI%?11%A2QB1%D241%F3QA1=&Mr=r<+fURL%43321p061p0=1p0D1p0Q01p0Q41p0Q:1p0Q=1p0QD1pS@QM1pT2QN1pSFQO1pQ:R11pSJR81").
Proof using All. intros fx R d0 nx b.
intros Hc Hnx Hd Hb V R10 R26 R25. vfacts V.
set (a1 := bv_unsigned (getr R (reg 11))).
pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as Ha1. change (bv_modulus 64) with (2 ^ 64) in Ha1.
assert (R11 : getr R (reg 11) = Z_to_bv 64 a1) by (symmetry; apply Z_to_bv_bv_unsigned).
runp PMBVALP1.bvlL_conc fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => nx | 35%nat => e - d0 | 37%nat => b | 39%nat => a1 | _ => 0 end).
repeat (destruct EX as [EX|EX]; [msks EX; lexit V nx R26|]); msks EX; lexit V nx R26.
Qed.
Local Ltac r1v X d0 nx b b1 V R10 R26 R25 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => nx | 35%nat => e - d0 | 37%nat => b | 39%nat => b1 | _ => 0 end) ltac:(fun EX =>
destruct EX as [EX|EX]; msks EX;
[ epi_exit V
| gpre; apply (lead_case _ _ d0 nx b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10| kept 26%nat R26| kept 25%nat R25] ])
end.
Lemma r1_case : ltac2:(TCodec.tc2 tcn__PmBVal "RF'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r3%5231%7231&Q<r4+2%3221vQK%<221&Q@r5%2217%@285%B221z%C21;+WO%E2=1%G231&Nr8%211';&Q1r9&R4&QBu:%211%42Q81%7261%62Q8;%:3Q821r:u<%911%;2Q?1%>241%Q32>Q1%>2Q@1%B3Q@31r;uJ%A11%C2QG1%F241%E2QGF%I3QG21r<uI%H11%J2QN1%M241%O3QM17&Mr>r=+fUQL%43321p061p0=1p0E1p0N1p0Q:1p0Q>1p0QD1p0QJ1p0R11pS@R:1pT2R;1pSFR<1pQ:R>1pSJRE1").
Proof using All. intros fx R d0 nx b.
intros Hc Hd Hnx Hb V R10 R12 R26 R25. vfacts V.
destruct (BY (d0 + 1) ltac:(lia)) as (b1 & Hb1 & U1).
destruct (SH (d0 + 1) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
- r1v PMBVALP4.bvlR1Z_conc d0 nx b b1 V R10 R26 R25.
- vsplit v Hv.
+ r1v PMBVALP4.bvlR1P1_conc d0 nx b b1 V R10 R26 R25.
+ r1v PMBVALP4.bvlR1P2_conc d0 nx b b1 V R10 R26 R25.
+ r1v PMBVALP4.bvlR1P3_conc d0 nx b b1 V R10 R26 R25.
+ r1v PMBVALP4.bvlR1P4_conc d0 nx b b1 V R10 R26 R25.
+ r1v PMBVALP4.bvlR1P5_conc d0 nx b b1 V R10 R26 R25.
+ r1v PMBVALP4.bvlR1P6_conc d0 nx b b1 V R10 R26 R25.
+ r1v PMBVALP4.bvlR1P7_conc d0 nx b b1 V R10 R26 R25.
Qed.
Local Ltac r2v X d0 nx b b2 V R10 R26 R25 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 34%nat => nx | 35%nat => e - d0 | 37%nat => b | 39%nat => b2 | _ => 0 end) ltac:(fun EX =>
destruct EX as [EX|EX]; msks EX;
[ epi_exit V
| gpre; apply (r1_case _ _ d0 nx b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10| assumption| kept 26%nat R26| kept 25%nat R25] ])
end.
Lemma r2_case : ltac2:(TCodec.tc2 tcn__PmBVal "RF'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r3%5231%7231&Q<r4+3%3221vQK%<221&Q@r5%2217%@285%B221z%C21;+WO%E2=1%G231&Nr8%211';&Q1r9&R4&QBu:%211%42Q81%7261%62Q8;%:3Q821r:u1%911%;2Q?1%>241%Q32>Q1%>2Q@1%B3Q@31r;uJ%A11%C2QG1%F241%E2QGF%I3QG21r<uI%H11%J2QN1%M241%O3QM17&Mr>r=+fUPL%43321p061p0=1p0E1p0N1p0Q:1p0Q>1p0QD1p0QJ1p0R11pS@R:1pT2R;1pSFR<1pQ:R>1pSJRE1").
Proof using All. intros fx R d0 nx b.
intros Hc Hd Hnx Hb V R10 R1 R26 R25. vfacts V.
destruct (BY (d0 + 2) ltac:(lia)) as (b2 & Hb2 & U2).
destruct (SH (d0 + 2) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
- r2v PMBVALP4.bvlR2Z_conc d0 nx b b2 V R10 R26 R25.
- vsplit v Hv.
+ r2v PMBVALP4.bvlR2P1_conc d0 nx b b2 V R10 R26 R25.
+ r2v PMBVALP4.bvlR2P2_conc d0 nx b b2 V R10 R26 R25.
+ r2v PMBVALP4.bvlR2P3_conc d0 nx b b2 V R10 R26 R25.
+ r2v PMBVALP4.bvlR2P4_conc d0 nx b b2 V R10 R26 R25.
+ r2v PMBVALP4.bvlR2P5_conc d0 nx b b2 V R10 R26 R25.
+ r2v PMBVALP4.bvlR2P6_conc d0 nx b b2 V R10 R26 R25.
+ r2v PMBVALP4.bvlR2P7_conc d0 nx b b2 V R10 R26 R25.
Qed.
Local Ltac r3v X d0 b b3 V R10 R26 R25 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | 39%nat => b3 | _ => 0 end) ltac:(fun EX =>
destruct EX as [EX|EX]; msks EX;
[ epi_exit V
| gpre; apply (r2_case _ _ d0 (d0 + 4) b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10| assumption| kept 26%nat R26| kept 25%nat R25] ])
end.
Lemma r3_case : ltac2:(TCodec.tc2 tcn__PmBVal "RK'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r2%5231%7231&Q<r3+4%3221vQK%<221z%>216+WO%@281%B231&Nr6%211';&Q1r7&R4&QBu:%211%42Q31%7261%62Q3;%:3Q321r8u<%911%;2Q:1%>241+3%O2?1%?2Q<1%C3Q<41r9uJ%B11%D2QC1%G241%Q72>Q5%G2QD1%K3QD31r:u1%J11%L2QK1%O241%Q?2=Q=%O2QL1%Q33QL31r;uI%Q211%Q42R31%Q7241%Q62R3E%Q:3R321&Mr=r<+fToL%43321p061p0>1p0G1p0Q01p0Q:1p0QF1p0QJ1p0R01p0R71pS@R@1pSFRA1pQ:RC1pSJRJ1").
Proof using All. intros fx R d0 b.
intros Hc Hd Hb V R10 R12 R26 R1 R25. vfacts V.
destruct (BY (d0 + 3) ltac:(lia)) as (b3 & Hb3 & U3).
destruct (SH (d0 + 3) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
- r3v PMBVALP4.bvlR3Z_conc d0 b b3 V R10 R26 R25.
- vsplit v Hv.
+ r3v PMBVALP4.bvlR3P1_conc d0 b b3 V R10 R26 R25.
+ r3v PMBVALP4.bvlR3P2_conc d0 b b3 V R10 R26 R25.
+ r3v PMBVALP4.bvlR3P3_conc d0 b b3 V R10 R26 R25.
+ r3v PMBVALP4.bvlR3P4_conc d0 b b3 V R10 R26 R25.
+ r3v PMBVALP4.bvlR3P5_conc d0 b b3 V R10 R26 R25.
+ r3v PMBVALP4.bvlR3P6_conc d0 b b3 V R10 R26 R25.
+ r3v PMBVALP4.bvlR3P7_conc d0 b b3 V R10 R26 R25.
Qed.
Definition L2 : list nat := [2; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 28; 29; 30; 31; 3; 4; 10; 25]%nat.
Lemma tbl_case : ltac2:(TCodec.tc2 tcn__PmBVal "R8'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r2%5231%7231&Q@r3vQK%3221z%<214+WO%>261%@231&Nr6%211';&Q1r7&R4&QBu:%211%42Q11%7261%62Q1;%:3Q121r8u;%911%;2Q81%>241&Q<+T\bM%22D1%@2Q;1%D3Q;51r9uI%C11%E2QB1%H241%G2QBH%K3QB21&Mr;r:+fTmL%43321p061p0>1p0I1p0Q51p0Q91p0Q?1p0QD1pS@QM1pSFQN1pQ:R01pSJR71").
Proof using All. intros fx R d0 b.
intros Hc Hd Hb V R10 R11 R25.
destruct (table_ok b Hb) as (tb & TB).
assert (L1 : (27%bv : bv 5) <> 0%bv) by discriminate.
assert (LL2 : getr R (11%bv : bv 5) = Z_to_bv 64 (b + 143965)) by exact R11.
assert (L3 : rdn RSEGS Mv (Z_to_bv 64 (b + 143965 + bv_signed (0%bv : bv 12))) 1 = Some [tb]).
{ change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r, Z.add_comm. rewrite (PMCG.rdn_img RSEGS Mv 65536 1269760 _ 1 IMG) by lia. exact TB. }
pose proof (PMCG.lbu_img_run RSEGS fx R Mv 0xb13bc (ltac:(oW' 0xb13bc%Z)) 27%bv 11%bv 0%bv (b + 143965) tb (ltac:(oF' 0xb13bc%Z)) eq_refl (ltac:(oD' 0xb13bc%Z)) L1 ltac:(lia) ltac:(lia) LL2 ltac:(lia)
ltac:(change (bv_signed (0%bv : bv 12)) with 0; lia) L3) as MSl.
set (R2 := regupd R 27%bv (Z_to_bv 64 (bv_unsigned tb))) in MSl.
assert (RU : forall k, k <> 27%nat -> (k < 32)%nat -> getr R2 (reg k) = getr R (reg k)).
{ intros k Hk Hk32. unfold R2. replace (27%bv : bv 5) with (reg 27) by (apply bv_eq; reflexivity). apply PMPX.regupd_other_idx; lia. }
assert (R27 : getr R2 (reg 27) = Z_to_bv 64 (bv_unsigned tb)).
{ unfold R2. replace (27%bv : bv 5) with (reg 27) by (apply bv_eq; reflexivity). apply PMPX.regupd_same_idx. lia. }
pose proof (bv_unsigned_in_range 8 tb) as Htb. change (bv_modulus 8) with 256 in Htb.
assert (KS2 : forall k, In k L2 -> getr R2 (reg k) = getr R (reg k)).
{ intros k Hk. unfold L2 in Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite RU by lia; reflexivity|]). destruct Hk. }
assert (V2 : vconst R2) by exact (vconst_keep R R2 V ltac:(kks KS2)).
assert (R2_10 : getr R2 (reg 10) = Z_to_bv 64 d0) by (rewrite KS2 by inl; exact R10).
assert (R2_25 : getr R2 (reg 25) = Z_to_bv 64 b) by (rewrite KS2 by inl; exact R25).
apply (goal_pre fx R 0xb13bc fx R2 (0xb13bc + 4)).
{ exact MSl. }
{ kks KS2. }
change (0xb13bc + 4) with 0xb13c0.
clear MSl KS2 RU.
vfacts V2.
set (t := bv_unsigned tb) in *.
assert (CASES : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ 4 <= t) by lia.
destruct CASES as [Et|[Et|[Et|[Et|Et]]]].
- rewrite Et in R27.
runp PMBVALP1.bvlT0_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end).
repeat (destruct EX as [EX|EX]; [msks EX; first [ epi_exit V2 | gpre; apply (back_case _ _ (d0 + 1) ltac:(lia) ltac:(lia)); [vk V2| assumption] ]|]);
msks EX; first [ epi_exit V2 | gpre; apply (back_case _ _ (d0 + 1) ltac:(lia) ltac:(lia)); [vk V2| assumption] ].
- rewrite Et in R27. destruct (Z_le_gt_dec (e - d0) 1) as [LE|GT].
+ runp PMBVALP1.bvlT1a_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end).
msks EX. epi_exit V2.
+ runp PMBVALP1.bvlT1b_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end).
msks EX. gpre.
apply (r1_case _ _ d0 (d0 + 2) b ltac:(lia) ltac:(lia) ltac:(lia) Hb); [vk V2| kept 10%nat R2_10| assumption| assumption| kept 25%nat R2_25].
- rewrite Et in R27. destruct (Z_le_gt_dec (e - d0) 2) as [LE|GT].
+ runp PMBVALP1.bvlT2a_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end).
msks EX. epi_exit V2.
+ runp PMBVALP1.bvlT2b_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end).
msks EX. gpre.
apply (r2_case _ _ d0 (d0 + 3) b ltac:(lia) ltac:(lia) ltac:(lia) Hb); [vk V2| kept 10%nat R2_10| assumption| assumption| kept 25%nat R2_25].
- rewrite Et in R27. destruct (Z_le_gt_dec (e - d0) 3) as [LE|GT].
+ runp PMBVALP1.bvlT3a_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end).
msks EX. epi_exit V2.
+ runp PMBVALP1.bvlT3b_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end).
msks EX. gpre.
apply (r3_case _ _ d0 b ltac:(lia) ltac:(lia) Hb); [vk V2| kept 10%nat R2_10| assumption| assumption| assumption| kept 25%nat R2_25].
- runp PMBVALP1.bvlTbig_conc fx R2 (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | 38%nat => t | _ => 0 end).
destruct EX as [EX|EX]; msks EX; epi_exit V2.
Qed.
Local Ltac sv X d0 b V R10 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end) ltac:(fun EX =>
msks EX; gpre; apply (tbl_case _ _ d0 b ltac:(lia) ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10| assumption| assumption])
end.
Lemma slow : ltac2:(TCodec.tc2 tcn__PmBVal "Q>'Q0&Ay5'R5yR0%211%5241'=':&Q?vR1vQH%3221r1%5231%7231&Q@r2vQK%3221&Nr4%211';&Q1r5&R4&QBu:%211%42L1%7261%62L;%:3L21&Mr7r6+fTl<%43321p061p0B1p0F1p0K1pSFQ41pQ:Q61pSJQ=1").
Proof using All. intros fx R d0.
intros Hc Hd V R10. vfacts V.
destruct (BY d0 ltac:(lia)) as (b & Hb & U0).
destruct (SH d0 ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)].
- sv PMBVALP1.bvlSZ_conc d0 b V R10.
- vsplit v Hv.
+ sv PMBVALP1.bvlSP1_conc d0 b V R10.
+ sv PMBVALP1.bvlSP2_conc d0 b V R10.
+ sv PMBVALP1.bvlSP3_conc d0 b V R10.
+ sv PMBVALP1.bvlSP4_conc d0 b V R10.
+ sv PMBVALP1.bvlSP5_conc d0 b V R10.
+ sv PMBVALP1.bvlSP6_conc d0 b V R10.
+ sv PMBVALP1.bvlSP7_conc d0 b V R10.
Qed.
Local Ltac fv X k NEXT b V R10 :=
lazymatch goal with |- goal_from ?fx ?R _ =>
runpk X fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b | _ => 0 end) ltac:(fun EX =>
destruct EX as [EX|EX]; msks EX;
[ gpre; lazymatch goal with A10 : getr _ (reg 10) = Z_to_bv 64 (c + k) |- _ => apply (slow _ _ (c + k) ltac:(lia) ltac:(lia)); [vk V| exact A10] end
| NEXT ])
end.
Local Ltac fnext FN V R10 := gpre; apply (FN _ _ ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10].
Local Ltac fback V := gpre; apply (back_case _ _ (c + 8) ltac:(lia) ltac:(lia)); [vk V| assumption].
Local Ltac fcases Z P1 P2 P3 P4 P5 P6 P7 k NEXT :=
lazymatch goal with V : vconst ?R, R10 : getr ?R (reg 10) = _ |- goal_from _ ?R _ =>
vfacts V;
let b := fresh "b" in let Hb := fresh "Hb" in let U := fresh "U" in
destruct (BY (c + k) ltac:(lia)) as (b & Hb & U);
destruct (SH (c + k) ltac:(lia)) as [Z0 | (v & Hv & Uv & Hcv)];
[ fv Z k NEXT b V R10
| vsplit v Hv; [ fv P1 k NEXT b V R10 | fv P2 k NEXT b V R10 | fv P3 k NEXT b V R10 | fv P4 k NEXT b V R10
| fv P5 k NEXT b V R10 | fv P6 k NEXT b V R10 | fv P7 k NEXT b V R10 ] ]
end.
Lemma fast7 : ltac2:(TCodec.tc2 tcn__PmBVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu:%211%42H1%7261%62HC%:3H21&Mr6r5+fTk0%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R10.
fcases PMBVALP3.bvlF7Z_conc PMBVALP3.bvlF7P1_conc PMBVALP3.bvlF7P2_conc PMBVALP3.bvlF7P3_conc PMBVALP3.bvlF7P4_conc PMBVALP3.bvlF7P5_conc
PMBVALP3.bvlF7P6_conc PMBVALP3.bvlF7P7_conc 7 ltac:(fback V).
Qed.
Lemma fast6 : ltac2:(TCodec.tc2 tcn__PmBVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu:%211%42H1%7261%62HC%:3H21&Mr6r5+fTj0%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R10.
fcases PMBVALP3.bvlF6Z_conc PMBVALP3.bvlF6P1_conc PMBVALP3.bvlF6P2_conc PMBVALP3.bvlF6P3_conc PMBVALP3.bvlF6P4_conc PMBVALP3.bvlF6P5_conc
PMBVALP3.bvlF6P6_conc PMBVALP3.bvlF6P7_conc 6 ltac:(fnext fast7 V R10).
Qed.
Lemma fast5 : ltac2:(TCodec.tc2 tcn__PmBVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu:%211%42H1%7261%62HC%:3H21&Mr6r5+fTi0%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R10.
fcases PMBVALP3.bvlF5Z_conc PMBVALP3.bvlF5P1_conc PMBVALP3.bvlF5P2_conc PMBVALP3.bvlF5P3_conc PMBVALP3.bvlF5P4_conc PMBVALP3.bvlF5P5_conc
PMBVALP3.bvlF5P6_conc PMBVALP3.bvlF5P7_conc 5 ltac:(fnext fast6 V R10).
Qed.
Lemma fast4 : ltac2:(TCodec.tc2 tcn__PmBVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu:%211%42H1%7261%62HC%:3H21&Mr6r5+fTh0%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R10.
fcases PMBVALP2.bvlF4Z_conc PMBVALP2.bvlF4P1_conc PMBVALP2.bvlF4P2_conc PMBVALP2.bvlF4P3_conc PMBVALP2.bvlF4P4_conc PMBVALP2.bvlF4P5_conc
PMBVALP2.bvlF4P6_conc PMBVALP2.bvlF4P7_conc 4 ltac:(fnext fast5 V R10).
Qed.
Lemma fast3 : ltac2:(TCodec.tc2 tcn__PmBVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu:%211%42H1%7261%62HC%:3H21&Mr6r5+fTg0%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R10.
fcases PMBVALP2.bvlF3Z_conc PMBVALP2.bvlF3P1_conc PMBVALP2.bvlF3P2_conc PMBVALP2.bvlF3P3_conc PMBVALP2.bvlF3P4_conc PMBVALP2.bvlF3P5_conc
PMBVALP2.bvlF3P6_conc PMBVALP2.bvlF3P7_conc 3 ltac:(fnext fast4 V R10).
Qed.
Lemma fast2 : ltac2:(TCodec.tc2 tcn__PmBVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu:%211%42H1%7261%62HC%:3H21&Mr6r5+fTf0%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R10.
fcases PMBVALP2.bvlF2Z_conc PMBVALP2.bvlF2P1_conc PMBVALP2.bvlF2P2_conc PMBVALP2.bvlF2P3_conc PMBVALP2.bvlF2P4_conc PMBVALP2.bvlF2P5_conc
PMBVALP2.bvlF2P6_conc PMBVALP2.bvlF2P7_conc 2 ltac:(fnext fast3 V R10).
Qed.
Lemma fast1 : ltac2:(TCodec.tc2 tcn__PmBVal "Q9'Q0&Ay5'R5yR0%211%5241&Q?vR1vQH%3221&Q<+8%2241vQK%8221&Nr3%211';&Q1r4&R4&QBu:%211%42H1%7261%62HC%:3H21&Mr6r5+fTe0%43321p061p0B1p0F1p0L1pQ:Q11pSJQ81").
Proof using All. intros fx R.
intros Hc Hce V R10.
fcases PMBVALP2.bvlF1Z_conc PMBVALP2.bvlF1P1_conc PMBVALP2.bvlF1P2_conc PMBVALP2.bvlF1P3_conc PMBVALP2.bvlF1P4_conc PMBVALP2.bvlF1P5_conc
PMBVALP2.bvlF1P6_conc PMBVALP2.bvlF1P7_conc 1 ltac:(fnext fast2 V R10).
Qed.
End IH.
Lemma granule0 : ltac2:(TCodec.tc2 tcn__PmBVal "G'=&Q?vR1r1%3221&Q<r2+8%3221vQK%9221&JvC&Q=r3%2218+QoooPP0%<221+1%83721p0:1p0A1pSBF1").
Proof using All. intros c.
intros H1 H2. set (a := c + (7 - c mod 8)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hm.
pose proof (Z.div_mod c 8 ltac:(lia)) as Dm.
assert (Ea : a / 8 = c / 8).
{ unfold a. replace (c + (7 - c mod 8)) with (7 + (c / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
assert (Ma : a mod 8 = 7).
{ unfold a. replace (c + (7 - c mod 8)) with (7 + (c / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
destruct (SH a ltac:(unfold a; lia)) as [Z0 | (v & Hv & _ & Hav)]; [rewrite Ea in Z0; exact Z0| lia].
Qed.
Lemma loop_head : ltac2:(TCodec.tc2 tcn__PmBVal "QB'6'Q0&Ay5'R5yR0%211%5241'=';&QBr4%211&QDvQKr1%3221%83951':&Q?vR1r2%3221&Q@%123:%7231&N%11@&Q1r5&R4u:%F11%32N1%6251%52NH%K3N21&Mr7r6+fTcH%43321p061p0@1p0C1p0L1pSBQ61pQ:Q81pSJQ?1pT0QA1").
Proof using All.
intros n. induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf). intros fx R c Hn' Hc V R10.
assert (IH : forall fx R c', c < c' < e -> vconst R -> getr R (reg 10) = Z_to_bv 64 c' -> goal_from fx R 0xb1278).
{ intros fx' R' c' Hc' V' R10'. apply (IHn (Z.to_nat (e - c')) ltac:(lia) fx' R' c'); [lia| lia| exact V'| exact R10']. }
vfacts V.
destruct (Z_le_gt_dec 8 (e - c)) as [GE|LT].
- destruct (BY c ltac:(lia)) as (b0 & Hb0 & U0).
pose proof (granule0 c ltac:(lia) ltac:(lia)) as Z0.
runp PMBVALP1.bvlHf_conc fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b0 | _ => 0 end).
destruct EX as [EX|EX]; msks EX; gpre.
+ apply (slow c IH _ _ c ltac:(lia) ltac:(lia)); [vk V| first [kept 10%nat R10 | assumption]].
+ apply (fast1 c IH _ _ ltac:(lia) ltac:(lia)); [vk V| kept 10%nat R10].
- runp PMBVALP1.bvlHs_conc fx R (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | _ => 0 end).
msks EX; gpre.
apply (slow c IH _ _ c ltac:(lia) ltac:(lia)); [vk V| first [kept 10%nat R10 | assumption]].
Qed.
End Loop.
Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis GAP : PMBGAP.rt_img_gap HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma u8_of_byte : ltac2:(TCodec.tc2 tcn__PmBVal "F'R5yR0%211'8y8%511%311p051'=&Hr3r2r1%43321&I&Q5r4%342176p051pT>;1pS<<1pQ6>1").
Proof. intros M a v. intros B. unfold L5.u8_at. cbn [rdn]. unfold byte_at in B. rewrite B. reflexivity. Qed.
Theorem validate_ok : ltac2:(TCodec.tc2 tcn__PmBVal "6&OvQ7v@vQFv>%544321").
Proof.
unfold PMB.validate_spec, PMSPA.validate_spec, PMSPA.scan_spec. cbn [pa_validate PMB.AD ADDR_B].
intros fx R M model K LB FF LK Aw cr p n sp r HH AM K0 ENT FRM FRS A10 A11 Hn Hp Hp0 Hpn DEF ACC VIS LOC BASE KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
change (PMSPA.pm_scr 0) with 12288 in *.
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 12288 112 HH ASTK ltac:(lia)) as (SL112 & SH112 & V3).
pose proof (PMBGAP.gap_vis HI GAP LB FF LK cr Aw M model HH) as GZ.
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (V0' : L5.img_clear MV 1232896 1269760) by (intros i Hi; apply V0; lia).
set (P := fun a => sp - 104 <= a < sp - 104 + 104).
assert (FIN : forall fx2 R2 M1v, mem_grows MV M1v -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
msteps RSEGS (L5SAR.st fx R 0xb11c8 MV) (L5SAR.st fx2 R2 0xb15ac M1v) -> getr R2 (reg 1) = Z_to_bv 64 r ->
regs_preserved R R2 -> srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb11c8 M model) K).
{ intros fx2 R2 M1v MG1 AG1 MSA B1 RP. unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx2 R 0xb11c8 R2 0xb15ac M1v P K HH AM MSA MG1 AG1).
{ intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
apply (PMBSK.ret_exit L ar C HI LY HIok fx2 R2 M1 model1 K _ FF LK cr Aw 0xb15ac r (ltac:(oW' 0xb15ac%Z)) HH1 AM1 (ltac:(oF' 0xb15ac%Z)) eq_refl (ltac:(oD' 0xb15ac%Z)) B1 ltac:(lia) Hr2).
intros model2 MRT2 AM2 HH2.
apply (KONT fx2 R2 M1 model2).
- exact RP.
- intros x Ox. rewrite <- (Z_to_bv_bv_unsigned _ x). apply FR1; [apply bv_unsigned_in_range|].
intros Px. unfold P in Px. apply (Ox (sp - 12288, 12288)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. lia.
- exact MGM1.
- eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
- exact AM2.
- exact HH2. }
assert (EPIL : forall fx3 R3 M1v, mem_grows MV M1v -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
getr R3 (reg 2) = Z_to_bv 64 (sp - 112) ->
L5.u64_at RSEGS M1v (sp - 104) (bv_unsigned (getr R (reg 27))) ->
L5.u64_at RSEGS M1v (sp - 96) (bv_unsigned (getr R (reg 26))) -> L5.u64_at RSEGS M1v (sp - 88) (bv_unsigned (getr R (reg 25))) ->
L5.u64_at RSEGS M1v (sp - 80) (bv_unsigned (getr R (reg 24))) -> L5.u64_at RSEGS M1v (sp - 72) (bv_unsigned (getr R (reg 23))) ->
L5.u64_at RSEGS M1v (sp - 64) (bv_unsigned (getr R (reg 22))) -> L5.u64_at RSEGS M1v (sp - 56) (bv_unsigned (getr R (reg 21))) ->
L5.u64_at RSEGS M1v (sp - 48) (bv_unsigned (getr R (reg 20))) -> L5.u64_at RSEGS M1v (sp - 40) (bv_unsigned (getr R (reg 19))) ->
L5.u64_at RSEGS M1v (sp - 32) (bv_unsigned (getr R (reg 18))) -> L5.u64_at RSEGS M1v (sp - 24) (bv_unsigned (getr R (reg 9))) ->
L5.u64_at RSEGS M1v (sp - 16) (bv_unsigned (getr R (reg 8))) -> L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1))) ->
(forall k, In k [3; 4]%nat -> getr R3 (reg k) = getr R (reg k)) ->
msteps RSEGS (L5SAR.st fx R 0xb11c8 MV) (L5SAR.st fx3 R3 0xb1574 M1v) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb11c8 M model) K).
{ intros fx3 R3 M1v MG1 AG1 R32 S104 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8 K3 MS3.
cfeed PX (PMBVALP1.bvlX_conc fx3 R3 M1v (fun j => match j with 2%nat => sp | 40%nat => bv_unsigned (getr R (reg 1)) | 41%nat => bv_unsigned (getr R (reg 8))
| 42%nat => bv_unsigned (getr R (reg 9)) | 43%nat => bv_unsigned (getr R (reg 18)) | 44%nat => bv_unsigned (getr R (reg 19)) | 45%nat => bv_unsigned (getr R (reg 20))
| 46%nat => bv_unsigned (getr R (reg 21)) | 47%nat => bv_unsigned (getr R (reg 22)) | 48%nat => bv_unsigned (getr R (reg 23)) | 49%nat => bv_unsigned (getr R (reg 24))
| 50%nat => bv_unsigned (getr R (reg 25)) | 51%nat => bv_unsigned (getr R (reg 26)) | 52%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | apply bv_unsigned_in_range | unfold PMBVALP1.aligned; lia | lia]).
destruct PX as (fx4 & R4 & M4 & _ & FR4 & _ & (MS4 & KS4 & X1 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27)).
assert (EM : M4 = M1v) by (apply functional_extensionality; exact FR4). subst M4.
apply (FIN fx4 R4 M1v MG1 AG1 ltac:(eapply msteps_trans; [exact MS3| exact MS4])).
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
destruct Hx as [<-|Hx]; [rewrite X27; apply Z_to_bv_bv_unsigned|].
destruct Hx. }
destruct (Z.eq_dec n 0) as [N0|N0].
-
subst n. destruct (Z.eq_dec p 0) as [P0|P0].
+ cfeed PP (PMBVALP1.bvlE00_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | _ => 0 end)) ltac:(first [assumption | unfold PMBVALP1.aligned; lia | lia | (rewrite A11; reflexivity)]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS & KS & E2 & E12 & E13 & E14 & S104 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8)).
apply (EPIL fx1 R1 M1v MG1 ltac:(intros a Ha Na; apply FRZ1; [exact Ha| exact Na]) E2 S104 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8); [intros k Hk; apply KS; revert k Hk; kin| exact MS].
+ cfeed PP (PMBVALP1.bvlE01_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | _ => 0 end)) ltac:(first [assumption | unfold PMBVALP1.aligned; lia | lia | (rewrite A11; reflexivity)]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS & KS & E2 & E12 & E13 & E14 & S104 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8)).
apply (EPIL fx1 R1 M1v MG1 ltac:(intros a Ha Na; apply FRZ1; [exact Ha| exact Na]) E2 S104 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8); [intros k Hk; apply KS; revert k Hk; kin| exact MS].
-
assert (P1 : 1 <= p) by (destruct Hp0; lia).
cfeed PP (PMBVALP1.bvlEn_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => p | 35%nat => n | _ => 0 end)) ltac:(first [assumption | unfold PMBVALP1.aligned; lia | lia]).
destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS & KS & E2 & E5 & E6 & E7 & E8 & E9 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22
& E23 & E24 & E28 & E29 & E30 & E31 & S104 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8)).
assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
assert (NPs : forall c, 0 <= c < 2 ^ 47 -> ~ P (c / 8 + 2147450880)).
{ intros c Hc. unfold P. assert (c / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). assert (0 <= c / 8) by (apply Z.div_pos; lia). lia. }
assert (NPb : forall c, p <= c < p + n -> ~ P c).
{ intros c Hc. unfold P. destruct LOC as [X|[X|X]]; lia. }
assert (IMG1 : L5.img_clear M1v 65536 1269760).
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
assert (GZ1 : L5KA.zeros_at M1v 2147468872 44).
{ intros j Hj. rewrite AG1 by (unfold P; lia). apply (GZ j Hj). }
rewrite e6 in E7. rewrite e17 in E17. rewrite e15 in E15. rewrite e19 in E19.
assert (E10 : getr R1 (reg 10) = Z_to_bv 64 p) by (rewrite (KS 10%nat) by inl; exact A10).
assert (VC1 : vconst sp (p + n) R1) by (unfold vconst; repeat split; assumption).
destruct (loop_head M1v sp p (p + n) IMG1 ltac:(lia) P1 ltac:(lia) Hpn ltac:(lia) BY1 SH1 GZ1 (Z.to_nat n) fx1 R1 p ltac:(lia) ltac:(lia) VC1 E10)
as (fx2 & R2 & MS2 & SP2 & KS2).
apply (EPIL fx2 R2 M1v MG1 AG1 SP2 S104 S96 S88 S80 S72 S64 S56 S48 S40 S32 S24 S16 S8).
+ intros k Hk. rewrite (KS2 k ltac:(revert k Hk; kin)). apply KS. revert k Hk. kin.
+ eapply msteps_trans; [exact MS| exact MS2].
Qed.
End Stage.
End PMBVAL.
