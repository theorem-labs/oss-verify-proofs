(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmBSrcKit PmCertKitG PmBB10P.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBB10 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBB10.PMBB10."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBB10.PMBB10.Loop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBB10P.PMBB10P."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "1list"; "1nat"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0FF"; "0HI"; "0IH"; "0IH'"; "0L"]; ["0LB"; "0LK"; "4Model"; "5bvmap"; "0M"; "0M'"; "0R"; "0R'"; "6mrestrict"; "7msteps"; "8credit"; "9ahid"; "9byte_at"; "9fframe"; "9ri_inv"; "9vml_of"]; [":img_clear"; ":u32_at"; ":u64_at"; ":u8_at"; ":writable"; ";zeros_at"; "<KEEPX"; "=goal_from"; "<head"; ">KS_ab10E_1"; ">aligned"; "?is_base10_spec"; "@FPState"; "@getr"; "@mkst"; "@seg_rom"]; ["Amem_grows"; "Bloaded_segments"; "0S"; "0SCFG_P"; "CIn"; "Dadd"; "Ddiv"; "Dland"; "Dle"; "Dlt"; "Dmodulo"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0a"]; ["0ar"; "0b"; "0c"; "0cr"; "0e"; "0fx"; "0fx'"; "0g"; "0i"; "0j"; "0model"; "0n"; "0p"; "0sp"; "EZ_to_bv"; "Ebv"]; ["Ebv_unsigned"; "0t"; "0t'"; "0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBB10.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition KEEPX : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Ltac kx_tac KS := intros k Hk; apply KS; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [inl|]); destruct Hk.
Definition head (R : bvmap 5 word) (S c e t : Z) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 16) /\ getr R (reg 5) = Z_to_bv 64 13 /\ getr R (reg 6) = Z_to_bv 64 2147450880 /\ getr R (reg 7) = Z_to_bv 64 8185
/\ getr R (reg 10) = Z_to_bv 64 c /\ getr R (reg 11) = Z_to_bv 64 c /\ getr R (reg 12) = Z_to_bv 64 t /\ getr R (reg 13) = Z_to_bv 64 e
/\ getr R (reg 14) = Z_to_bv 64 5 /\ getr R (reg 15) = Z_to_bv 64 10 /\ getr R (reg 16) = Z_to_bv 64 2 /\ getr R (reg 17) = Z_to_bv 64 1
/\ getr R (reg 28) = Z_to_bv 64 145632.
Section Loop.
Variable Mv : word -> option byte.
Variables (S ra p e : Z).
Hypothesis RA : L5.u64_at RSEGS Mv (S - 8) ra.
Hypothesis Hra : 0 <= ra < 2 ^ 64.
Hypothesis HS : 140735332487184 <= S <= 2 ^ 47.
Hypothesis HS16 : S mod 16 = 0.
Hypothesis IMG : L5.img_clear Mv 65536 1269760.
Hypothesis Hp : 1 <= p.
Hypothesis Hpe : p <= e.
Hypothesis He : e <= 2 ^ 47.
Hypothesis BY : forall c, p <= c < e -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS Mv c b.
Hypothesis SH : forall c, p <= c < e -> L5KA.zeros_at Mv (c / 8 + 2147450880) 1 \/ (exists v, 1 <= v <= 7 /\ L5.u8_at RSEGS Mv (c / 8 + 2147450880) v /\ c mod 8 < v).
Hypothesis TSH : forall g, 0 <= g < 6 -> L5KA.zeros_at Mv (2147469084 + g) 1.
Hypothesis TSH6 : L5.u8_at RSEGS Mv 2147469090 4.
Definition goal_from (fx : FPState) (R : bvmap 5 word) (pc : Z) : Prop :=
exists fx' R', msteps RSEGS (L5SAR.st fx R pc Mv) (L5SAR.st fx' R' 0xb207c Mv) /\ getr R' (reg 1) = Z_to_bv 64 ra /\ getr R' (reg 2) = Z_to_bv 64 S
/\ (forall k, In k KEEPX -> getr R' (reg k) = getr R (reg k)).
Lemma epi : ltac2:(TCodec.tc2 tcn__PmBB10 "N'Q<&Cy5'R?yR0%211%5241'6&Q=r1&R>&QLu2%211%42<1%7261&QNvQB+@%3221%:2@1%>3@61&Q7r3r2+fXSD%43321p061pQ>F1pT<M1").
Proof using RA Hra HS HS16. intros fx R.
intros R2.
cfeed PP (PMBB10P.ab10X_conc fx R Mv (fun j => match j with 2%nat => S | 40%nat => ra | _ => 0 end)) ltac:(first [assumption | unfold PMBB10P.aligned; lia | lia]).
destruct PP as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A1 & A2)).
assert (EM : M1 = Mv) by (apply functional_extensionality; exact FR). subst M1.
exists fx1, R1. split; [exact MS|]. split; [exact A1|]. split; [exact A2|]. kx_tac KS.
Qed.
Lemma back_edge : ltac2:(TCodec.tc2 tcn__PmBB10 "QE':'Q<&Cy5'R?yR0%211%5241&QIr4vR4%3221&Q8r3vQBr5r2%5543271'5&QHz%2218&QM+2+R0%3221%B2=1%9261&Q7r6+fWl4%332@1p051p0@1p0G1pU4Q31pQ>M1pT<Q41vR<%O21H%E2IN%G221%N5ML=Q0J+fXQ@%@3?M1p0B1p041p061pU4Q@1pQ>Q:1pT<QA1pL>1pT6QD1").
Proof using All. intros c IH fx R t.
intros Hc HD Ht. pose proof HD as (R2 & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R28).
cfeed PP (PMBB10P.ab10F_conc fx R Mv (fun j => match j with 2%nat => S | 33%nat => c | 34%nat => e | 36%nat => t | _ => 0 end)) ltac:(first [assumption | lia]).
destruct PP as (fx1 & R1 & M1 & MG & FR & FRZ & [(MS & KS & C0) | (MS & KS & A10 & A12 & C0)]);
(assert (EM : M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1.
- destruct (IH fx1 R1 t C0) as (fx2 & R2' & MS2 & B1 & B2 & KS2); [| exact Ht |].
{ repeat split; rewrite (KS _) by inl; assumption. }
exists fx2, R2'. split; [eapply msteps_trans; [exact MS| exact MS2]|]. split; [exact B1|]. split; [exact B2|].
intros k Hk. rewrite (KS2 k Hk). revert k Hk. kx_tac KS.
- destruct (epi fx1 R1 ltac:(rewrite (KS 2%nat) by inl; exact R2)) as (fx2 & R2' & MS2 & B1 & B2 & KS2).
exists fx2, R2'. split; [eapply msteps_trans; [exact MS| exact MS2]|]. split; [exact B1|]. split; [exact B2|].
intros k Hk. rewrite (KS2 k Hk). revert k Hk. kx_tac KS.
Qed.
Local Ltac tcase X g IH' :=
lazymatch goal with
| HRc : p <= ?c < e |- goal_from ?fx ?R _ =>
pose proof (X fx R Mv (fun j => match j with 2%nat => S | 33%nat => c | 34%nat => e | _ => 0 end)) as PT; cbn beta iota in PT;
L5SAR.feed PT ltac:(first [assumption | exact (TSH g ltac:(lia)) | lia]);
destruct PT as (fx1 & R1 & M1 & MG & FR & FRZ & (MS & KS & A10 & A11 & A12 & RST));
(assert (EM : M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1;
lazymatch type of A12 with getr _ _ = Z_to_bv 64 ?tv =>
(assert (HD1 : head R1 S (c + 1) e tv) by (repeat split; first [ assumption | (rewrite (KS _) by inl; assumption) ]));
destruct (back_edge (c + 1) IH' fx1 R1 tv ltac:(lia) HD1 ltac:(lia)) as (fx2 & R2' & MS2 & B1 & B2 & KS2);
exists fx2, R2'; split; [eapply msteps_trans; [exact MS| exact MS2]|]; split; [exact B1|]; split; [exact B2|];
intros k Hk; rewrite (KS2 k Hk); revert k Hk; kx_tac KS
end
end.
Lemma idx_range : ltac2:(TCodec.tc2 tcn__PmBB10 "Q1':'5&QHzr1%3221+WO%5231%7231&QI&QG&QJ&QEr2+_oooooooooonC%3221&QM+2+R0%3221%9251%;21?+=%>221+Q=r3%H221+QI%J231%L231p071p0G1pT4Q01").
Proof. intros b.
intros Hb H. rewrite (Z.land_ones _ 8) in H by lia. change (2 ^ 8) with 256 in H.
destruct (Z_lt_le_dec b 45) as [LT|GE].
- rewrite (Z.mod_small (b + 18446744073709551571) (2 ^ 64)) in H by lia.
replace (b + 18446744073709551571) with ((b + 211) + 72057594037927935 * 256) in H by lia. rewrite Z_mod_plus_full in H. rewrite Z.mod_small in H by lia. lia.
- replace (b + 18446744073709551571) with ((b - 45) + 1 * 2 ^ 64) in H by lia. rewrite Z_mod_plus_full in H. rewrite Z.mod_small in H by lia.
rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma tbl : ltac2:(TCodec.tc2 tcn__PmBB10 "V<':'Q<&Cy5'R?yR0%211%5241&QI&QEr5+1%3221vR4%6221&Q8r3vQBr6%:218r2%6554281'5&QHz%2219&QM+2+R0%3221%F2>1%9261&Q7+fWl4%23@H1p041p0?1p0G1pU6Q61pQ>Q01pT<Q71vR<%C21Q0%Q32Q1N%F221%F2EQ3+WO%H2Q51%J231'6&Q=&R>&QLu2%211%42QD1%62Q81&QN+@%22Q:1%92QG1%<3QG51r4u5%<11%>2QN1%@241+=%A2QO1%D3QO31u6%C11%E2R51%G2QO1+QoooPP0%H2R61%K3R631u7%J11%L2R<1%N2QN1+WoI%O2R=1%Q23R=31r7u:%Q211%Q42RD1%Q6241r;%Q72RE1%Q:3RE31r8u;%Q:11%Q<2RL1%Q>241r<%Q?2RM1%QB3RM31r9u=%QB11%QD2S41%QF241%QF2S4RL%QI3S421r:u>%QI11%QK2S;1%QM241+5%QN2S<1%R13S<31u?%R011%R22SB1%R42M1+:%R52SC1%R83SC31u@%R711%R92SI1%R;2L1%R;2SIS3%R>3SI21r=uA%R>11%R@2T01%RB241%RB2T0SJ%RE3T021r>uL%RE11%RG2T71%RI241+T^W0%RJ2T81%RM3T831&R@r?u<%RN11%S02T@1%S2241%62T@1&QJ&QK+4&QGrB+_oooooooooonC%TC221%721T0%521S@%8271%:21T3%TH21E%<21T5%SB3U3>1&QFrC%TM21;%A21T:%B21T<%T?2T>1%62RI1%B21U0%SC21TD%G21T@%TG2U31rD%U721E%K21TD%I21T4%U;21S@+fWn8%TE3@K1p031p091p0E1p0Q;1p0QD1p0QL1p0R31p0R;1p0RD1p0RL1p0S51p0S>1p0SF1p0SN1p0T71p0TE1p0TJ1pQ>V01pT<V71pNU11pT4V:1pT6V;1").
Proof using All. intros c b IH' fx R.
intros HRc Hb R2 R5 R6 R7 R10 R11 R13 R14 R15 R16 R17 R28 E12 BIT IDX.
pose proof (idx_range b Hb IDX) as HB.
assert (HB' : b = 45 \/ b = 46 \/ b = 47 \/ b = 48 \/ b = 49 \/ b = 50 \/ b = 51 \/ b = 52 \/ b = 53 \/ b = 54 \/ b = 55 \/ b = 56 \/ b = 57) by lia.
destruct HB' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
(assert (R12 : getr R (reg 12) = Z_to_bv 64 (bv_unsigned (getr R (reg 12)))) by (symmetry; apply Z_to_bv_bv_unsigned)); rewrite E12 in R12; vm_compute in BIT.
- tcase PMBB10P.ab10T0_conc 0 IH'.
- exfalso. apply BIT. reflexivity.
- exfalso. apply BIT. reflexivity.
- tcase PMBB10P.ab10T3_conc 1 IH'.
- tcase PMBB10P.ab10T4_conc 2 IH'.
- tcase PMBB10P.ab10T5_conc 2 IH'.
- tcase PMBB10P.ab10T6_conc 3 IH'.
- tcase PMBB10P.ab10T7_conc 3 IH'.
- tcase PMBB10P.ab10T8_conc 4 IH'.
- tcase PMBB10P.ab10T9_conc 4 IH'.
- tcase PMBB10P.ab10T10_conc 5 IH'.
- tcase PMBB10P.ab10T11_conc 5 IH'.
- tcase PMBB10P.ab10T12_conc 0 IH'.
Qed.
Local Ltac bexit c t b IH' :=
lazymatch goal with
| MS : msteps _ _ (L5SAR.st ?fx1 ?R1 0xb2074 _), KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x), R2 : getr ?R (reg 2) = _ |- goal_from _ ?R _ =>
destruct (epi fx1 R1 ltac:(rewrite (KS 2%nat) by inl; exact R2)) as (fx2 & R2' & MS2 & B1 & B2 & KS2);
exists fx2, R2'; split; [eapply msteps_trans; [exact MS| exact MS2]|]; split; [exact B1|]; split; [exact B2|];
intros k Hk; rewrite (KS2 k Hk); revert k Hk; kx_tac KS
| MS : msteps _ _ (L5SAR.st ?fx1 ?R1 0xb2030 _), KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x) |- goal_from _ ?R _ =>
let tv := lazymatch goal with _ : getr R1 (reg 12) = Z_to_bv 64 5 |- _ => constr:(5) | _ => t end in
assert (HD1 : head R1 S (c + 1) e tv) by (repeat split; first [ assumption | (rewrite (KS _) by inl; assumption) ]);
lazymatch type of HD1 with head _ _ _ _ ?tv =>
destruct (back_edge (c + 1) IH' fx1 R1 tv ltac:(lia) HD1 ltac:(lia)) as (fx2 & R2' & MS2 & B1 & B2 & KS2);
exists fx2, R2'; split; [eapply msteps_trans; [exact MS| exact MS2]|]; split; [exact B1|]; split; [exact B2|];
intros k Hk; rewrite (KS2 k Hk); revert k Hk; kx_tac KS
end
| MS : msteps _ _ (L5SAR.st ?fx1 ?R1 0xb1fc8 _), KS : forall x, In x _ -> getr ?R1 (reg x) = getr ?R (reg x) |- goal_from _ ?R _ =>
assert (TB : goal_from fx1 R1 0xb1fc8) by (apply (tbl c b IH' fx1 R1); first [ assumption | (rewrite (KS _) by inl; assumption) | lia ]);
destruct TB as (fx2 & R2' & MS2 & B1 & B2 & KS2);
exists fx2, R2'; split; [eapply msteps_trans; [exact MS| exact MS2]|]; split; [exact B1|]; split; [exact B2|];
intros k Hk; rewrite (KS2 k Hk); revert k Hk; kx_tac KS
end.
Local Ltac body X c t b IH' :=
lazymatch goal with |- goal_from ?fx ?R _ =>
pose proof (X fx R Mv (fun j => match j with 2%nat => S | 33%nat => c | 34%nat => e | 36%nat => t | 37%nat => b | _ => 0 end)) as PP; cbn beta iota in PP;
L5SAR.feed PP ltac:(first [assumption | lia]);
destruct PP as (fx1 & R1 & M1 & MG & FR & FRZ & EX); (assert (EM : M1 = Mv) by (apply functional_extensionality; exact FR)); subst M1;
repeat (destruct EX as [EX|EX]; [decompose [and] EX; clear EX; bexit c t b IH'|]); decompose [and] EX; clear EX; bexit c t b IH'
end.
Lemma loop_ms : ltac2:(TCodec.tc2 tcn__PmBB10 "QD'2'Q<&Cy5'R?yR0%211%5241':'6&QLr5%211&QNvR4r2%3221%83951'5&QHvR<r3%3221&QI%123:%7231&Q8vQBr4%35B21?8z%<213&QM+2+R0%3221%=281%C261&Q7r8r7+fWl4%43321p061p0?1p0D1p0M1pU4Q71pT6Q81pQ>Q:1pT<QA1pTDQC1").
Proof using All.
induction j as [|j IH]; intros fx R c t Hj Hc HD Ht; [lia|].
assert (IH' : forall fx R t', c + 1 < e -> head R S (c + 1) e t' -> 0 <= t' < 2 ^ 64 -> goal_from fx R 0xb1f84).
{ intros fx' R' t' Hc' HD' Ht'. apply (IH fx' R' (c + 1) t'); [lia| lia| exact HD'| exact Ht']. }
pose proof HD as (R2 & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R28).
destruct (BY c Hc) as (b & Hb & Ub).
destruct (SH c Hc) as [Z0 | (v & Hv & Uv & Hcv)].
- body PMBB10P.ab10BZ_conc c t b IH'.
- assert (L7e : Z.land c 7 = c mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
assert (L7 : 0 <= Z.land c 7 < v) by (rewrite L7e; pose proof (Z.mod_pos_bound c 8); lia).
assert (HV : v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) by lia.
destruct HV as [->|[->|[->|[->|[->|[->| ->]]]]]].
+ body PMBB10P.ab10P1_conc c t b IH'.
+ body PMBB10P.ab10P2_conc c t b IH'.
+ body PMBB10P.ab10P3_conc c t b IH'.
+ body PMBB10P.ab10P4_conc c t b IH'.
+ body PMBB10P.ab10P5_conc c t b IH'.
+ body PMBB10P.ab10P6_conc c t b IH'.
+ body PMBB10P.ab10P7_conc c t b IH'.
Qed.
End Loop.
Lemma entry_piece : ltac2:(TCodec.tc2 tcn__PmBB10 "XM'Q<&Cy5'R?yR0%211%5241'3y8%611%311p061':'5&QHzr3%3221&QI&QM+2+R0%3221%5271%;271'6&Q=r8&R>&QLu2%211%42N1%7261r6%72O1%;3O31r9u:%:11%<2Q61%?241%A3Q517r:u;%@11%B2Q<1%E241%G3Q;1=&Q0+RPP0+QVhP0%33921&Q2&QAr;+QWbaH+QoooPP0%544321&Q1r<+QWbb0+1%449321+SoomohPTP@%QC215+TPPPPPPPP0%QE271%QG231&Q:r=+@%3221&Q4r?&QNr>%2216%54H417'9%QG3R4:R1%R32C5%3221%R529A%R62R5:+QooooO%R82<1%R:231'7&Q@rFr1%3221%R?2R>2%R<23R8%RB221&8rG+8%H221r2%RG221&QE%1245%RF241%RL241%:11r4%R@2S8RL%211rI%113%RG3S631p071p0C1pTBS71'I&Q>rH+fWi8%RL2SD1&Q?%11R4%655J3Q11+fXSD%S12SI1%95S>J1Q34%;3R941'2&QD&Q6%233Q81%S71Q0%S92T31%S<2K1%S=2I2%S?3T321p061pU::1%SA2Q7S;rE%R221R6%SB2T:1%SF3T:41rC%SH3T51T2%R726Q@&R@u1%SH11%SJ2TD1%SM2QF1%52TD1%S44S3QN71%T=291%T>2<1%T?2B1%T@2N1+fWl4%T32TK1%Q;5T@QL1R5Q6%Q=3S;Q61&Q9%Q23Q3R81p01LpU:Q51u5%T:11%T<2U61%T?2R51+=%T?2U71%TC3U731u6%TA11%TC2U=1%TF2R<1%TE2U=SH%TI3U=21u7%TG11%TI2UC1%TL2RB1+WoI%TL2UD1%U03UD31%U02RFT<rD%U02UH1%U43UH31u<%U211%U42UN1%U72RM1%U62UNUC%U:3UN21u=%U811%U:2V41%U=2S31%S22=QH%U=2V51%UA3V531u>%U?11%UA2V;1%UD2S:1+5%UD2V<1%UH3V<31u?%UF11%UH2VB1%UK2SA1+:%UK2VC1%UO3VC31u@%UM11%UO2VI1%V22SH1%V12VIV9%V53VI21uA%V311%V52VO1%V82SN1%V72VOU5%V;3VO21uL%V911%V;2W51%V>2T41+T^W0%V>2W61%VB3W631&QJ%U22RMVN%221VH%W12UA1%W321RG%W4261%W52>1%W62E1%W72L1%W82Q41%W92Q<1%W:2QD1%W;2QK1%W<2R01%W=2R81%W>2R?1%W?2S=1%W@2RH1%WA2RM1%U@2S21%WC2T=1%WD2U51qQ<WG1%U;2WH1qQ@WN1%U=2WO1qT>X61%U?2X71p0UA1p0UF1p0UH1p0UM1p0V41p0V91p0V?1p0VE1p0VL1p0W11p0W81p0W?1p0WL1p0WM1p0WN1pTHX;1pTJX<1pTLX=1pQ:X?1pQ>XE1pT<XL1").
Proof. intros fx R M sp p n.
intros H2 Hp0 Hn0 R2 R10 R11 IM SBc FLc HS AL WR Hpn Hp47 Hn26.
destruct (Z.eq_dec p 0) as [P0|P1].
- assert (N0 : n = 0) by (destruct Hpn as [X|X]; lia). subst p n.
cfeed PP (PMBB10P.ab10E00_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => 0 | 35%nat => 0 | _ => 0 end)) ltac:(first [assumption | lia]).
destruct PP as (fx1 & R1 & M1 & MG & _ & FR & (MS & KS & E2 & _ & _ & _ & _ & C1)).
exists fx1, R1, M1. split; [exact MG|]. split; [exact FR|]. left. split; [exact MS|]. split; [kx_tac KS|]. split; [exact E2|]. split; [reflexivity| exact C1].
- assert (P1' : 1 <= p) by lia.
cfeed PP (PMBB10P.ab10E_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => p | 35%nat => n | _ => 0 end)) ltac:(first [assumption | lia]).
destruct PP as (fx1 & R1 & M1 & MG & _ & FR & [(MS & KS & E2 & _ & _ & _ & _ & C0 & C1) | X]).
+ exists fx1, R1, M1. split; [exact MG|]. split; [exact FR|]. left. split; [exact MS|]. split; [kx_tac KS|]. split; [exact E2|].
split; [rewrite Z.sub_0_r, Z.mod_small in C0 by lia; lia| exact C1].
+ exists fx1, R1, M1. split; [exact MG|]. split; [exact FR|]. right. exact X.
Qed.
Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma u8_of_byte : ltac2:(TCodec.tc2 tcn__PmBB10 "F'R?yR0%211'3y8%511%311p051':&Lr3r2r1%43321&Q3&QAr4%342176p051pU8;1pT0<1pQ:>1").
Proof. intros M a v. intros B. unfold L5.u8_at. cbn [rdn]. unfold byte_at in B. rewrite B. reflexivity. Qed.
Lemma table_shadow : ltac2:(TCodec.tc2 tcn__PmBB10 "R1'1'4':%2211%411&M%611&J'R?yR0%211'3y8%511%311p051'B&Nv<r7r6r5r4r3r2&Or1%211%;8:9876541'5&QHz%2216&QI+6%2291%7241&Q5&H&K%12DB%321D&QE+QoooahL%221D+1%93521p0;1pT@Q>1&Q3&QA%<2MK%>21M+Qoooai2+4%645321%K281p0M1pTFQ:1pQ:Q<1p2QH1pT8QF1pQ4QH1pHQI1pQ2QL1").
Proof. intros LB FF LK cr Aw M model.
intros HH. pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as G. rewrite (aicl_globals IL ILY) in G.
rewrite Forall_forall in G. destruct (G (0x238e0, 52) ltac:(cbn; tauto)) as ((SZ & SP) & SA). cbn [fst snd] in SZ, SP, SA.
change (52 / 8) with 6 in SZ. change (52 mod 8) with 4 in SP. specialize (SP ltac:(lia)).
unfold HeapIfaceA.S, HeapIfaceA.SB in SP. change (0x238e0 / 8 + 2147450880 + 6) with 2147469090 in SP.
assert (IS : forall x, 2147469084 <= x <= 2147469090 -> in_shadow_of 0x238e0 52 x).
{ intros x Hx. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB. change (0x238e0 / 8 + 2147450880) with 2147469084.
change ((0x238e0 + 52 - 1) / 8 + 2147450880) with 2147469090. exact Hx. }
split.
- intros g Hg. apply (proj2 (L5A.zeros_at_vis (ahid Aw model) M (2147469084 + g) 1 (L5A.avis_of_shadow_allowed Aw model 0x238e0 52 (2147469084 + g) 1 SA ltac:(intros i Hi; apply IS; lia)))).
intros j Hj. pose proof (SZ g ltac:(lia)) as B. unfold byte_at in B. unfold HeapIfaceA.S, HeapIfaceA.SB in B. change (0x238e0 / 8 + 2147450880) with 2147469084 in B.
replace (2147469084 + g + j) with (2147469084 + g) by lia. exact B.
- apply (proj2 (L5A.u8_at_vis (ahid Aw model) M 2147469090 4 (L5A.avis_of_shadow_allowed Aw model 0x238e0 52 2147469090 1 SA ltac:(intros i Hi; apply IS; lia)) ltac:(lia) ltac:(lia))).
apply u8_of_byte. exact SP.
Qed.
Theorem is_base10_ok : ltac2:(TCodec.tc2 tcn__PmBB10 "6&Q;vQCv?vR0v<%544321").
Proof.
unfold PMB.is_base10_spec, PMSPA.is_base10_spec, PMSPA.scan_spec. cbn [pa_is_base10 PMB.AD ADDR_A].
intros fx R M model K LB FF LK Aw cr p n sp r HH AM K0 ENT FRM FRS A10 A11 Hn Hp Hp0 Hpn DEF ACC VIS LOC BASE KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
change (PMSPA.pm_scr 0) with 12288 in *.
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 12288 16 HH ASTK ltac:(lia)) as (SL16 & SH16 & V3).
pose proof (table_shadow LB FF LK cr Aw M model HH) as (TS0 & TS6).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (HP01 : n = 0 \/ 1 <= p) by (destruct Hp0 as [X|X]; [left; exact X| right; lia]).
pose proof (entry_piece fx R MV sp p n) as PP.
L5SAR.feed PP ltac:(first [assumption | unfold PMBB10P.aligned; lia | lia]).
destruct PP as (fx1 & R1 & M1v & MG1 & FRZ1 & EX).
set (P := fun a => sp - 8 <= a < sp - 8 + 8).
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
assert (TS1 : forall g, 0 <= g < 6 -> L5KA.zeros_at M1v (2147469084 + g) 1).
{ intros g Hg j Hj. rewrite AG1 by (unfold P; lia). apply (TS0 g Hg j Hj). }
assert (TS61 : L5.u8_at RSEGS M1v 2147469090 4).
{ apply (L5C.u8_at_agree RSEGS MV M1v); [intros i Hi; rewrite AG1; [reflexivity| lia| unfold P; lia]| lia| lia| exact TS6]. }
assert (FIN : forall fx2 R2, msteps RSEGS (L5SAR.st fx R 0xb1f28 MV) (L5SAR.st fx2 R2 0xb207c M1v) -> getr R2 (reg 1) = Z_to_bv 64 r ->
getr R2 (reg 2) = Z_to_bv 64 sp -> (forall k, In k KEEPX -> getr R2 (reg k) = getr R (reg k)) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb1f28 M model) K).
{ intros fx2 R2 MSA B1 B2 KSA. unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx2 R 0xb1f28 R2 0xb207c M1v P K HH AM MSA MG1 AG1).
{ intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
apply (PMBSK.ret_exit L ar C HI LY HIok fx2 R2 M1 model1 K _ FF LK cr Aw 0xb207c r (ltac:(oW' 0xb207c%Z)) HH1 AM1 (ltac:(oF' 0xb207c%Z)) eq_refl (ltac:(oD' 0xb207c%Z)) B1 ltac:(lia) Hr2).
intros model2 MRT2 AM2 HH2.
apply (KONT fx2 R2 M1 model2).
- apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx.
destruct Hx as [<-|Hx]; [rewrite B2, Rsp; reflexivity|]. apply KSA. exact Hx.
- intros x Ox. rewrite <- (Z_to_bv_bv_unsigned _ x). apply FR1; [apply bv_unsigned_in_range|].
intros Px. unfold P in Px. apply (Ox (sp - 12288, 12288)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. lia.
- exact MGM1.
- eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
- exact AM2.
- exact HH2. }
assert (HR : 0 <= r < 2 ^ 64) by lia.
destruct EX as [(MS & KS & E2 & C0 & C1) | (MS & KS & E2 & E5 & E6 & E7 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E28 & C0 & C1)];
rewrite Rra, L5.unsigned_lit in C1 by lia.
-
destruct (epi M1v sp r C1 HR ltac:(lia) A16 fx1 R1 E2) as (fx2 & R2 & MS2 & B1 & B2 & KS2).
apply (FIN fx2 R2 ltac:(eapply msteps_trans; [exact MS| exact MS2]) B1 B2).
intros k Hk. rewrite (KS2 k Hk). revert k Hk. kx_tac KS.
-
rewrite Z.sub_0_r, Z.mod_small in C0 by lia.
assert (Hp1 : 1 <= p) by (destruct Hp0 as [X|X]; lia).
assert (HD : head R1 sp p (p + n) 0).
{ repeat split; first [assumption | (rewrite (KS _) by inl; assumption)]. }
destruct (loop_ms M1v sp r p (p + n) C1 HR ltac:(lia) A16 IMG1 Hp1 ltac:(lia) Hpn BY1 SH1 TS1 TS61 (Z.to_nat n) fx1 R1 p 0 ltac:(lia) ltac:(lia) HD ltac:(lia))
as (fx2 & R2 & MS2 & B1 & B2 & KS2).
apply (FIN fx2 R2 ltac:(eapply msteps_trans; [exact MS| exact MS2]) B1 B2).
intros k Hk. rewrite (KS2 k Hk). revert k Hk. kx_tac KS.
Qed.
End Stage.
End PMBB10.
