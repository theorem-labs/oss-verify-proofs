(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JatInitCache JatPopulate1 ArtRuns JatCls JatFp JatClsRep JatClsGfa2 JatClsRefill JatCARSpec ArtBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapPure () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["0BUDGET"; "1bool"; "1length"; "1list"; "1nil"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2or"; "3Z"; "0KMAX"; "0LENMAX"; "0RES"; "4art_EVOK"]; ["4art_cost_sum"; "5aev"; "6art_ca_events"; "6art_ca_pre"; "7art_cls"; "7art_cls_mfa'"; "7art_cls_needs_populate"; "7art_cls_new"; "7art_cls_ok"; "7art_evok_list"; "7cl_cache"; "7cl_free"; "7cl_mfa"; "7cl_mu"; "8In"; "9add"]; ["9gt"; "9le"; "9lt"; "9mul"; "9of_nat"; "9pow"; "9sub"; "0c"; "0cl"; "0k"; "0kbase"; "0km"; "0log"; "0qs"; "0spb"; "0tot"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma art_new_le : ltac2:(TCodec.tc2 tcn__JatWrapPure "I';'D'8&Q1+1r2%3221+N%5231%7231&Hr3%2217z&Gr4%2215%>241+XP0%@231%B231p091p0=1pRBF1pR@H1").
Proof.
intros c cl Hc (_ & (Hau0 & Haumu) & Hrem & _). destruct (art_class_size_facts c Hc) as (Hsz & _). unfold art_cls_new.
set (sz := AsanTab.class_size c) in *. split; [apply Z.div_pos; lia|].
assert ((cl_mu cl + 262144 - cl_au cl) / sz < 8193); [|lia]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_mfa_step := (ltac2:(TCodec.tc2 tcn__JatWrapPure "Q?';'D'8&Q1+1r2%3221+N%5231%7231&Hr3%2217&O&Q4&2&K%116%32B1%511&Gr4%221;%:241':'9&Er1%2271&L%119%63O31&Q0&Q3+4%2218%4216+XPP0%I281%>3Q7;1%Q6241%A2:1tS0Q:C1p0O1p0Q31pRBQ<1pR@Q>1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_mfa_step) 0%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_mfa_step) 1%nat 0%nat).
Lemma art_mfa_step : ltac:(sec_stmt2 constr:(SEC_T_art_mfa_step) 2%nat 0%nat).
Proof.
intros Hc OK tot.
pose proof (art_new_le c cl Hc OK) as Hnew. fold tot.
destruct OK as (_ & _ & _ & _ & _ & _ & (kf & Emfa) & (Hmfa0 & Hmfa1) & Hnf4 & _).
unfold art_cls_mfa'. destruct (4 * tot <=? cl_mfa cl) eqn:E; [left; reflexivity|right]. apply Z.leb_gt in E. split; [lia|].
assert (Hlo : 262144 * kf < 4 * tot) by lia. assert (Hhi : 4 * tot <= 262144 * kf + 32768) by (unfold tot; lia).
assert (Eq : (4 * tot + 262143) / 262144 = kf + 1). { symmetry. apply (Z.div_unique _ 262144 _ (4 * tot + 262143 - 262144 * (kf + 1))); lia. }
rewrite Eq. lia.
Qed.
End SE.
Lemma art_room_of_credit : ltac2:(TCodec.tc2 tcn__JatWrapPure "R0';'D'8&Q1+1r3%3221+N%5231%7231&Hr4%2217&O&Mr5%211&Q3+XPP0%2218%7241&Q6+S`PPPP0%2215%E241+4&Q4&2&Kr6%211%42O1%611%@281+XP0%B2:1%C21E%H241+`PPPP0%B21E%Q5231r7%L11%N21I%Q921F&E%B15%D2Q?1%F11&Gr8%221:%Q7241%82<1%QC21@%QE2;1p0@1p0Q11p0QD1p0Q?1p0QC1pRDQM1pRBQM1pR@QO1").
Proof.
intros c cl k Hc OK Hk R1 R2. split; [lia|]. pose proof (art_new_le c cl Hc OK) as Hnew.
destruct (art_mfa_step c cl Hc OK) as [E|(Hgt & E)]; cbv zeta in *; rewrite E.
- destruct OK as (_ & _ & _ & _ & _ & _ & _ & (_ & H) & _). exact H.
- destruct OK as (_ & _ & _ & _ & _ & _ & (kf & Emfa) & _ & Hnf4 & _).
assert (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912 - 262144) by lia.
assert (262144 * kf < 536870912 - 262144) by lia. assert (kf + 1 <= 2047) by lia. lia.
Qed.
Lemma art_ca_cost : ltac2:(TCodec.tc2 tcn__JatWrapPure "Q0';'D'8&Q1+1r2%3221+N%5231%7231&Hr3%2217z&@&Br5r4%33217%511%A271&Q5+2+C%3221%F261%H261p0?1p0C1pRBL1pR@N1pRNO1").
Proof.
intros spb c cl Hc OK. unfold art_ca_events, art_refill_events. destruct (cl_cache cl); [|cbn; lia].
destruct (art_cls_needs_populate c cl); [|cbn; lia].
destruct (art_mfa_step c cl Hc OK) as [E|(Hgt & E)]; cbv zeta in *.
- pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & Hnf4 & _).
match goal with |- context [if ?b then _ else _] => destruct b eqn:Eb end; cbn [art_cost_sum fold_right art_cost]; [lia|].
rewrite E. lia.
- match goal with |- context [if ?b then _ else _] => destruct b eqn:Eb end; cbn [art_cost_sum fold_right art_cost]; [lia|]. rewrite E. lia.
Qed.
Lemma art_ca_evok : ltac2:(TCodec.tc2 tcn__JatWrapPure "SH'3'6';%2211%411'A%611'D'8&Q1+1r3%3221+N%5231%7231&Hr4%2217'9r8&Q3+RPP0r7%3221%63G51&Q2r9%2251r:&O%12;9%G231&N(5+TPPPRTP0%24Q2Q291r@%53Q321&M%11D+XPP0%E21C%H3Q931z%Q421I%Q>1Q<&J%11C(4%11Q@%Q03531'1&Fr<r;%3221(7%Q73621%D15%N21C+S`PPPP0%QE221&E&Q4&2&K%11=%32R21%511&Gr=%221B%Q;241%;2D1+`PPPP0%R3221%R52?1p0D1p0L1&@%11Q<&Q5+2+C%3221%QH251rC%R?221&I&?rErDrB%443271rA&B%13QLJQ;%93431p0;1p0E1p0QH1p0QK1p0R11p0R81p0R=1p0RA1p0RI1p0RM1pRHS;1pRBS71pR@S=1pRFS>1pRLS?1pRNS@1pRJS=1pJSB1pLSC1p2SD1pNSC1").
Proof.
intros RES BUDGET LENMAX KMAX log spb qs kbase c cl km Hc OK Espb Hk1 Hk2 HRES Emu Hkm Room HB.
unfold art_ca_events, art_refill_events. destruct (cl_cache cl) eqn:Ec; [|exact I].
destruct (art_cls_needs_populate c cl) eqn:NP; [|exact I]. destruct (Room eq_refl eq_refl) as (R1 & R2).
pose proof OK as (_ & _ & _ & _ & _ & _ & (kf & Emfa) & (Hmfa0 & _) & _).
assert (EV1 : art_EVOK RES BUDGET LENMAX KMAX log (AMmapFixed (spb + c * 2 ^ 32 + cl_mu cl) 262144)).
{ cbn [art_EVOK]. split. { rewrite Espb, Emu. replace (65536 * qs + c * 2 ^ 32 + 262144 * km) with ((16 * qs + c * 2 ^ 20 + 64 * km) * 4096) by lia. apply Z_mod_mult. }
split; [reflexivity|]. split; [lia|]. split; [exists (kbase, 0x2000011000); cbn [fst snd]; split; [exact HRES|lia]|].
rewrite art_cost_sum_snoc. cbn [art_cost]. lia. }
destruct (art_mfa_step c cl Hc OK) as [E|(Hgt & E)]; cbv zeta in *.
- match goal with |- context [if ?b then _ else _] => destruct b eqn:Eb end.
+ cbn [art_evok_list]. split; [exact EV1|exact I].
+ apply Z.leb_gt in Eb. exfalso. unfold art_cls_mfa' in E. rewrite (proj2 (Z.leb_gt _ _) Eb) in E.
pose proof (Z.div_mod (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) + 262143) 262144 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) + 262143) 262144 ltac:(lia)) as Rm. lia.
- match goal with |- context [if ?b then _ else _] => destruct b eqn:Eb end; [apply Z.leb_le in Eb; lia|].
cbn [art_evok_list]. split; [exact EV1|]. split; [|exact I]. rewrite E. replace (cl_mfa cl + 262144 - cl_mfa cl) with 262144 by lia.
cbn [art_EVOK]. split. { rewrite Espb, Emfa. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with ((16 * qs + c * 2 ^ 20 + 917504 + 64 * kf) * 4096) by lia. apply Z_mod_mult. }
split; [reflexivity|]. split; [lia|]. split; [exists (kbase, 0x2000011000); cbn [fst snd]; split; [exact HRES|rewrite E in R2; lia]|].
rewrite !art_cost_sum_snoc. cbn [art_cost]. lia.
Qed.
Lemma art_cls_ok_ca_pre : ltac2:(TCodec.tc2 tcn__JatWrapPure "QL';'D'8&Q1+1r2%3221+N%5231%7231&Hr3%2217'9'3%11?&J%116(4%11C%73531'1&Fr5r4%3221(7%>3621&O&M%117+XPP0%4221+S`PPPP0%O221&E&Q4&2&K%11@%32Q81%511&Gr6%221E%A241%;2G1+`PPPP0%Q=221%Q?2?1p0G1p0O1&C%12NM%Q<2O1p041p0Q<1p0Q@1pRBQI1pR@QK1").
Proof.
intros c cl Hc OK Room. unfold art_ca_pre. destruct (cl_cache cl) eqn:Ec; [|exact OK].
rewrite art_cls_refill_eq. apply art_cls_ok_take.
- apply art_cls_ok_pre_take; [exact Hc|exact OK|]. intros NP. exact (Room eq_refl NP).
- unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl); [cbn [art_cls_populate cl_cache]|]; exact Ec.
- apply art_pre_take_enough; assumption.
- pose proof (art_refill_n_range c ltac:(lia)). lia.
Qed.
