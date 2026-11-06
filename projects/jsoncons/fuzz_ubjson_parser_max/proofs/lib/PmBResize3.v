(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStep PmStepAB0 PmBRzKit PmBResizeP PmBReset1 PmBResize1 PmBResize2 PmTxtKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBResize3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBResize3.PMBRZ3.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw0"; "1app"; "1cons"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0FF"; "0HI"; "0K"; "0L"]; ["0LB"; "0LBo"; "0LK"; "0LK0"; "4Model"; "5bvmap"; "0M"; "0M'"; "0M0"; "0R"; "0R0"; "6credit"; "7fframe"; "7ri_inv"; "7vml_of"; "9u64_at"]; ["9u8_at"; "8SCFG"; ":mem_ok"; ":rs_regs"; ":saves"; ":stok"; ";VLong"; ";VShort"; ";pot_text"; ";tb_ok"; ";vs_own"; ";vstr"; ";vstr_at"; "<HV"; "<accA"; "<cfg"]; ["<credit_le"; "<scA"; "=FPState"; "=getr"; ">srealizes"; "?mem_grows"; "@amodel_ok"; "Aloaded_segments"; "0S"; "0SCFG_P"; "Badd"; "Ble"; "Blt"; "Bmodulo"; "Bmul"; "Bof_nat"]; ["Bpow"; "Bsub"; "0a"; "0ar"; "0c"; "0cr"; "0cr0"; "0fx"; "0k"; "0m"; "0model"; "0model0"; "0n"; "0n0"; "0o"; "0p"]; ["0s"; "CZ_to_bv"; "Cbv"; "Cbv_unsigned"; "0tg"; "0x"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
| solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMBRZ3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation vstr_at := (PM.vstr_at RSEGS PMSPA.accA).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (o n S r tg : Z) (s : PM.vstr).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis STK0 : L5CA.astk ar M0 S 14336.
Hypothesis AO : PMSPA.aobjA FF o 24.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hn1 : 0 <= n <= PM.vs_size s + PM.CHUNK.
Hypothesis Hn2 : n < 2 ^ 26 + PM.CHUNK.
Hypothesis OPN : PMB.opnew_spec L ar HI.
Hypothesis OPD : PMB.opdel_spec L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
(s' : PM.vstr) (tg' : Z) (cr' : credit),
regs_preserved R0 R' -> vstr_at M' o s' -> PM.vs_size s' = n -> PM.tb_ok s' tg' ->
(n <= PM.vs_cap s -> PM.vs_own s' = PM.vs_own s /\ tg' = tg) ->
L5CA.ahpres L ar LB FF S (PMSPA.pm_scr 1) [(o, 24)] M0 M' ->
PMSPA.credit_keep cr0 cr' (scA (PM.pot_text HV s tg)) (scA (PM.pot_text HV s' tg')) ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
ri_inv HI (PM.vs_own s' ++ LB) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
Definition saves (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
/\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
/\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
/\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22)))
/\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))).
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition stok (model : Model) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
L5CA.amodel_ok Aw model /\ model_rt model0 model /\ incl LK LK0 /\ incl Aw0 Aw.
Definition mem_ok (M : word -> option byte) : Prop :=
L5SAR.ek L ar LB FF S 14336 [(o, 24)] M0 M /\ L5SAR.dk L ar LB FF S 14336 M0 M /\ L5CA.astk ar M S 14336 /\ PMSPA.accA M o 24.
Let sub_in := PMBRZ1.sub_in.
Let vfacts := PMBRZ1.vfacts L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let bfacts := PMBRZ1.bfacts L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let fit_short := PMBRZ1.fit_short L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let fit_long := PMBRZ1.fit_long L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let grow_short := PMBRZ2.grow_short L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let grow_long := PMBRZ2.grow_long L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Let mem_ok_obj := PMBRZ2.mem_ok_obj L ar C IL HI LY HIok ICok ILY R0 M0 model0 K LB FF LK0 Aw0 cr0 o n S r tg s Rra0 RAok Rsp0 Rtp0 K0 STK0 AO Ho3 Hn1 Hn2 OPN OPD KONT.
Lemma sub_wrap1 : ltac2:(TCodec.tc2 tcn__PmBResize3 "Q2';&QKzr2%3221r3%5213&QL&R0+2+QO%3221%5271'9&QM&QJ&QN+_oooooooooooOr5%3221+R0%=2<1%8231r4%9221%;214&R1%1249%?3L31p0A1p0H1p0K1pTBQ01pU<Q11").
Proof. intros x k.
intros H0 H1 H2. replace (18446744073709551615 * x) with (- x + x * 2 ^ 64) by (clear - H0; lia). rewrite Z_mod_plus_full.
rewrite Zplus_mod_idemp_l. replace (- x + k) with (k - x) by (clear; lia). apply Z.mod_small. clear - H0 H1 H2. lia.
Qed.
Lemma sub_wrap2 : ltac2:(TCodec.tc2 tcn__PmBResize3 "Q7';&QKzr2%3221&QLr3%2214&R0+2+QO%3221%7261'9&QM&QJ&QN+_oooooooooooOr5%3221+R0%=2<1%8231r4%:213%:231%<215%<21:%>217&R1%127<+1%3221%D3Q151p0F1p0L1p0Q01pU>Q51pU<Q61").
Proof. intros x y.
intros H0 H1 H2. rewrite (Z.mod_small y) by (clear - H0 H1 H2; lia). rewrite (sub_wrap1 x y) by (clear - H0 H1 H2; lia).
replace (y - x + 18446744073709551615) with ((y - x - 1) + 1 * 2 ^ 64) by (clear; lia). rewrite Z_mod_plus_full. apply Z.mod_small. clear - H0 H1 H2. lia.
Qed.
Definition rs_regs (R : bvmap 5 word) : Prop :=
forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Lemma saves_of : ltac2:(TCodec.tc2 tcn__PmBResize3 "SJ'RByR0%211'5y8%511%311p051&O&QGr1&R1vQH+R@%3221&RC&QCvJ&RAy5&QOuH%211%5241%8271%:2H1%B4A@<1r2+R8%B2A1uG%;11%>2=1%A2@1%C2Q11%K4J861r3+R0%K2J1uF%D11%G2F1%J2I1%L2Q:1%Q44Q3861r4+QH%Q42Q31uE%M11%Q02O1%Q32Q21%Q52QC1%Q=4Q<861r5+Q@%Q=2Q<1uD%Q611%Q92Q81%Q<2Q;1%Q>2QL1%QF4QE861r6+Q8%QF2QE1uC%Q?11%QB2QA1%QE2QD1%QG2R51%QO4QN861r7+Q0%QO2QN1uB%QH11%QK2QJ1%QN2QM1%R02R>1%R84R7861r8+H%R82R71u9%R111%R42R31%R72R61%R92RG1%RA4R@861r9+@%RA2R@1u8%R:11%R=2R<1%R@2R?1%RB2S01%RJ4RI861r:+8%RJ2RI1u1%RC11%RF2RE1%RI2RH1%RK2S91%S34S2861&Q4r;%211p041p0>1p0H1p0Q21p0Q<1p0QF1p0R01p0R:1p0RD1p0RN1pQ>SB1").
Proof using All. intros M. intros. unfold saves. repeat split; assumption. Qed.
Lemma mem_ok_frame : ltac2:(TCodec.tc2 tcn__PmBResize3 "RD'RByR0%211'5y8%511%311p051'4'7';%2211%411&L%611&K'D&Mv=&2r5v@%33;21v<r4r3r2r7&Nr1%211%>8=9876541&Q2r8%211&QEr9%2214'8&QKz%221<&QL&R0+2+R0%3221%52B1%:271&:&R1vQH+R@%3221%?21L&QJ%1234%?2O1%D241%:11'9r<&RA%12QNQ6%311r=%113%73QM31p091p0E1pT6QL1r:%Q811p031p0Q51p0Q91p0Q=1pTFQM1p2R21pT<R01pQ6R21pQ4R51pQ@R;1pQ>R<1").
Proof using All. intros M M' LBo LK cr Aw model.
intros HH (EK & DK & STK & ACO) MG FR. pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (vfacts _ _ _ _ _ _ HH STK) as (_ & (O1 & O2 & O5) & _).
split; [|split; [|split]].
- apply (L5SAR.ek_trans L ar LB FF S 14336 _ M0 M M' EK).
apply (L5SAR.ek_piece L ar LB FF S 14336 _ M M' (fun a => S - 80 <= a < S - 80 + 80) FR). intros a Ha CA OW Wa.
destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 14336 a HH SPT (L5SAR.aclient_appb L ar LB LBo FF S 14336 a CA)) as [Z1|Z1]; lia.
- apply (L5SAR.dk_trans L ar LB FF S 14336 M0 M M' DK). apply (L5SAR.dk_grows L ar LB FF S 14336 M M' MG).
- exact (L5SAR.astk_grows ar M M' S 14336 STK MG).
- apply (PMFA.accA_agree M M' o 24); [| exact ACO].
apply (PMBRZK.agsh_frame M M' (fun a => S - 80 <= a < S - 80 + 80) o 24 FR); [intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| lia| lia].
Qed.
Lemma append_short : ltac2:(TCodec.tc2 tcn__PmBResize3 "T4'QB&Ey5'RByR0%211%5241'5y8%611%311p061'D'4&L%211'7';%2211%611&Q5r5r4r3%43321'9'Q;vR@(Q7%116%53431vR<&QJ%12;:%93A31&QK+1%221?'8zr6%6221+F%8231%6231&Q9vRD%22D1&Q@&QAv?&Q8&Q=vR3%2241%431L9%7261vR6%:221&QCr>&RA&QOu:%211%42QO1%7261vR>%72R01%Q<3R031r?u;%:11%<2R71%?241r9%?2R81%QD3R831&Q3r@%211&Q2%113&Q0&QGrA&QN+2r=%3221%7465G1&Mv=v@v<rB&N%11<%78654CQ9L31'QD&Q1vQI%211&Q?rErD+jZoDrC%56H4321=v>%;4J821p0=1p0F1p0O1p0Q21p0Q61p0Q?1p0QK1p0R71p0R;1p0RC1p0RG1p0RL1p0S31pTDS;1pTLS<1p2S;1pQ6S@1pTFSD1pQ>SF1pQDSL1pT@T31").
Proof using All. intros fx R M model LK Aw n0 m.
intros STO Es En Hm Hn0 TBOK CR A10 A11 RR MO B0 HH.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
destruct (PMTK.u64_of_defined RSEGS M o ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M o 24 o 8 ODEF); lia)) as (w & Hw & W0).
pose proof (PMTK.u64_low_byte RSEGS M o w (2 * n0) W0 B0 Hw ltac:(lia)) as WL.
pose proof (PMTK.short_size w n0 Hw WL Hn0) as HSS.
assert (TB0 : Z.testbit w 0 = false).
{ rewrite <- (Z.mod_pow2_bits_low w 8 0) by lia. change (2 ^ 8) with 256. rewrite WL. apply PMF.even_byte. }
assert (R2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by inl; exact Rsp0).
assert (B0v : L5.u8_at RSEGS MV o (2 * n0)).
{ apply (proj2 (L5A.u8_at_vis H M o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
assert (W0v : L5.u64_at RSEGS MV o w).
{ apply (proj2 (L5A.u64_at_vis H M o _ (L5A.avis_sub H o 24 o 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W0. }
pose proof (PMBRZP.aapS0_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | 36%nat => w | 43%nat => m | _ => 0 end)) as P.
cbn beta iota in P. rewrite HO in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia | apply PMF.even_byte]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & EX).
rewrite HSS in EX. rewrite (sub_wrap1 n0 22) in EX by lia.
unfold PMSPA.cfg.
assert (CONT : forall (fx1' : FPState) (R1' : bvmap 5 word) (pc1 : Z), msteps RSEGS (@mkst fx R (Z_to_bv 64 0xd2bf4) MV (seg_rom RSEGS)) (@mkst fx1' R1' (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
(forall M1 model1, ri_inv HI LB FF LK cr0 Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 -> mem_ok M1 ->
mrestrict (ahid Aw model) M1 = M1v -> L5.u8_at RSEGS M1 o (2 * n0) -> srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1' R1' pc1 M1 model1) K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd2bf4 M model) K).
{ intros fx1' R1' pc1 MS K1. unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr0 Aw M model fx fx1' R 0xd2bf4 R1' pc1 M1v (fun a => S - 80 <= a < S - 80 + 80) K HH AM MS MG1 FR1).
{ intros a Ha Wa. split; [apply (L5SAR.stack_client L ar LB FF 0 0 a); lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1' VV1. apply (K1 M1 model1 HH1 AM1 MRT1).
- exact (mem_ok_frame M M1 [] LK cr0 Aw model HH MO MGM1 FR1').
- exact VIS1.
- apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1'; lia| lia| lia| exact B0]. }
destruct EX as [(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
|(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)].
- apply (CONT fx1 R1 0xd2c58 MS1). intros M1 model1 HH1 AM1 MRT1 MO1 VIS1 B01.
assert (SV1 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
apply (fit_short fx1 R1 M1 model1 LK Aw n0 m).
+ split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
+ exact Es.
+ exact En.
+ exact Hm.
+ lia.
+ lia.
+ rewrite Es in TBOK. destruct TBOK as (_ & _ & X). exact X.
+ exact E2.
+ rewrite E8, A10. reflexivity.
+ exact E9.
+ exact E10.
+ rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 18))), E18. reflexivity.
+ exact E23.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply saves_of; (apply SV1; [lia| lia|]; rewrite <- (RR _) by inl; eassumption).
+ exact MO1.
+ exact B01.
+ exact HH1.
- apply (CONT fx1 R1 0xd2c80 MS1). intros M1 model1 HH1 AM1 MRT1 MO1 VIS1 B01.
assert (SV1 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
apply (grow_short fx1 R1 M1 model1 LK Aw n0 m).
+ split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
+ exact Es.
+ exact En.
+ exact Hm.
+ lia.
+ exact Hn0.
+ exact TBOK.
+ exact CR.
+ exact E2.
+ rewrite E8, A10. reflexivity.
+ exact E9.
+ exact E10.
+ rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 18))), E18. reflexivity.
+ exact E23.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply saves_of; (apply SV1; [lia| lia|]; rewrite <- (RR _) by inl; eassumption).
+ exact MO1.
+ exact HH1.
Qed.
Lemma append_long : ltac2:(TCodec.tc2 tcn__PmBResize3 "T2'QB&Ey5'RByR0%211%5241'5y8%611%311p061'D'4&L%211'7';%2211%611&Q5r7r6r5%43321'9'Q;vR@(Q6r4r3%33821%73651vR<&QJ%12<5%;3C31&QK+1%221:&Q9vRD%22?1&Q@&QAv?&Q8&Q=vR3%2241%431G9%7261vR6%:221&QCr?&RA&QOu:%211%42QJ1%7261vR>%72QK1%Q73QK31r@u;%:11%<2R21%?241r8%?2R31%Q?3R331&Q3rA%211&Q2%113&Q<&QG&Q>rB%45321DQG&Mv=(3(6r=%24R7R71Q1v@%53R821v<rC&N%11=%<8;54EQ;N31'QD&Q1vQI%211&Q?rFrE+jZoDrD%56J4321=v>%;4L821p0=1p0K1p0Q11p0Q41p0Q81p0QA1p0QM1p0R91p0R=1p0RA1p0RF1p0RO1pTDS71pU0S81pTLS91pT:S:1p2S91pQ6S>1pTFSB1pQ>SD1pQDSJ1pT@T11").
Proof using All. intros fx R M model LK Aw c n0 p m.
intros STO Es En Hm TBOK CR A10 A11 RR MO VS HH.
pose proof MO as (EK & DK & STK & ACO). pose proof STO as (AM & MRT & ILK & IAW).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
rewrite Es in VS. destruct VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & ACP).
destruct (vfacts _ _ _ _ _ _ HH STK) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (WST : L5.writable RSEGS MV (S - 80) 80).
{ apply (proj2 (L5A.writable_vis H M (S - 80) 80 (VSTK (S - 80) 80 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5SAR.astk_writable ar M S 14336); [exact STK| lia| lia| lia]. }
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (Dof : S - 80 + 80 <= o \/ o + 24 <= S - 80) by lia.
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
pose proof (PMF.u8_of_u64 RSEGS M o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
assert (TB1 : Z.testbit (c + 1) 0 = true) by (rewrite <- (Z.mod_pow2_bits_low (c + 1) 8 0) by lia; exact ODB).
assert (EC : 2 * ((c + 1) / 2) = c) by (pose proof (Z.div_mod (c + 1) 2 ltac:(lia)) as X; rewrite Z.add_mod, Hce in X by lia; cbn in X; lia).
assert (R2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by inl; exact Rsp0).
assert (B0v : L5.u8_at RSEGS MV o ((c + 1) mod 256)).
{ apply (proj2 (L5A.u8_at_vis H M o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
assert (W0v : L5.u64_at RSEGS MV o (c + 1)).
{ apply (proj2 (L5A.u64_at_vis H M o _ (L5A.avis_sub H o 24 o 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W0. }
assert (W8v : L5.u64_at RSEGS MV (o + 8) n0).
{ apply (proj2 (L5A.u64_at_vis H M (o + 8) _ (L5A.avis_sub H o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W8. }
pose proof (PMBRZP.aapL0_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 36%nat => c + 1 | 43%nat => m | _ => 0 end)) as P.
cbn beta iota in P. rewrite HO in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FR1 & EX).
rewrite EC in EX. rewrite (sub_wrap2 n0 c) in EX by lia.
unfold PMSPA.cfg.
assert (CONT : forall (fx1' : FPState) (R1' : bvmap 5 word) (pc1 : Z), msteps RSEGS (@mkst fx R (Z_to_bv 64 0xd2bf4) MV (seg_rom RSEGS)) (@mkst fx1' R1' (Z_to_bv 64 pc1) M1v (seg_rom RSEGS)) ->
(forall M1 model1, ri_inv HI ((p, c) :: LB) FF LK cr0 Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 -> mem_ok M1 ->
mrestrict (ahid Aw model) M1 = M1v -> L5.u64_at RSEGS M1 o (c + 1) -> L5.u64_at RSEGS M1 (o + 16) p -> PMSPA.accA M1 p c ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1' R1' pc1 M1 model1) K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd2bf4 M model) K).
{ intros fx1' R1' pc1 MS K1. unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok ((p, c) :: LB) FF LK cr0 Aw M model fx fx1' R 0xd2bf4 R1' pc1 M1v (fun a => S - 80 <= a < S - 80 + 80) K HH AM MS MG1 FR1).
{ intros a Ha Wa. split; [apply (L5SAR.stack_client L ar _ FF 0 0 a); lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1' VV1. apply (K1 M1 model1 HH1 AM1 MRT1).
- exact (mem_ok_frame M M1 [(p, c)] LK cr0 Aw model HH MO MGM1 FR1').
- exact VIS1.
- apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; lia| lia| lia| exact W0].
- apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; lia| lia| lia| exact W16].
- destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & _).
apply (PMFA.accA_agree M M1 p c); [| exact ACP].
apply (PMBRZK.agsh_frame M M1 (fun a => S - 80 <= a < S - 80 + 80) p c FR1'); [intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia| lia| lia]. }
destruct EX as [(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
|(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)].
- apply (CONT fx1 R1 0xd2c58 MS1). intros M1 model1 HH1 AM1 MRT1 MO1 VIS1 W01 W161 ACP1.
assert (SV1 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
apply (fit_long fx1 R1 M1 model1 LK Aw c n0 p m).
+ split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
+ exact Es.
+ exact En.
+ exact Hm.
+ lia.
+ exact E2.
+ rewrite E8, A10. reflexivity.
+ exact E9.
+ exact E10.
+ exact E18.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply saves_of; (apply SV1; [lia| lia|]; rewrite <- (RR _) by inl; eassumption).
+ exact MO1.
+ exact W01.
+ exact W161.
+ lia.
+ exact Hc.
+ exact Hce.
+ exact ACP1.
+ exact TBOK.
+ exact HH1.
- apply (CONT fx1 R1 0xd2c80 MS1). intros M1 model1 HH1 AM1 MRT1 MO1 VIS1 W01 W161 ACP1.
assert (SV1 : forall a v, S - 80 <= a -> a + 8 <= S -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v X1 X2 X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis _ M1 a v (VSTK a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
apply (grow_long fx1 R1 M1 model1 LK Aw c n0 p m).
+ split; [exact AM1|]. split; [exact (L5LZ.model_rt_trans model0 model model1 MRT MRT1)|]. split; [exact ILK| exact IAW].
+ exact Es.
+ exact En.
+ exact Hm.
+ lia.
+ lia.
+ exact TBOK.
+ exact Hc.
+ exact Hce.
+ exact W161.
+ exact ACP1.
+ exact CR.
+ exact E2.
+ rewrite E8, A10. reflexivity.
+ exact E9.
+ exact E10.
+ exact E18.
+ exact E23.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply saves_of; (apply SV1; [lia| lia|]; rewrite <- (RR _) by inl; eassumption).
+ exact MO1.
+ exact HH1.
Qed.
Lemma resize_entry : ltac2:(TCodec.tc2 tcn__PmBResize3 "RA'QB&QFv1vR;%3221&Mv=&2'7';%2211&Q:vR@%211v@%83521v<vCvR6vH&N%11B%A8@7654D31'9'RByR0%211&QCvJ&RAy5&QOu:%211%5241%8271vR>%82<1%?3<31u;%911%<2;1%?2>1vR<%?2C1%F3C31&Q<&QG&Q>%3521N=Q5&Q9vRD%22Q81&Q@&QAv?&Q8&Q=vR3%2241%431Q@9%7261%921Q<'QD&Q1vQI%211&Q?r8+j\[@%36G2Q:1QCR3v>%94I621p0;1p0F1p0J1p0O1p0Q71p0QH1p0R;1pT@R@1").
Proof using All. intros fx.
intros AM0 HH A10 A11 VS TBOK CR.
pose proof STK0 as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
pose proof VS as (DO & ACO & _).
destruct (vfacts _ _ _ _ _ _ HH STK0) as (VSTK & (O1 & O2 & O5) & ODEF & OVIS & VBLK).
set (H := ahid Aw0 model0) in *. set (MV := mrestrict H M0) in *.
pose proof (PMKB.aobj_of_aobjA FF o 24 AO Ho3) as AOB.
assert (WOV : L5.writable RSEGS MV o 24).
{ apply (proj2 (L5A.writable_vis H M0 o 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (HO : bv_unsigned (getr R0 (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (MR0 : model_rt model0 model0) by (unfold model_rt; destruct model0; reflexivity).
assert (STO0 : stok model0 LK0 Aw0) by (split; [exact AM0|]; split; [exact MR0|]; split; apply incl_refl).
assert (MO0 : mem_ok M0).
{ split; [intros a _; reflexivity|]. split; [intros a _ _ D; exact D|]. split; [exact STK0| exact ACO]. }
assert (RR0 : rs_regs R0) by (intros x _; reflexivity).
assert (NSHo : forall x, o + 0 <= x < o + 0 + 24 -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x X; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
unfold PMSPA.cfg.
assert (CASE : (exists n0, s = PM.VShort n0) \/ (exists c n0 p, s = PM.VLong c n0 p)) by (destruct s as [x|x y z]; [left; exists x | right; exists x, y, z]; reflexivity).
destruct CASE as [(n0 & Es)|(c & n0 & p & Es)]; rewrite Es in VS, HH.
-
destruct VS as (_ & _ & Hn0 & B0).
assert (Hn1' : n <= n0 + 16384) by (pose proof Hn1 as Hn1c; rewrite Es in Hn1c; cbn [PM.vs_size] in Hn1c; unfold PM.CHUNK in Hn1c; lia).
assert (B0v : L5.u8_at RSEGS MV o (2 * n0)).
{ apply (proj2 (L5A.u8_at_vis H M0 o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
pose proof (PMBRZP.arzS_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | 37%nat => n | _ => 0 end)) as P.
cbn beta iota in P. rewrite HO in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia | apply PMF.even_byte]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
replace (2 * n0 / 2) with n0 in EX by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
destruct EX as [(MS1 & KS1 & F13 & _ & F)|(MS1 & KS1 & F11 & _ & _ & F)].
+
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 S) by (rewrite (KS1 2%nat) by inl; exact Rsp0).
assert (R1_11 : getr R1 (reg 11) = Z_to_bv 64 n) by (rewrite (KS1 11%nat) by inl; exact A11).
assert (HO1 : bv_unsigned (getr R1 (reg 10)) = o) by (rewrite (KS1 10%nat) by inl; exact HO).
pose proof (PMBRZP.arzTS_conc fx1 R1 MV (fun j => match j with 2%nat => S | 37%nat => n | _ => 0 end)) as Q.
cbn beta iota in Q. rewrite HO1 in Q.
L5SAR.feed Q ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct Q as (fx2 & R2 & M2v & MG2 & _ & FR2 & MS2 & KS2 & _ & _ & _ & CN & CB).
assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite (KS2 1%nat) by inl; rewrite (KS1 1%nat) by inl; exact Rra0).
pose proof (PMK.ret_to RSEGS fx2 R2 M2v 0xd319c (ltac:(oW' 0xd319c%Z)) r (ltac:(oF' 0xd319c%Z)) eq_refl (ltac:(oD' 0xd319c%Z)) RA2 ltac:(lia) Hr2) as MS3.
set (W1 := fun a => o + 0 <= a < o + 0 + 24).
apply (L5SAR.apiece L ar C HI LYa HIok (PM.vs_own (PM.VShort n0) ++ LB) FF LK0 cr0 Aw0 M0 model0 fx fx2 R0 0xd3170 R2 r M2v W1 K HH AM0).
{ eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]. }
{ exact MG2. }
{ exact FR2. }
{ intros a Ha Wa. unfold W1 in Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia| lia]. }
intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2' VV2.
apply (KONT fx2 R2 M2 model2 LK0 Aw0 (PM.VShort n) tg cr0).
* apply L5SAR.preserved_by_index. intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
* split; [intros i Hi; apply MGM2; apply DO; exact Hi|].
split; [exact (PMFA.accA_agree M0 M2 o 24 (PMBRZK.agsh_frame M0 M2 W1 o 24 FR2' NSHo ltac:(lia) ltac:(lia)) ACO)|].
split; [lia|]. rewrite <- VIS2 in CB. exact (proj1 (L5A.u8_at_vis _ M2 o (2 * n) (L5A.avis_sub _ o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CB).
* reflexivity.
* rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
* intros _. rewrite Es. split; reflexivity.
* change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M2).
-- apply (L5SAR.ek_piece L ar LB FF S 14336 _ M0 M2 W1 FR2'). intros a Ha CA OW Wa. unfold W1 in Wa.
apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- pose proof (L5SAR.astk_grows ar M0 M2 S 14336 STK0 MGM2) as (_ & _ & _ & _ & D2 & _). exact D2.
-- apply (L5SAR.dk_grows L ar LB FF S 14336 M0 M2 MGM2).
* rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
* exact MRT2.
* apply incl_refl.
* apply incl_refl.
* exact AM2.
* exact HH2.
+
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd3170 R1 0xd2bf4 _ K HH AM0 MS1 (fun x X => X) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (EM1 : M1 = M0).
{ apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
subst M1.
apply (append_short fx1 R1 M0 model1 LK0 Aw0 n0 (n - n0)).
* split; [exact AM1|]. split; [exact MRT1|]. split; apply incl_refl.
* exact Es.
* lia.
* lia.
* exact Hn0.
* exact TBOK.
* exact CR.
* rewrite (KS1 10%nat) by inl. exact A10.
* exact F11.
* intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
* exact MO0.
* exact B0.
* exact HH1.
-
pose proof VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & ACP).
destruct (bfacts _ _ _ _ _ _ p c HH (or_introl eq_refl)) as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & _ & PO).
pose proof (PMF.u8_of_u64 RSEGS M0 o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
assert (B0v : L5.u8_at RSEGS MV o ((c + 1) mod 256)).
{ apply (proj2 (L5A.u8_at_vis H M0 o _ (L5A.avis_sub H o 24 o 1 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact B0. }
assert (W8v : L5.u64_at RSEGS MV (o + 8) n0).
{ apply (proj2 (L5A.u64_at_vis H M0 (o + 8) _ (L5A.avis_sub H o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W8. }
pose proof (PMBRZP.arzL_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 37%nat => n | _ => 0 end)) as P.
cbn beta iota in P. rewrite HO in P.
L5SAR.feed P ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FRw & _ & EX).
assert (EM : M1v = MV) by (apply functional_extensionality; exact FRw). subst M1v.
destruct EX as [(MS1 & KS1 & F11 & _ & _ & F)|(MS1 & KS1 & F13 & _ & F)].
+
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xd3170 R1 0xd2bf4 _ K HH AM0 MS1 (fun x X => X) (fun a _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (EM1 : M1 = M0).
{ apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FR1. pose proof (bv_unsigned_in_range 64 x) as X.
change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
subst M1.
apply (append_long fx1 R1 M0 model1 LK0 Aw0 c n0 p (n - n0)).
* split; [exact AM1|]. split; [exact MRT1|]. split; apply incl_refl.
* exact Es.
* lia.
* lia.
* exact TBOK.
* exact CR.
* rewrite (KS1 10%nat) by inl. exact A10.
* rewrite F11. f_equal. lia.
* intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
* exact MO0.
* rewrite Es. exact VS.
* exact HH1.
+
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 S) by (rewrite (KS1 2%nat) by inl; exact Rsp0).
assert (R1_11 : getr R1 (reg 11) = Z_to_bv 64 n) by (rewrite (KS1 11%nat) by inl; exact A11).
assert (HO1 : bv_unsigned (getr R1 (reg 10)) = o) by (rewrite (KS1 10%nat) by inl; exact HO).
assert (W16v : L5.u64_at RSEGS MV (o + 16) p).
{ apply (proj2 (L5A.u64_at_vis H M0 (o + 16) p (L5A.avis_sub H o 24 (o + 16) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact W16. }
assert (WRp : L5.writable RSEGS MV (p + n) 1).
{ apply (proj2 (L5A.writable_vis H M0 (p + n) 1 (VBLK p c (p + n) 1 ltac:(rewrite Es; left; reflexivity) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS M0 (p + n) 1); [apply (L5.defined_sub M0 p c (p + n) 1 DP); lia|lia|lia]. }
assert (Dpo : p + n + 1 <= o \/ o + 24 <= p + n) by lia.
pose proof (PMBRZP.arzTL_conc fx1 R1 MV (fun j => match j with 2%nat => S | 35%nat => p | 37%nat => n | _ => 0 end)) as Q.
cbn beta iota in Q. rewrite HO1 in Q.
L5SAR.feed Q ltac:(first [assumption | unfold PMBRZP.aligned; lia | lia]).
destruct Q as (fx2 & R2 & M2v & MG2 & _ & FR2 & MS2 & KS2 & _ & _ & CN & C8).
assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite (KS2 1%nat) by inl; rewrite (KS1 1%nat) by inl; exact Rra0).
pose proof (PMK.ret_to RSEGS fx2 R2 M2v 0xd31c0 (ltac:(oW' 0xd31c0%Z)) r (ltac:(oF' 0xd31c0%Z)) eq_refl (ltac:(oD' 0xd31c0%Z)) RA2 ltac:(lia) Hr2) as MS3.
set (W1 := fun a => (o + 8 <= a < o + 8 + 8) \/ (p + n + 0 <= a < p + n + 0 + 1)).
assert (Ip : In (p, c) (PM.vs_own (PM.VLong c n0 p) ++ LB)) by (left; reflexivity).
apply (L5SAR.apiece L ar C HI LYa HIok (PM.vs_own (PM.VLong c n0 p) ++ LB) FF LK0 cr0 Aw0 M0 model0 fx fx2 R0 0xd3170 R2 r M2v W1 K HH AM0).
{ eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]. }
{ exact MG2. }
{ intros a Ha Nw. apply FR2; [exact Ha| intros X; apply Nw; left; exact X| intros X; apply Nw; right; exact X]. }
{ intros a Ha [Wa|Wa]; split.
- apply (L5SAR.obj_client L ar _ FF 0 0 o 24 a AOB); lia.
- lia.
- apply (L5SAR.block_client L ar _ FF 0 0 p c a Ip); lia.
- lia. }
intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2' VV2.
assert (NSH2 : forall x, W1 x -> x < BIGSHADOW_LO \/ BIGSHADOW_HI <= x) by (intros x [X|X]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia).
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ W1 i) -> L5C.agree_on M0 M2 a m).
{ intros a0 m0 Ha0 Hm0 X i Hi. apply FR2'; [lia| apply X; exact Hi]. }
apply (KONT fx2 R2 M2 model2 LK0 Aw0 (PM.VLong c n p) tg cr0).
* apply L5SAR.preserved_by_index. intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
* split; [intros i Hi; apply MGM2; apply DO; exact Hi|].
split; [exact (PMFA.accA_agree M0 M2 o 24 (PMBRZK.agsh_frame M0 M2 W1 o 24 FR2' NSH2 ltac:(lia) ltac:(lia)) ACO)|].
split; [apply (L5C.u64_at_agree RSEGS M0 M2); [apply AG; [lia|lia| intros i Hi X; destruct X as [X|X]; lia]|lia|lia|exact W0]|].
split; [rewrite <- VIS2 in C8; exact (proj1 (L5A.u64_at_vis _ M2 (o + 8) n (L5A.avis_sub _ o 24 (o + 8) 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) C8)|].
split; [apply (L5C.u64_at_agree RSEGS M0 M2); [apply AG; [lia|lia| intros i Hi X; destruct X as [X|X]; lia]|lia|lia|exact W16]|].
split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MGM2; apply DP; exact Hi|].
exact (PMFA.accA_agree M0 M2 p c (PMBRZK.agsh_frame M0 M2 W1 p c FR2' NSH2 ltac:(lia) ltac:(lia)) ACP).
* reflexivity.
* rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
* intros _. rewrite Es. split; reflexivity.
* change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF S 14336 _ M0 M2).
-- apply (L5SAR.ek_piece L ar LB FF S 14336 _ M0 M2 W1 FR2'). intros a Ha CA OW Wa. destruct Wa as [X|X].
++ apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ exact (PMBRS1.own_not_aclient L ar C HI HIok [(p, c)] LB FF LK0 cr0 Aw0 M0 _ p c a S 14336 HH (or_introl eq_refl) ltac:(lia) CA).
-- pose proof (L5SAR.astk_grows ar M0 M2 S 14336 STK0 MGM2) as (_ & _ & _ & _ & D2 & _). exact D2.
-- apply (L5SAR.dk_grows L ar LB FF S 14336 M0 M2 MGM2).
* rewrite Es. unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_text. cbn [PM.vs_cap fst snd]. lia.
* exact MRT2.
* apply incl_refl.
* apply incl_refl.
* exact AM2.
* exact HH2.
Qed.
End Call.
End WithHeap.
End PMBRZ3.
