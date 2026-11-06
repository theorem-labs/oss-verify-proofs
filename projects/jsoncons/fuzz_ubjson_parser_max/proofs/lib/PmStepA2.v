(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA L5CoreA
L5StepAR PmLayout PmLayoutA PmSpecsA PmSpecsAa.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmStepA2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0C"; "1bool"; "1false"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0FF"; "0HI"; "0K"; "0L"; "0LB"]; ["0LK"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M1v"; "0R"; "0R1"; "6mrestrict"; "7msteps"; "8credit"; "9aclientw"; "9ahid"; "9asan_layout"; "9asan_statics_cells"; "9fframe"]; ["9hl_rt_ro"; "9model_rt"; "9ri_inv"; "9vml_of"; ":SCFG"; ";cfg"; "<layout"; "=FPState"; "=mkst"; "=seg_rom"; ">TSet"; "?srealizes"; "@mem_grows"; "Aamodel_ok"; "Bloaded_segments"; "0SCFG_P"]; ["Cle"; "Clt"; "Cpow"; "0W"; "0a"; "0ar"; "0cr"; "0fx"; "0fx1"; "0model"; "0model1"; "0pc"; "0pc1"; "DZ_to_bv"; "Dbv"]]).
Local Ltac lia := L5FastLia.plia.
Module PMKA2.
Import L5A. Import L5CA.
Section WithIface.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Lemma apiece_img : ltac2:(TCodec.tc2 tcn__PmStepA2 "UG'4'6':%2211%411&O%611&J'QNyR0%211'5y8%511%311p051'A'Q7&By5%221:!p0D1&Q:&Q2v<r@r?r>r=r<r;&Q3r:%211%;8:9876541&Q=%1286'I&Q>&Q8r9&QMr8%22Q31&H&L%12CA%321C&Q9%11;%;5D:731r7r6%<2Q=1r5%@5G4216%C3B61&Q<%=2Q0N%?21Q0%3218'7&Q@zr1%3221&QA&QB+2+R0%3221%5271%;271&9r2%Q111%311'8r3%Q62R71%Q@11rCrA%Q6221rB%Q93216%93R961p0;1p0@1pS:RH1%QB1@&Kv>vQErHrG%574321Q1Q1B&Q0%126D%J11%Q7241p0;1p0N1pS:S61rFrErD%R<1Q;%RE8RD>=432Q21%R:24Q3&Q1%125Q1'2p0S81r4%R62D1%R72E;%Q83421%R92H>%R;21R3%Q;3S:1RN%R02KR6%Q61Q@%QB11%RN1Q=rL%11Q?%QB3SB31p051p0QI1pS:T11rJ%RG371R4(3%QI3F21%S91QM%N1QN%QL3SL21p041pS:T21'Q;&Q4vQ?%211&Q5%15QCQ8Q7SAS9%64S<31R0p081p0B1p0L1p0N1p0Q21p0Q91p0Q<1p0Q>1pSFT<1pQ:T>1%=5T4T2T1R9R;%B4SH?1SDp031p0QI1p0R81p0S61p0S;1p0T01p0T31pLT@1pS8TB1pQ<TJ1pSJU81pQ@TG1pSHU:1pQ>TI1pSBTM1pS@TN1pSDU01pQ8U21p2U>1pS>U<1pQ2U>1pHU?1pQ0UB1").
Proof. intros LB FF LK cr A M model fx fx1 R pc R1 pc1 M1v W K.
intros HH [Hh MI] MS MG FZ WC KONT.
pose proof (HAJ.aior_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
pose proof (L5SAR.vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & _).
set (H := ahid A model) in *.
unfold L5A.cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
intros model1 MI1 SBM1 HC1.
set (M1 := munrestrict H M M1v).
assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
assert (MGM1 : mem_grows M M1).
{ intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
apply (KONT M1 model1).
- rewrite VML. apply (HAJ.aior_frame _ _ _ _ _ HIok LB FF LK cr A M M1 _ HH).
+ intros a Ha Hp. apply FRM1. exact Ha. intros CW. destruct (WC a Ha CW) as [C1 C2]. destruct Hp as [Hp|[Hp|Hp]].
* exact (Hp (aclientw_client _ _ _ _ _ _ _ C1)). * exact (C2 Hp).
* exact (L5SAR.aclientw_not_bshadow L ar C HI LY HIok LB FF LK cr A M _ 0 0 a HH C1 Hp).
+ exact MGM1.
- split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
- apply L5LZ.sbm_model_rt. exact SBM1.
- apply L5LZ.sbm_ahid. exact SBM1.
- exact M1vis.
- exact MGM1.
- exact FRM1.
- intros a Ha. unfold M1. apply L5LZ.munrestrict_visible. exact Ha.
Qed.
End WithIface.
Lemma rt_ro_bss : ltac2:(TCodec.tc2 tcn__PmStepA2 "D'M'N':'Q6r3r2%3221&Q@+QV`P0%2214&9&Q0r5%2219%411p061p0:1pS:?1p4A1pNC1").
Proof. intros L C a. intros LYJ Ha X. pose proof (PMA.ly_ro L C LYJ a X). lia. Qed.
End PMKA2.
