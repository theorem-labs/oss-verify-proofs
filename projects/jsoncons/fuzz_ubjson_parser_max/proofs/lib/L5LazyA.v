(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct AsanAcctShape HeapIface HeapIfaceA L5Defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__L5LazyA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1bool"; "1false"; "1list"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "3Z"; "0H"; "0H'"; "0K"; "4machine_state"; "4ms_mem"]; ["5mkCfg"; "6Model"; "6VmMaps"; "6m_halted"; "6m_vm_lazy"; "6m_vmmaps"; "6page_base"; "6page_in_ranges"; "7bvmap"; "0M"; "0M'"; "0M1v"; "0P"; "0R"; "0R'"; "8A_wf"]; ["8H_off_segments"; "8MInv"; "8lazy_cover"; "8mrestrict"; "8munrestrict"; "8restrict"; "8same_but_materialized"; "8segs_below_b"; "8unrestrict"; "8wx_segs_nowrap"; "9msteps"; ":ahid"; ":model_rt"; ";SCFG"; "<FPState"; "<mkst"]; ["<seg_rom"; "=TSet"; ">srealizes"; "0SCFG_P"; "?le"; "0a"; "0fx"; "0fx'"; "0m"; "0m'"; "0m1"; "0m2"; "0m3"; "0model"; "0model'"; "0pc"]; ["0pc'"; "0segs"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0top"; "0w"; "0x"]]).
Module L5LZ.
Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Lemma restrict_mkst : ltac2:(TCodec.tc2 tcn__L5LazyA "Q5'Q>'R3yR0%211'2p021&Hy5%2215'5y8%:11%311p0:1'9'>&Q5r4&Q?r5r3r2r1&Q@vR1%211%8576541%;2:1&Q3%12<7%<5;:915%A3@41pQDC1pT0N1pQLJ1pHN1pS>Q41").
Proof. intros fx H R pc M. reflexivity. Qed.
Lemma unrestrict_mkst : ltac2:(TCodec.tc2 tcn__L5LazyA "Q@'Q>'R3yR0%211'2p021&Hy5%2215'5y8%:11%311p0:1'9'>&Q8r7&?&Q?r9r6r5r4&Q@vR1%211%8576541%:11r8r3r2r1%>543217%B3A61&Q4%13C=4%B58761;%H3G41pQFJ1pT2Q51pQNQ11pQDM1pT0Q81pQLQ41pHQ81pS@Q>1pS>Q?1").
Proof. intros fx fx' H R pc M R' pc' M'. reflexivity. Qed.
Lemma mrestrict_of_munrestrict : ltac2:(TCodec.tc2 tcn__L5LazyA "Q2'R3yR0%211'2pT@21'5y8%711%311p071pT@82'9r4r1%211(7%53=21r3r2%211(1%11>%;3>31p071pS<F1&Q3&Q4%13?:9%32@1%B3D1;p061pQFE1pQDG1pHM1").
Proof. intros H M M'.
intros Hc. apply functional_extensionality. intros a. unfold mrestrict, munrestrict.
destruct (H a) eqn:E. symmetry; apply Hc; exact E. reflexivity.
Qed.
Lemma munrestrict_hidden : ltac2:(TCodec.tc2 tcn__L5LazyA "L'R3yR0%211'2pT@21'5y8%711%311p071'9r4r1%211(7%53<21&Q4r5r3r2%443921%:12%<3>21p081pS<F1pQF@1pQDA1pHG1").
Proof. intros H M M' a. intros E. unfold munrestrict. rewrite E. reflexivity. Qed.
Lemma munrestrict_visible : ltac2:(TCodec.tc2 tcn__L5LazyA "L'R3yR0%211'2pT@21'5y8%711%311p071'9r4r1%211(3%53<21&Q4r5r3r2%443921%312%<3>21p081pS<F1pQF@1pQDA1pHG1").
Proof. intros H M M' a. intros E. unfold munrestrict. rewrite E. reflexivity. Qed.
Lemma mrestrict_visible' : ltac2:(TCodec.tc2 tcn__L5LazyA "J'R3yR0%211'2pT@21'5y8%711%311p071'9r3r1%211(3%53<21&Q3r4r2%33281%912%;3=21p071pS<E1pQD?1pHE1").
Proof. intros H M a. intros E. unfold mrestrict. rewrite E. reflexivity. Qed.
Lemma mrestrict_agree_on : ltac2:(TCodec.tc2 tcn__L5LazyA "QF'R3yR0%211'2p021'5y8%711%311p071':!p021r2r1%211'8'9r7&R2%12C7%311(3%63D21r6%115%93G14%;241p0=1pS<C1r3%11Ar5%11=%A3J19p041pS<J1r4%11H&Q3r8%231AEr9%431IG%K3Q431p071pS<Q41p0;1p0C1pQJQ51pQFQ91pQDQ:1pJQ@1pHQA1").
Proof. intros H H' M M' P.
intros HV HM a Ha. destruct (HV a Ha) as [E E']. unfold mrestrict. rewrite E, E'. apply HM. exact Ha.
Qed.
Theorem cps_of_msteps_lazy : ltac2:(TCodec.tc2 tcn__L5LazyA "SD'R3yR0%211'2p021'4'6':%2211%411'Q>&Hy5%221;'5y8%@11%311p0@1'A&QA&Q0vR1r<%3221&Q9%114&Q2r>&Dr4%211r=%63521&O%117'Q1r?r6%3221'9%K1Q7&Cr7%211(1%11Q<%73631'Q:&Q?r@&Q3rB%221N&Q@%11Q1%756LH31r;r:r9%;5G3215%=3Q751rCr1%L221&Q6r2%22:1rG%116(7%O3R421%Q316%L1QI%Q23QI21p041pS<R:1'QB&Q=vQC%211(@rD&Q4rA%23A1QI%Q554Q4QA1O%621QI%;4R281R1p0=1p0G1p0K1pSNR91%Q<5Q9Q;QHR1Q6%=21Q4%B4R9?1Q4p041p0Q41p0QC1p0QL1p0R11p0R41p0R<1p0R?1pLRD1pSLRF1pQHRH1pT2S91pQNRO1pQDRK1pT0S<1pQLS21pS@S61pS>S71p2S91pHS?1").
Proof. intros H A fx fx' R pc M R' pc' M1v model K.
intros HH Hwx HL HA HI Hh MS HK.
rewrite <- (restrict_mkst fx H R pc M) in MS.
apply (srz_msteps_restricted_T segs SCFG H HH Hwx A _ _ model K HL HA HI Hh MS).
intros model' HI' HS HC. rewrite (unrestrict_mkst fx fx') . apply (HK model' HI' HS).
intros a Ha. exact (HC a Ha).
Qed.
Lemma lazy_cover_ahid : ltac2:(TCodec.tc2 tcn__L5LazyA "@'4'6':%2211%411'A&Q2&Q;r2r1%3221&D%113%73315pSL91p2;1").
Proof. intros A model. unfold ahid. apply lazy_cover_mkH. intros r Hr; exact Hr. Qed.
Lemma H_off_segments_ahid : ltac2:(TCodec.tc2 tcn__L5LazyA "Q:'4'6':%2211%411'A'9'2&Q7vR1r1%3221(7%73621'R3yR0%211&G&F%119&Dr4%211%6241%B3A1<&QD&R4r2%22=1%4281p061pT>?1&Q0&Q;r5%221>%42K1p061p0I1pT<Q51pSLQ31p2Q51").
Proof. intros A model top.
intros Hb Hhi a Ha. unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hp _].
apply (find_segment1_none_above segs top). exact Hb. apply Hhi. exact Hp.
Qed.
Lemma sbm_halted : ltac2:(TCodec.tc2 tcn__L5LazyA "C'A&Q6r2r1%3221'9'5'R3yR0%211%411&C%11:r3%311%:3531p0<1pSDA1pSBB1").
Proof. intros m m'. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_lazy : ltac2:(TCodec.tc2 tcn__L5LazyA "E'A&Q6r2r1%3221'9'4'6'R3yR0%211%4211%611&D%11<r3%311%<3531p0>1pSDC1pSBD1").
Proof. intros m m'. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_vmmaps : ltac2:(TCodec.tc2 tcn__L5LazyA "?'A&Q6r2r1%3221'9'B&E%116r3%311%63531p081pSD=1pSB>1").
Proof. intros m m'. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_ahid : ltac2:(TCodec.tc2 tcn__L5LazyA "J'4'6':%2211%411'A&Q6r2r1%3221'9'R3yR0%211'2p021&Q;r4%221;r3%4231%;3631p0=1pSDB1pSBC1p2E1").
Proof. intros A m m'. intros Hs. unfold ahid. rewrite (sbm_lazy m m' Hs). reflexivity. Qed.
Lemma sbm_model_rt : ltac2:(TCodec.tc2 tcn__L5LazyA ";'A&Q6r2r1%3221&Q<r3%2215p041pSD91pSB:1").
Proof. intros m m'. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma model_rt_trans : ltac2:(TCodec.tc2 tcn__L5LazyA "<'A&Q<r3r2%3221r5%5214p031p041pSJ91pSH:1pSF;1").
Proof. intros m1 m2 m3. unfold model_rt. intros -> ->. destruct m1; reflexivity. Qed.
Lemma model_rt_halted : ltac2:(TCodec.tc2 tcn__L5LazyA "C'A&Q<r2r1%3221'9'5'R3yR0%211%411&C%11:r3%311%:3531p0<1pSDA1pSBB1").
Proof. intros m m'. intros ->. destruct m; reflexivity. Qed.
End WithSegs.
End L5LZ.
