(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 JbtInv JbtFsInv JbtIfaceInst
JbtWrapStrlen JbtIcptLaws JbtWrapMemI.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtIcptInst () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.IcptIfaceAB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtIfaceInst."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "stdpp.bitvector.definitions."], [["0BASE"; "0BUDGET"; "1list"; "1prod"; "2eq"; "3Z"; "0IL"; "4SpuriousCfg"; "0MAPS0"; "0NOACC0"; "0RESV0"; "5wx_segs_nowrap"; "6aicpt_ok"; "6as0_icpt_layout"; "6icpt_layout"; "7art_fsg"]; ["7art_fsinv"; "8art_L"; "9art_iface"; "9art_run"; "9rn_ar"; "9rn_key"; "9rn_loff"; "9rn_tp"; "9rn_tsd"; ":loaded_segments"; "0rn"; "0scfg"; ";bv"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Theorem art_icpt_ok : ltac2:(TCodec.tc2 tcn__JbtIcptInst "R4'7'>'5&;&I%211'=r3%211'2'3'LyR0%211%4211%611'C'4&Gr1%211+V^Rf0%53D21&Er2%211z%:3I21&H%11F+VbWkH%>3M21&Fr4%211+@%C3Q221'<&A&Dr5%211r=r>&B'?r9r8r7r6r<&@%887654321<%@5?<;:1p0B1p0H1p0M1p0Q31pQFQ:1p2QI1pDQ=1pFQ>1pBQ?1p0QG1p0QK1p4QO1p>R11pQHR31").
Proof.
intros scfg IL BUDGET Hwx ILY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff.
destruct ILY as [E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14].
constructor.
- exact (art_astrlen MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl E1 E2 E3 E4).
- exact (art_law_globals MAPS0 RESV0 NOACC0 BASE BUDGET rn IL E5).
- exact (art_law_img_shadow MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L IL eq_refl eq_refl E6).
- exact (art_law_shadow_defined MAPS0 RESV0 NOACC0 BASE BUDGET rn).
- exact (art_law_tls MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L IL eq_refl eq_refl eq_refl (eq_sym Htp) E9 Htsd Hkey0 art_L_ro_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro).
- exact (art_amemcpy_libc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl eq_refl E7 art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
- exact (art_amemmove_libc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl eq_refl E8 art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
Qed.
