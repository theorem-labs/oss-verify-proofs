(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceANull ArtMem ArtRuns ArtBridge EarInv EarFsInv EarFsInvLaws
     EarInvFreePure EarInvRepX EarFsInvLaws4 EarWrapFree EarWrapFreeNull EarIfaceInst.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import EarInvFreePure EarWrapFreeR.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_EarIfaceInstFree () := "I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv5rn_tpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA5hl_tpC13~~~C47Corelib4Init5Logic6eq_symK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EarFsInv9art_fsinvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EarFsInvLawsCart_fsinv_in_provedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv8art_rn_kC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=EarFsInvLaws4Kart_fsinv_frame_law2_provedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;EarWrapFree=art_wrap_freeC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EarFsInv7art_fsg00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EarIfaceInst5art_LC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EarIfaceInst=art_L_staticsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EarFsInvLawsJart_fsinv_frame_law_provedC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv7art_run00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?EarWrapFreeNullBart_wrap_free_nullC13~~~".   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x675a80.

#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="Halloc Hwx STATIC Htp"] Theorem art_inst_free : afree_spec art_L (rn_ar rn) scfg HI.
Proof.
ltac2:(KReplay.run1 (kr_t_EarIfaceInstFree ()) ["Inst"] "h02FFh12FSh22LKh31Mh41Dh51gh63rn0h73gfsp;1p;2p;4p;5p;6p;Ig0000j16Tg000Pj24Tg000jj11Tg001Oj10Tg0024j15Tg002Rj1=Tg003Yj1<Tg004dj4;Tg005@j19Tg005^j18Tg006Aj1:Tg006cR0j57Tg0080j6ATg009Kj2@Tg00:Uj1?Tg00<9lI>Tf0R1#0#0#0#0p=3%01#0p=2g00=MR2P0p,5MAPS0p,5RESV0p,6NOACC0p,4BASEp,6BUDGETp,2rnR0p,4scfgg00>ZR3p,6Hallocp,3Hwxp,6STATICg00?g#6g00@f'4g00B3R4g00BQR5#1R6#1#1#0#1#3#1#1#2#1#1#0#2#5'4%05#2R5#0#2R7#2#3R8#5,44P4%=0%<3p,3HtpC;%38#5,44%06#1#2#1#1#0#2#3#3#3#5,44g00C6g00DKg00EmR6%64#6R4g00G8#6R8%97#8%95#8#:[R5f5R7f3R3f2R9f1R:P1D7P1W1W3X28W0X52W4W6P0P3P9P:P1D7P0f4R;P3P9P:P1EAW1X35X28X08X721@7;P3P9P:P1D7P1W1X35X28X08X52X44X66%?0MI>o"). Qed.

#[using="Hwx Htp"] Theorem art_inst_free_null : afree_null_spec art_L (rn_ar rn) scfg HI.
Proof.
ltac2:(KReplay.run1 (kr_t_EarIfaceInstFree ()) ["Inst"] "h02FFh12FSh22LKh31Mh43gfsp;1p;2p;4p;5p;6p;Dg0000j18Tg000Pj24Tg000jj11Tg001Oj10Tg0024j15Tg002Rj1<Tg003Yj1;Tg004dj4:Tg005@j16Tg005^j17Tg006Aj19Tg006cR0j5?Tg0080j6>Tg00HDlD=Tf0R1#0#0#0#0p=3%01#0p=2g00=MR2P0p,5MAPS0p,5RESV0p,6NOACC0p,4BASEp,6BUDGETp,2rnR0p,4scfgg00>ZR3p,3Hwxg00?g#8g00@f'4g00B3R4g00BQR5#1R6#1#1#0#1#3#1#1#2#1#1#0#2#5'4%05#2R5#0#2R7#2#3R8#5,44P4%<0%;3p,3HtpC:%38#5,44%06#1#2#1#1#0#2#3#3#3#5,44g00C6g00DKg00G8#8R4%67#7%65#7#9[P0f3R5f2R7f1R6P1D?P0f4P5P7P6P1E>W1W3X24W0X42MD=o"). Qed.
End Inst.
