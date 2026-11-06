(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx EbrInv EbrFsInv EbrIfaceInst EbrWrapSmalloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_EbrWrapSmallocI () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>wx_segs_nowrapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv5rn_tpC13~~~K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InK47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA5hl_tpC13~~~C47Corelib4Init5Logic6eq_symC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EbrWrapSmalloc<art_asmallocC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv7art_run00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images9AsanUbsan1M?loaded_segmentsC13~~~K47Corelib7Numbers7BinNums1Z01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EbrIfaceInst5art_LC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Theorem art_inst_smalloc : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> rn_tp rn = 0x67a180 ->
  forall k, In k [0; 1; 2; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) k.
Proof.
ltac2:(KReplay.run1 (kr_t_EbrWrapSmallocI ()) [] "h04BASEh16BUDGETh22Hkh33Htph43Hwxh55MAPS0h66NOACC0h75RESV0h81kh92rnh:4scfgp;1p;2p;3p;4p;Gg0000j10Tg000Uj1@Tg0013j1>Tg001Vj2GTg0026j1:Tg002Vj1ATg003hj1<Tg004oj13Tg005Tj3FTg005nj16Tg006Lj1ETg006lj37Tg007Lj3CTg007cj2;Tg008=j1BTg009Hj4?Tg009dlGDTf0R0#0#0#0#0p=4%30#3p=1%00#3p=9%00#0p=2%00#6p==g00;:R1%60';p=5%30#0p=8g00;XR2#0R3#0#4R4#@#>R5/G5#:R5g00<=g00=Hg00>BR6#Af2R7#<%32R8#0R9#0#1#1#9#4#1#2#4#=5F1g00?T%62%63%68%33R3#6%E15715715715715719C10f:f9f8f7f6f5R8f4f3g00@2R2g00A?#:/;6%04#2R4#0#2#4#5%89#9#1#2#4#4#4#5P1%<8%B2P7C?P7%54%33#1R3#0#1R4#0R7#0#2#1#1#2#5%37#8#1#4#5%14#9#2#4#5%33#2R3#2#1#9#1#2#5%83#8#2#8#2#5R3P3f1P0MGDW2X81W3W4W:W9X11X01X65X75W5o"). Qed.
