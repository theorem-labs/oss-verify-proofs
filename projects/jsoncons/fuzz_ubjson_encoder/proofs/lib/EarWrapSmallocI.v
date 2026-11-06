(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx EarInv EarFsInv EarIfaceInst EarWrapSmalloc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_EarWrapSmallocI () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>wx_segs_nowrapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv5rn_tpC13~~~K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InK47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA5hl_tpC13~~~C47Corelib4Init5Logic6eq_symC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EarWrapSmalloc<art_asmallocC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EarInv7art_run00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~K47Corelib7Numbers7BinNums1Z01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EarIfaceInst5art_LC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Theorem art_inst_smalloc : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> rn_tp rn = 0x675a80 ->
  forall k, In k [0; 1; 2; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) k.
Proof.
ltac2:(KReplay.run1 (kr_t_EarWrapSmallocI ()) [] "h04BASEh16BUDGETh22Hkh33Htph43Hwxh55MAPS0h66NOACC0h75RESV0h81kh92rnh:4scfgp;1p;2p;3p;4p;Gg0000j10Tg000Uj1?Tg0013j1=Tg001Vj2GTg0026j1;Tg002Vj1@Tg003hj1<Tg004oj15Tg005Tj3ETg005nj17Tg006Lj1CTg006lj39Tg007Lj3BTg007cj2:Tg008=j1ATg009Hj4>Tg009dlGDTf0R0#0#0#0#0p=6%50#5p=8%50#0p=1%00#5p=3%00#0p=2%00#7p=Fg00;:R1%70':p=4g00;XR2#0R3#0#6R4#?#=R5/G5#;R5g00<=g00=Hg00>BR6#@f2R7#<%52R8#0R9#0#8#1#1#8#3#3#2#6#F5E1g00?O%72%73%78%53R3#7%C15915915915915919B10f:f9f8f7f6f5R8f4f3g00?mR2g00A:#;/:6%04#2R4#0#2#6#4%19#3#1#2#6#6#6#4P1%<8%A2P7C>P7%44%83#1R3#3R4#0R7#0#2#3#3#2#4%57#1#2#1#2#4%84#2#3#1#2#4%13R3#2#1#8#3#2#4%13#3#1#6#4R3P3f1P0MGDW2X81W3W4W:W9X11X01X65X75W5o"). Qed.
