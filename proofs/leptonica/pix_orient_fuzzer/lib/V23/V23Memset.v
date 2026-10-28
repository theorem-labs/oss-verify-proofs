(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib ShapeAlg PureModel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Memset.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocCode.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Memset () := "C6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memset;memset_specK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib2zfI5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23<V23RelocCode8v23_codeK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memset;memset_clobI47Corelib7Numbers7BinNums1N00C5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segments____________________C6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memset?memset_post_memC6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memset9memset_atI5ARocqVerifyHarness?AgentSubmission6Common9PureModel7md_pure00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSet".
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Abbreviation memset_clob := Memset.memset_clob.

Section Contract.
  Context {fx : FPState}.

  Theorem memset_spec : forall regs (M rom : word -> option byte) (d n : Z) (ret : word),
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x11e6d4 : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Memset ()) ["Contract"] "h01nh11Hh21Mh32b1h42b2h51dh64regsh75regs'h83reth93romh:3RLTh;1bh<1rp;3p;1p;2p;4p;5p;6g0000j3ZTg0013j17Tg001Xj12Tg002=j1ATg002[j15Tg003>j2STg003jj1MTg004Lj2@Tg004hj16Tg005Fj2HTg005cj2FTg006?R0j2<Tg006Zj2YTg0077j1UTg0086j29Tg008\j1TTg009<j4DTg00:<j30Tg00:Vj1RTg00;Nj2>Tg00<1j34Tg00<Tj2LTg00=Tj2JTg00>Nj5?Tg00?Gj2ITg00?gj4KTg00@Gj1GTg00@gj3NTg00AGj3OTg00BHj3BTg00CCj3PTg00CZj3QTg00DVj2CTg00E0j28Tg00EZj3ETg00F>j2XTg00FXj6WTg00G4j2VTf0R1#7#7p=3f3R2f2R3f1R4'V;01p=1%21#2p=;%71#2p=:%21#7p==p,2fxR5g00GmR6g00Hh3Zg00IfR7#7R8#2R9#AR:%38R;#7#3R<#AR=#5R>'SR?%A;#5#M\>R@g00JKRAg00JiRB/@3RC%67RD/@3%68%6<'HR<,F3'<R8f4RE/Y2/@<R<g00KGRF%U6RGf7RHf5RI,9=RJ%TERKCDg00KgRL30%RERMP>f:RNg00LGRO1>:Dd94:DPIC1P>f;RP%79#6RQPO1>:Qd54:RRf8,9=RSC1P>f<RT%29#6R9PO1>:9d54:19=BRUC1P>f=RV%27RW#3#6RXPO1>:Xd54:f9,9=RYC1P5f?RZ%2;#3#3#;,L6%2W#3#;#:#=#;#=#3#6'Jf>RWPVD?P5P1PN1IAAR6PAPAPBPPCK%G63N9OWTPVD?R65BGP>P1PR19=TRRC1%5:RGg00Lc9PG1W<?QZ1RG'<'<X7?,C?[[[[[[[[[^8>^0A]5^9@]2]6g00MfRB%51R;%54R[P0%53?0411823182450AR0[1834183150A%52?034[R\%5E?023\0AE341P1n2001000000120000000W4W3W0P\^4[^3;^0BP1P=%37#:#;#=#:#=#;#:#:#3#6R7,9=RBA4=7OR;1XA718=B18=;50AdO4b1A0>B;P>PBg00NDRBPHPJPKCD=0FLP>PNA4:DOPIC1P>PPA4:QORQPSC1P>PTA4:9OPUC1P>PVA4:XOPYC1P5PZf@PWPVD?=BB6P>P1PQPRC1/<G'<X7?,C?[[[[\M[\<\8\C^8>^0A^5A^9@^2@^6?X;>P4P;P1EWb1b:o"). Qed.

  Lemma memset_post_mem : forall (M : word -> option byte) (d n : Z),
    (0 <= d)%Z -> (d + n <= 2 ^ 64)%Z ->
    (forall i, (0 <= i < n)%Z -> zf M d [(0, n)]%Z (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 0))
    /\ (forall x : word, (bv_unsigned x < d \/ d + n <= bv_unsigned x)%Z -> zf M d [(0, n)]%Z x = M x)
    /\ mem_grows M (zf M d [(0, n)]%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Memset ()) ["Contract"] "g00Oko"). Qed.

  Corollary memset_at : forall model regs (M rom : word -> option byte) (d n : Z) (ret : word) (S : TSet),
    md_pure model ->
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    (forall regs', getr regs' 10 = Z_to_bv 64 d -> regs_agree (fun r => In r memset_clob) regs regs' ->
       realizes SEGS (mkCfg (mkst regs' ret (zf M d [(0, n)]%Z) rom) model) S) ->
    realizes SEGS (mkCfg (mkst regs (0x11e6d4 : word) M rom) model) S.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Memset ()) ["Contract"] "h01nh11Hh21Mh31Sh42b1h52b2h61dh75modelh84regsh95regs'h:3reth;3romh<3RLTh=1bh>1rp;3p;1p;2p;4p;5p;6g00Q2j3[Tg0013j17Tg001Xj14Tg002=j1BTg002[j16Tg003>j2QTg003jj1OTg00R3j1MTg004Lj2@Tg004hj15Tg005Fj2FTg005cj2DTg006?R0j2ZTg006Zj2UTg0077j1TTg0086j28Tg008\j1RTg009<j4CTg00:<j30Tg00:Vj1PTg00;Nj2<Tg00<1j33Tg00CCj3NTg00CZj3LTg00?Gj2KTg00?gj4HTg00@Gj1GTg00@gj3ITg00AGj3JTg00>Nj5?Tg00S2j2ATg00Sgj3=Tg00<Tj2ETg00=Tj2STg00E0j29Tg00EZj3YTg00F>j2XTg00FXj6WTg00G4j2VTf0R1#7#7p=2f3R2f2R3f1R4'V;01p=1%41#4p=;%71#4p=:%41#7p=>p,2fxR5g00GmR6g00Hh3[g00TfR7g00IfR8#7R9#4R:#BR;%29R<#7#2R=#BR>#6R?'QR@%B<#6#O\?RAg00JKRBg00U\RCf7RD#MREg00JiRFf4RG'@RH%58RI/@G%59%5='FR=,DG'ZR9f6RJf5'U/@=R=g00KGRK%T6RLf9RM18>DRN%RJROCCg00KgRP30%PJRJP?f<RQg00LGRR1<;Id93;IPDC1P?f=RS%7:#5RTPR1<;Td53;RUf:,8>RVC1P?f>RW%4:#5R:PR1<;:d53;18>FRXC1P?f?RY%48RZ#2#5R[PR1<;[d53;f;R\,8>R]C1P?P1PU18>WRUC1%6;R^g00Lc9N^1W>fBR^;L4R_P5P3PWf@R`1KBBRaPBPBPFPYCH%Ga3I5J^fARaD?fD'ARF==LS[[^9@P5Pa%4<#2#2#;,E6%4Z#2#;#:#>#;#>#2#5'SP`PYD?/A^==L\[[[[[[[[[[[]3^:?^0B]6^;A]2]8]7g00MfRL%61RZ%64R6P0%63?0411923192450BR0[1934193150B%62?034[R<%6G?023\0AY341P1n2001000000120000000W5W4W0P<^56^4Z^0LP1P>%28#:#;#>#:#>#;#:#:#2#5R8,8>RLA3>8RRZ1XB819>L19>Z50BdO4b1A0?LZP?PLg00NDRLPMPNPOCC=0KPP?PQA3;IRPDC1P?PSA3;TRRTPVC1P?PWA3;:RPXC1P?PYA3;[RP]C1P?P1PTPUC1A=LFS\_[^9@P5PafCP`PYD?/A^==L\[[[[[\J[\=\9\H\E^3C^:?^0B^6B^;A^2A^8@^77X=?P4PZP1EWb1b<o"). Qed.
End Contract.
