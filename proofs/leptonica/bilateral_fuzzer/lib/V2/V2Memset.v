(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib ShapeAlg PureModel.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Memset.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocCode.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Memset () := "C6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memset;memset_specK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica8WalksLib2zfI5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Common5Hoare:regs_agreeI47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocCode7v2_codeK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memset;memset_clobI47Corelib7Numbers7BinNums1N00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memset?memset_post_memC6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memset9memset_atI5ARocqVerifyHarness?AgentSubmission6Common9PureModel7md_pure00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg8realizes00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission6Common8ShapeAlg4TSet".
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
      msteps SEGS (mkst regs (0x43880 : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Memset ()) ["Contract"] "h01nh11Hh21Mh32b1h42b2h51dh64regsh75regs'h83reth93romh:3RLTh;1bh<1rp;3p;1p;2p;4p;5p;6g0000j3WTg0013j12Tg001Xj10Tg002=j1<Tg002[j16Tg003>j2PTg003jj1MTg004Lj2>Tg004hj17Tg005Fj2ETg005cj2CTg006?R0j2:Tg006Zj2VTg0077j1UTg0086j29Tg008\j1RTg009<j4ATg00:<j34Tg00:Vj1OTg00;Nj2;Tg00<1j35Tg00<Tj2LTg00=Tj2KTg00>Nj5=Tg00?Gj2GTg00?gj4HTg00@Gj1FTg00@gj3ITg00AGj3JTg00BHj3@Tg00CCj3DTg00CZj3NTg00DVj2?Tg00E0j28Tg00EZj3QTg00F>j2BTg00FXj6STg00G4j2TTf0R1#2#2p=1f3R2f2R3f1R4'T;41p=3p,2fxR5g00GmR6g00He3Wg00I`R7#2R8#0R9#<R:%18R;#2#1R<#<R=#6R>'PR?%<;#6#M\>R@g00JERAg00JcRB/>3RC%77RD/>3%78%7<'ER<,C3':R8f4RE/V2/><R<g00KARF%U6RGf7RHf5RI,9=RJ%RERKCAg00KaRL34%OERMP>f:RNg00LARO1;:Dd95:DPIC3P>f;RP%29#7RQPO1;:Qd55:RRf8,9=RSC3P>f<RT%09#7R9PO1;:9d55:19=BRUC3P>f=RV%07RW#1#7RXPO1;:Xd55:f9,9=RYC3P5f?RZ%0;#1#1#0#0,L6%0W#1#0#0#2#0#0#2#0#0#0#2#1#7'Kf>RWPVD=P5P1PN1GAAR6PAPAPBPPCH%F63I9JWTPVD=R65@GP>P1PR19=TRRC3%6:RGg00L]9DG1W<?NZ1RG':':X7?,??[[[[[[[[[^8>^0A]5^9@]2]6g00M`RB%61R;%64R[P0%63?4411823182454AR0[1834183154A%62?434[R\%6E?423\0AQ341P1n2001000000120000000W4W3W0P\^4[^3;^0BP1P=%17#1#0#0#0#2#1#0#2#1#1#1#7R7,9=RBA5=7OR;1BA718=B18=;54AdO4b1A4>B;P>PBg00N>RBPHPJPKCA=4FLP>PNA5:DOPIC3P>PPA5:QORQPSC3P>PTA5:9OPUC3P>PVA5:XOPYC3P5PZf@PWPVD==@B6P>P1PQPRC3/:G':X7?,??[[[[\M[\<\8\C^8>^0A^5A^9@^2@^6?X;>P4P;P1ESb1b:o"). Qed.

  Lemma memset_post_mem : forall (M : word -> option byte) (d n : Z),
    (0 <= d)%Z -> (d + n <= 2 ^ 64)%Z ->
    (forall i, (0 <= i < n)%Z -> zf M d [(0, n)]%Z (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 0))
    /\ (forall x : word, (bv_unsigned x < d \/ d + n <= bv_unsigned x)%Z -> zf M d [(0, n)]%Z x = M x)
    /\ mem_grows M (zf M d [(0, n)]%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_V2Memset ()) ["Contract"] "g00OPo"). Qed.

  Corollary memset_at : forall model regs (M rom : word -> option byte) (d n : Z) (ret : word) (S : TSet),
    md_pure model ->
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    (forall regs', getr regs' 10 = Z_to_bv 64 d -> regs_agree (fun r => In r memset_clob) regs regs' ->
       realizes SEGS (mkCfg (mkst regs' ret (zf M d [(0, n)]%Z) rom) model) S) ->
    realizes SEGS (mkCfg (mkst regs (0x43880 : word) M rom) model) S.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Memset ()) ["Contract"] "h01nh11Hh21Mh31Sh42b1h52b2h61dh75modelh84regsh95regs'h:3reth;3romh<3RLTh=1bh>1rp;3p;1p;2p;4p;5p;6g00PWj3XTg0013j14Tg001Xj10Tg002=j1?Tg002[j17Tg003>j2NTg003jj1JTg00QXj1ETg004Lj2>Tg004hj16Tg005Fj2CTg005cj2ATg006?R0j2WTg006Zj2UTg0077j1TTg0086j28Tg008\j1OTg009<j4@Tg00:<j32Tg00:Vj1MTg00;Nj2;Tg00<1j35Tg00CCj3ITg00CZj3FTg00?Gj2GTg00?gj4HTg00@Gj1DTg00@gj3KTg00AGj3LTg00>Nj5<Tg00RWj2=Tg00SLj3:Tg00<Tj2BTg00=Tj2PTg00E0j29Tg00EZj3QTg00F>j2RTg00FXj6STg00G4j2VTf0R1#4#4p=1f3R2f2R3f1R4'V;21p=3p,2fxR5g00GmR6g00He3Xg00TKR7g00I`R8#4R9#0R:#?R;%19R<#4#1R=#?R>#7R?'NR@%?<#7#J\?RAg00JERBg00UARCf7RD#EREg00JcRFf4RG'>RH%68RI/>G%69%6='CR=,AG'WR9f6RJf5'U/>=R=g00KARK%T6RLf9RM18>DRN%OJROC@g00KaRP32%MJRJP?f<RQg00LARR1;;Id95;IPDC3P?f=RS%4:#6RTPR1;;Td55;RUf:,8>RVC3P?f>RW%0:#6R:PR1;;:d55;18>FRXC3P?f?RY%08RZ#1#6R[PR1;;[d55;f;R\,8>R]C3P?P1PU18>WRUC3%7;R^g00L]9I^1W>fBR^;F4R_P5P3PWf@R`1GBBRaPBPBPFPYCH%Da3K5L^fARaD<fD'=RF=:LS[[^9@P5Pa%0<#1#1#0#0,B6%0Z#1#0#0#4#0#0#4#0#0#0#4#1#6'PP`PYD</=^=:L\[[[[[[[[[[[]3^:?^0B]6^;A]2]8]7g00M`RL%71RZ%74R6P0%73?2411923192452BR0[1934193152B%72?234[R<%7G?223\0AQ341P1n2001000000120000000W5W4W0P<^56^4Z^0LP1P>%18#1#0#0#0#4#1#0#4#1#1#1#6R8,8>RLA5>8RRZ1RB819>L19>Z52BdO4b1A2?LZP?PLg00N>RLPMPNPOC@=2KPP?PQA5;IRPDC3P?PSA5;TRRTPVC3P?PWA5;:RPXC3P?PYA5;[RP]C3P?P1PTPUC3A:LFS\_[^9@P5PafCP`PYD</=^=:L\[[[[[\J[\=\9\H\E^3C^:?^0B^6B^;A^2A^8@^77X=?P4PZP1ESb1b<o"). Qed.
End Contract.
