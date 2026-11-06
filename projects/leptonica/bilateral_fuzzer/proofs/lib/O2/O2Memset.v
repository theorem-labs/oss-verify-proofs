(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib ShapeAlg PureModel.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Memset.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc O2RelocCode.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Memset () := "C69OSSVerify5KrLib6Common4Musl6Memset;memset_specC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib6Common9Leptonica8WalksLib2zfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Common5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2RelocCode7o2_codeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C69OSSVerify5KrLib6Common4Musl6Memset;memset_clobC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6Memset?memset_post_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6Memset9memset_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Abbreviation memset_clob := Memset.memset_clob.

Section Contract.
  Context {fx : FPState}.

  Theorem memset_spec : forall regs (M rom : word -> option byte) (d n : Z) (ret : word),
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x36e5c : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Memset ()) ["Contract"] "h01nh11Hh21Mh32b1h42b2h51dh64regsh75regs'h83reth93romh:3RLTh;1bh<1rp;3p;1p;2p;4p;5p;6g0000j3ZTg0013j17Tg001Xj12Tg002=j1ATg002[j14Tg003>j2STg003jj1MTg004Lj2@Tg004hj16Tg005Fj2HTg005cj2FTg006?R0j2;Tg006Zj2YTg0077j1UTg0086j29Tg008\j1TTg009<j4DTg00:<j30Tg00:Vj1RTg00;Nj2>Tg00<1j33Tg00<Tj2LTg00=Tj2JTg00>Nj5?Tg00?Gj2ITg00?gj4KTg00@Gj1GTg00@gj3NTg00AGj3OTg00BHj3BTg00CCj3PTg00CZj3QTg00DVj2CTg00E0j28Tg00EZj3ETg00F>j2XTg00FXj6WTg00G4j2VTf0R1#7#7p=5f3R2f2R3f1R4'V;01p=1%21#2p=:%71#2p==%21#7p=<p,2fxR5g00GmR6g00He3Zg00I`R7#7R8#2R9#AR:%58R;#7#5R<#AR=#4R>'SR?%A;#4#M\>R@g00JERAg00JcRB/@3RC%67RD/@3%68%6<'HR<,F3';R8f4RE/Y2/@<R<g00KARF%U6RGf7RHf5RI,9=RJ%TERKCDg00KaRL30%RERMP>f:RNg00LARO1>:Dd93:DPIC1P>f;RP%79#6RQPO1>:Qd53:RRf8,9=RSC1P>f<RT%29#6R9PO1>:9d53:19=BRUC1P>f=RV%27RW#5#6RXPO1>:Xd53:f9,9=RYC1P5f?RZ%2;#5#5#:,L6%2W#5#:#=#<#:#<#5#6'Jf>RWPVD?P5P1PN1IAAR6PAPAPBPPCK%G63N9OWTPVD?R65BGP>P1PR19=TRRC1%4:RGg00L]9PG1W<?QZ1RG';';X7?,C?[[[[[[[[[^8>^0A]5^9@]2]6g00M`RB%41R;%44R[P0%43?0411823182450AR0[1834183150A%42?034[R\%4E?023\0AE341P1n2001000000120000000W4W3W0P\^4[^3;^0BP1P=%27#=#<#:#<#=#=#:#5#6R7,9=RBA3=7OR;1XA718=B18=;50AdO4b1A0>B;P>PBg00N>RBPHPJPKCD=0FLP>PNA3:DOPIC1P>PPA3:QORQPSC1P>PTA3:9OPUC1P>PVA3:XOPYC1P5PZf@PWPVD?=BB6P>P1PQPRC1/;G';X7?,C?[[[[\M[\<\8\C^8>^0A^5A^9@^2@^6?X;>P4P;P1EWb1b:o"). Qed.

  Lemma memset_post_mem : forall (M : word -> option byte) (d n : Z),
    (0 <= d)%Z -> (d + n <= 2 ^ 64)%Z ->
    (forall i, (0 <= i < n)%Z -> zf M d [(0, n)]%Z (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 0))
    /\ (forall x : word, (bv_unsigned x < d \/ d + n <= bv_unsigned x)%Z -> zf M d [(0, n)]%Z x = M x)
    /\ mem_grows M (zf M d [(0, n)]%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Memset ()) ["Contract"] "g00Odo"). Qed.

  Corollary memset_at : forall model regs (M rom : word -> option byte) (d n : Z) (ret : word) (S : TSet),
    md_pure model ->
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    (forall regs', getr regs' 10 = Z_to_bv 64 d -> regs_agree (fun r => In r memset_clob) regs regs' ->
       realizes SEGS (mkCfg (mkst regs' ret (zf M d [(0, n)]%Z) rom) model) S) ->
    realizes SEGS (mkCfg (mkst regs (0x36e5c : word) M rom) model) S.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Memset ()) ["Contract"] "h01nh11Hh21Mh31Sh42b1h52b2h61dh75modelh84regsh95regs'h:3reth;3romh<3RLTh=1bh>1rp;3p;1p;2p;4p;5p;6g00Pkj3[Tg0013j17Tg001Xj10Tg002=j1BTg002[j15Tg003>j2QTg003jj1OTg00Qlj1MTg004Lj2@Tg004hj14Tg005Fj2FTg005cj2DTg006?R0j2ZTg006Zj2UTg0077j1TTg0086j28Tg008\j1RTg009<j4CTg00:<j31Tg00:Vj1PTg00;Nj2;Tg00<1j33Tg00CCj3NTg00CZj3LTg00?Gj2KTg00?gj4HTg00@Gj1GTg00@gj3ITg00AGj3JTg00>Nj5?Tg00Rkj2ATg00S`j3<Tg00<Tj2ETg00=Tj2STg00E0j29Tg00EZj3YTg00F>j2XTg00FXj6WTg00G4j2VTf0R1#7#7p=6f3R2f2R3f1R4'V;11p=2%01#0p=:%71#0p==%01#7p=>p,2fxR5g00GmR6g00He3[g00T_R7g00I`R8#7R9#0R:#BR;%69R<#7#6R=#BR>#5R?'QR@%B<#5#O\?RAg00JERBg00UURCf7RD#MREg00JcRFf4RG'@RH%48RI/@G%49%4='FR=,DG'ZR9f6RJf5'U/@=R=g00KARK%T6RLf9RM18>DRN%RJROCCg00KaRP31%PJRJP?f<RQg00LARR1;;Id93;IPDC2P?f=RS%7:#4RTPR1;;Td53;RUf:,8>RVC2P?f>RW%0:#4R:PR1;;:d53;18>FRXC2P?f?RY%08RZ#6#4R[PR1;;[d53;f;R\,8>R]C2P?P1PU18>WRUC2%5;R^g00L]9N^1W>fBR^;L4R_P5P3PWf@R`1KBBRaPBPBPFPYCH%Ga3I5J^fARaD?fD'ARF=<LS[[^9@P5Pa%0<#6#6#:,E6%0Z#6#:#=#>#:#>#6#4'SP`PYD?/A^=<L\[[[[[[[[[[[]3^:?^0B]6^;A]2]8]7g00M`RL%51RZ%54R6P0%53?1411923192451BR0[1934193151B%52?134[R<%5G?123\0AY341P1n2001000000120000000W5W4W0P<^56^4Z^0LP1P>%08#=#>#:#>#=#=#:#6#4R8,8>RLA3>8RRZ1XB819>L19>Z51BdO4b1A1?LZP?PLg00N>RLPMPNPOCC=1KPP?PQA3;IRPDC2P?PSA3;TRRTPVC2P?PWA3;:RPXC2P?PYA3;[RP]C2P?P1PTPUC2A<LFS\_[^9@P5PafCP`PYD?/A^=<L\[[[[[\J[\=\9\H\E^3C^:?^0B^6B^;A^2A^8@^77X=?P4PZP1EWb1b<o"). Qed.
End Contract.
