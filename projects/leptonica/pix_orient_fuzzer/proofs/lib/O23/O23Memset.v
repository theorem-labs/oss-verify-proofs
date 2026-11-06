(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib ShapeAlg PureModel.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Memset.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocCode.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Memset () := "C69OSSVerify5KrLib6Common4Musl6Memset;memset_specC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib6Common9Leptonica8WalksLib2zfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Common5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23RelocCode8o23_codeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01C69OSSVerify5KrLib6Common4Musl6Memset;memset_clobC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6Memset?memset_post_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6Memset9memset_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~".
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
      msteps SEGS (mkst regs (0x10a230 : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Memset ()) ["Contract"] "h01nh11Hh21Mh32b1h42b2h51dh64regsh75regs'h83reth93romh:3RLTh;1bh<1rp;3p;1p;2p;4p;5p;6g0000j3YTg0013j18Tg001Xj13Tg002=j1@Tg002[j16Tg003>j2RTg003jj1MTg004Lj2=Tg004hj17Tg005Fj2GTg005cj2ETg006?R0j2;Tg006Zj2XTg0077j1UTg0086j29Tg008\j1STg009<j4CTg00:<j31Tg00:Vj1QTg00;Nj2<Tg00<1j34Tg00<Tj2LTg00=Tj2KTg00>Nj5>Tg00?Gj2HTg00?gj4ITg00@Gj1JTg00@gj3FTg00AGj3NTg00BHj3ATg00CCj3OTg00CZj3PTg00DVj2BTg00E0j2:Tg00EZj3DTg00F>j2TTg00FXj6WTg00G4j2VTf0R1#8#8p=2f3R2f2R3f1R4'V;11p=0%31#8p=?%81#3p=5p,2fxR5g00GmR6g00Hh3Yg00IfR7#8R8#3R9#@R:%28R;#8#2R<#@R=#6R>'RR?%@;#6#M\>R@g00JKRAg00JiRB/=3RC%77RD/=3%78%7<'GR<,E3';R8f4RE/X2/=<R<g00KGRF%U6RGf7RHf5RI,9=RJ%SERKCCg00KgRL31%QERMP>f:RNg00LGRO1<:Dd94:DPIC0P>f;RP%89#7RQPO1<:Qd54:RRf8,9=RSC0P>f<RT%39#7R9PO1<:9d54:19=BRUC0P>f=RV%37RW#2#7RXPO1<:Xd54:f9,9=RYC0P5f?RZ%?;#2#5#3,L6%?W#5#3#5#3#5#3#?#2#7'Kf>RWPVD>P5P1PN1HAAR6PAPAPBPPCI%J63F9NWTPVD>R65AGP>P1PR19=TRRC0%6:RGg00Lc9OG1W<?PZ1RG';';X7?,B?[[[[[[[[[^8>^0A]5^9@]2]6g00MfRB%61R;%64R[P0%63?1411:231:2451AR0[1:341:3151A%62?134[R\%6E?123\0AD341P1n2001000000120000000W4W3W0P\^4[^3;^0BP1P=%87#2#5#5#2#5#2#5#3#2#2#7R7,9=RBA4=7OR;1TA71:=B1:=;51AdO4b1A1>B;P>PBg00NDRBPHPJPKCC=1FLP>PNA4:DOPIC0P>PPA4:QORQPSC0P>PTA4:9OPUC0P>PVA4:XOPYC0P5PZf@PWPVD>=AB6P>P1PQPRC0/;G';X7?,B?[[[[\M[\<\8\C^8>^0A^5A^9@^2@^6?X;>P4P;P1EWb1b:o"). Qed.

  Lemma memset_post_mem : forall (M : word -> option byte) (d n : Z),
    (0 <= d)%Z -> (d + n <= 2 ^ 64)%Z ->
    (forall i, (0 <= i < n)%Z -> zf M d [(0, n)]%Z (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 0))
    /\ (forall x : word, (bv_unsigned x < d \/ d + n <= bv_unsigned x)%Z -> zf M d [(0, n)]%Z x = M x)
    /\ mem_grows M (zf M d [(0, n)]%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Memset ()) ["Contract"] "g00Oko"). Qed.

  Corollary memset_at : forall model regs (M rom : word -> option byte) (d n : Z) (ret : word) (S : TSet),
    md_pure model ->
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    (forall regs', getr regs' 10 = Z_to_bv 64 d -> regs_agree (fun r => In r memset_clob) regs regs' ->
       realizes SEGS (mkCfg (mkst regs' ret (zf M d [(0, n)]%Z) rom) model) S) ->
    realizes SEGS (mkCfg (mkst regs (0x10a230 : word) M rom) model) S.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Memset ()) ["Contract"] "h01nh11Hh21Mh31Sh42b1h52b2h61dh75modelh84regsh95regs'h:3reth;3romh<3RLTh=1bh>1rp;3p;1p;2p;4p;5p;6g00Q2j3ZTg0013j18Tg001Xj11Tg002=j1ATg002[j17Tg003>j2PTg003jj1NTg00R3j1LTg004Lj2>Tg004hj16Tg005Fj2ETg005cj2CTg006?R0j2YTg006Zj2UTg0077j1TTg0086j29Tg008\j1QTg009<j4BTg00:<j30Tg00:Vj1OTg00;Nj2;Tg00<1j34Tg00CCj3MTg00CZj3KTg00?Gj2HTg00?gj4GTg00@Gj1FTg00@gj3ITg00AGj3JTg00>Nj5=Tg00S2j2@Tg00Sgj3<Tg00<Tj2DTg00=Tj2RTg00E0j2:Tg00EZj3STg00F>j2XTg00FXj6WTg00G4j2VTf0R1#8#8p=3f3R2f2R3f1R4'V;01p=2%11#8p=?%81#1p=5p,2fxR5g00GmR6g00Hh3Zg00TfR7g00IfR8#8R9#1R:#AR;%39R<#8#3R=#AR>#7R?'PR@%A<#7#N\?RAg00JKRBg00U\RCf7RD#LREg00JiRFf4RG'>RH%68RI/>G%69%6='ER=,CG'YR9f6RJf5'U/>=R=g00KGRK%T6RLf9RM19>DRN%QJROCBg00KgRP30%OJRJP?f<RQg00LGRR1;;Id94;IPDC2P?f=RS%8:#6RTPR1;;Td54;RUf:,9>RVC2P?f>RW%1:#6R:PR1;;:d54;19>FRXC2P?f?RY%18RZ#3#6R[PR1;;[d54;f;R\,9>R]C2P?P1PU19>WRUC2%7;R^g00Lc9M^1W>fBR^;K4R_P5P3PWf@R`1HBBRaPBPBPFPYCG%Fa3I5J^fARaD=fD'@RF=<LS[[^9@P5Pa%?<#3#5#1,D6%?Z#5#1#5#1#5#1#?#3#6'RP`PYD=/@^=<L\[[[[[[[[[[[]3^:?^0B]6^;A]2]8]7g00MfRL%71RZ%74R6P0%73?0411:231:2450BR0[1:341:3150B%72?034[R<%7G?023\0AS341P1n2001000000120000000W5W4W0P<^56^4Z^0LP1P>%88#3#5#5#3#5#3#5#1#3#3#6R8,9>RLA4>8RRZ1XB81:>L1:>Z50BdO4b1A0?LZP?PLg00NDRLPMPNPOCB=0KPP?PQA4;IRPDC2P?PSA4;TRRTPVC2P?PWA4;:RPXC2P?PYA4;[RP]C2P?P1PTPUC2A<LFS\_[^9@P5PafCP`PYD=/@^=<L\[[[[[\J[\=\9\H\E^3C^:?^0B^6B^;A^2A^8@^77X=?P4PZP1EWb1b<o"). Qed.
End Contract.
