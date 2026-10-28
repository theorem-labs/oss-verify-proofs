(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import Frame.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Strnlen.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocCode V23RelocSites V23RelocImg V23MemcpyBase V23Memchr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Strnlen () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI5ARocqVerifyHarness?AgentSubmission3V239V23Memchr5mchrH00C5ARocqVerifyHarness?AgentSubmission3V239V23Memchr=mchrH_genericC6ARocqVerifyHarness?AgentSubmission6Common4Musl7Strnlen;ref_strnlenC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstI5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00C5ARocqVerifyHarness?AgentSubmission6Common<RefMemcpyLib8keeps_csI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica5Frame9frame_modI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23<V23RelocCode8v23_codeC5ARocqVerifyHarness?AgentSubmission3V23=V23RelocSites9v23_sitesC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg7v23_imgK47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00C5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segments____________________".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1. Context {fx : FPState}.
Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x1ed30 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x11ec28 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
ltac2:(KReplay.run1 (kr_t_V23Strnlen ()) ["VP1"] "h01nh11Kh23bufh33memh44regsh53reth63romh71sh82sph91Hh:3HOKh;2b1h<2b2h=4mem'h>5regs'h?3RLTh@1bp;1p;2p;5p;6p;?p;4p;3g0000j12Tg000Uj1GTg0013j1:Tg001Vj1aTg0028j1XTg002Xj18Tg003=j2VTg003ij5UTg004cj6PTg005cl?LTg006gj23Tg007Qj2@Tg007nj2`Tg008Jj1\Tg009Ij16Tg009gj2DTg00:Dj2>Tg00:jj4ITg00;jj35Tg00<Dj2FTg00=Dj2TTg00=aj2BTg00>=j2QTg00>]j1OTg00?=j2NTg00?Wj1MTg00@Oj2?Tg00A2j37Tg00AUj2KTg00BOj5ETg00CHj3HTg00DCj2JTg00EDj2RTg00Edj4STg00FDj1_Tg00Fdj3^Tg00GDj3]Tg00HIR0j2=Tg00Hdj2ATg00I>j3[Tg00Ibj2YTg00J<j6ZTg00JXj1CTg00K7j2WTf0R1#2#2p=0%C1#C#C#Cp=9%81#2p=<%21#8p=;%81#8p=1f3R2f2R3f1R4'W;51p=4g00L0R5#2R6#2R7#2R8#0R9#2#GR:#:R;%G8#:R<#a[R=%X<R>g00LUR?%86R@#GRA/V;RBf8RCf7RDf5REf4RFP2DURGp,2fxRHg00M3RIg00Mng00Nlg00Olf9RJPCPDf6RKPEPFP2P3P4PJPCPKPEPFP1EPM?LW:X5;W4X6=X0?W1W2X8;X7;W3g00Ph13:CRL/@E'`RMg00QFRN%\IROf:RP%69R9,DL,>:RLg00Qf#9#9#9#9#9#9#9#9RQCIg00RERR35%<8R8#8#0RS#;#1#0#0#6%87#1#0R7#2#1#;,FI'@%<S#0#0#0#6%87#1#<,FI'@'T13:J/D9R7'Bf;,3:RS1Q<J#O'@13:PR</D9'B1B<S'NR<%MEREP;PD%65RSg00ReRT1?ASd57APKC4P;PC%66R6PT1?A6d57Af=RUC4P;PJ%2@#6RVPT1?AVd57ARWf?RXC4P;PP%8@#6R@PT1?A@d57Af<RY,>:RZC4PHPU%28#;#;,FI%15RI#0#1#1#;#0#0#0#6'KfDR8f>R[DEPHP4PYP1P[DERY5HO1JU4ROP;P4PWf@,>:RWC41R;?R\P;P?fB,3:/D9,>:P9CS%_\3^9]81R\'='='=X==,A=X>B,AB[[[[[[[[[^:G^5;^4B^6=^0?^1?^2>^8;^7;^3=g00SAR9%:1R]%:4R^P0%:3?5411323132455?R0[1334133155?%:2?534[R_%:F?523\0A[341P1n2001000000120000000W<W;W0P_^<^^;]^09P1P:%05#;#1#<#1#0#0#<#<#0#6R5,>:R9A7:5TR]1Y?513:913:]55?dO4b9A5;9]P;P9g00S_R9PPPLPQCI=5NR%<I#1#;#0#1#0#0#6/B7P;PDA7ASTPKC4P;PCA7A6TPUC4P;PJA7AVTRVPXC4P;PPA7A@TPZC4PHPUfEP8P[DE=H9YP;P4PVPWC4/=\,=O'=X==,A=X>B,AB[[[[\E\<[[\M\G^5;^4B^6=^0?^1?^2>^8;^7;^3=X@;P4P]P1EZb9b?o"). Qed.
End VP1.
