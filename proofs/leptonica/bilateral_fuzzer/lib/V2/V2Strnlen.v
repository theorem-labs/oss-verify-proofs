(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import Frame.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Strnlen.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocCode V2RelocSites V2RelocImg V2MemcpyBase V2Memchr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Strnlen () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI5ARocqVerifyHarness?AgentSubmission2V28V2Memchr5mchrH00C5ARocqVerifyHarness?AgentSubmission2V28V2Memchr=mchrH_genericC6ARocqVerifyHarness?AgentSubmission6Common4Musl7Strnlen;ref_strnlenC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okC45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstI5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00C5ARocqVerifyHarness?AgentSubmission6Common<RefMemcpyLib8keeps_csI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C6ARocqVerifyHarness?AgentSubmission6Common9Leptonica5Frame9frame_modI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocCode7v2_codeC5ARocqVerifyHarness?AgentSubmission2V2<V2RelocSites8v2_sitesC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg6v2_imgK47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00C5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segments".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1. Context {fx : FPState}.
Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x125d0 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x43a08 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
ltac2:(KReplay.run1 (kr_t_V2Strnlen ()) ["VP1"] "h01nh11Kh23bufh33memh44regsh53reth63romh71sh82sph91Hh:3HOKh;2b1h<2b2h=4mem'h>5regs'h?3RLTh@1bp;1p;2p;5p;6p;?p;4p;3g0000j10Tg000Uj1HTg0013j1;Tg001Vj1bTg0028j1XTg002Xj16Tg003=j2VTg003ij5UTg004aj6RTg005_l?NTg006cj21Tg007Mj2ATg007jj2aTg008Fj1]Tg009Ej13Tg009cj2ETg00:@j2?Tg00:fj4JTg00;fj32Tg00<@j2GTg00=@j2TTg00=]j2CTg00>9j2QTg00>Yj1PTg00?9j2OTg00?Sj1MTg00@Kj2@Tg00@nj35Tg00AQj2LTg00BKj5FTg00CDj3ITg00D?j2KTg00E@j2STg00E`j4`Tg00F@j1_Tg00F`j3^Tg00G@j3\Tg00HER0j2>Tg00H`j2BTg00I:j3YTg00I^j2ZTg00J8j6[Tg00JTj1DTg00K3j2WTf0R1#0#0p=:%D1#D#D#Dp=9%61#0p=<%01#6p=8%61#6p=7%01#0#0#0p==f3R2f2R3f1R4'W;21p=4g00KlR5#0R6#0R7#0R8#:R9#0#HR:#;R;%H8#;R<#b[R=%X<R>g00LQR?%66R@#HRA/V;RBf8RCf7RDf5REf4RFP2DURGp,2fxRHg00LoRIg00Mgg00Nbg00O_f9RJPCPDf6RKPEPFP2P3P4PJPCPKPEPFP1ERM?NW:X5;W4X6=X0?W1W2X8;X7;W3g00PX11:CRL/AE'aRMg00Q6RN%]IROf:RP%39R9,EL,?:RLg00QV#9#9#9#9#9#9#9#9RQCJg00R5RR32%<8R8#6#:RS#8#7#=#3%67#7#:R7#0#7#8,GI'A%<S#:#=#3%67#7#<,GI'A'T11:J/E9R7'Cf;,1:RS1Q<J#P'A11:PR</E9'C1C<S'OR<%MEREP;PD%35RSg00RURT1@ASd55APKC4P;PC%36R6PT1@A6d55Af=RUC4P;PJ%0@#3RVPT1@AVd55ARWf?RXC4P;PP%6@#3R@PT1@A@d55Af<RY,?:RZC4PHPU%08#8#8,GI%75#:#7#7#8#:#=#3'LfDRIf>R8DFPHP4PYP1P8DFRY5IO1KU4ROP;P4PWf@,?:RWC41S;?R[P;P?fB,1:/E9,?:P9C`%_[3^9\I1R['>'>'>X==,B=X>B,BB[[[[[[[[[^:G^5;^4B^6=^0?^1?^2>^8;^7;^3=g00S1R9%;1R\%;4R]P0%;3?2411123112452?R0[1134113152?%;2?234[R^%;F?223\0AY341P1n2001000000120000000W<W;W0P^^<]^;\^09P1P:%=5#7#<#<#=#<#:#3R9,?:R\A5:9TR]1Z?911:\11:]52?dO4b9A2;\]P;P\g00SOR\PPPLPQCJ=2NR%:5#<#8#8#7#8#=#3/C7P;PDA5ASTPKC4P;PCA5A6TPUC4P;PJA5AVTRVPXC4P;PPA5A@TPZC4PHPUfEPIP8DF=I\YP;P4PVPWC4/>[,>O'>X==,B=X>B,BB[[[[\E\<[[\M\G^5;^4B^6=^0?^1?^2>^8;^7;^3=X@;P4P]P1E[b9b?o"). Qed.
End VP1.
