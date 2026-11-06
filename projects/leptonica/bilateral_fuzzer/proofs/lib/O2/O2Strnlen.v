(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Strnlen.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc O2RelocCode O2RelocSites O2RelocImg O2MemcpyBase O2Memchr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Strnlen () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI59OSSVerify5KrLib2O28O2Memchr5mchrH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Memchr=mchrH_genericC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl7Strnlen;ref_strnlenC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib6Common9Leptonica5Frame9frame_modC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C45stdpp9bitvector;definitions5bv_eqK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2RelocCode7o2_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2<O2RelocSites8o2_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg6o2_imgC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1. Context {fx : FPState}.
Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x125a0 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x36fe4 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
ltac2:(KReplay.run1 (kr_t_O2Strnlen ()) ["VP1"] "h01nh11Kh23bufh33memh44regsh53reth63romh71sh82sph91Hh:3HOKh;2b1h<2b2h=4mem'h>5regs'h?3RLTh@1bp;1p;2p;5p;6p;?p;4p;3g0000j11Tg000Uj1GTg0013j1;Tg001Vj1aTg0028j1XTg002Xj14Tg003=j2VTg003ij5UTg004aj6PTg005_l?LTg006cj22Tg007Mj2@Tg007jj2`Tg008Fj1\Tg009Ej16Tg009cj2DTg00:@j2>Tg00:fj4ITg00;fj37Tg00<@j2FTg00=@j2TTg00=]j2BTg00>9j2QTg00>Yj1OTg00?9j2NTg00?Sj1MTg00@Kj2?Tg00@nj38Tg00AQj2KTg00BKj5ETg00CDj3HTg00D?j2JTg00E@j2RTg00E`j4STg00F@j1_Tg00F`j3^Tg00G@j3]Tg00HER0j2=Tg00H`j2ATg00I:j3[Tg00I^j2YTg00J8j6ZTg00JTj1CTg00K3j2WTf0R1#1#1p=0%C1#C#C#Cp=:%41#1p=<%11#4p=9%41#4p=3f3R2f2R3f1R4'W;71p=5g00KlR5#1R6#1R7#1R8#0R9#1#GR:#;R;%G8#;R<#a[R=%X<R>g00LQR?%46R@#GRA/V;RBf8RCf7RDf5REf4RFP2DURGp,2fxRHg00LoRIg00Mgg00Nbg00O_f9RJPCPDf6RKPEPFP2P3P4PJPCPKPEPFP1EPM?LW:X5;W4X6=X0?W1W2X8;X7;W3g00PX12:CRL/@E'`RMg00Q6RN%\IROf:RP%69R9,DL,>:RLg00QV#:#:#:#:#:#:#:#:RQCIg00R5RR37%<8R8#4#0RS#9#3#0#0#6%47R7#3#0RT#1#3#9,FI'@%<S#0#0#0#6%4T#3#<,FI'@'T12:J/D9RT'Bf;,2:RS1Q<J#O'@12:PR</D9'B1B<S'NR<%MEREP;PD%65RSg00RURU1?ASd58APKC5P;PC%66R6PU1?A6d58Af=RVC5P;PJ%1@#6RWPU1?AWd58ARXf?RYC5P;PP%4@#6R@PU1?A@d58Af<RZ,>:R[C5PHPV%18#9#9,FI%35#0#3#3#9#0#0#0#6'KfDRIf>R8DEPHP4PZP1P8DERZ5HO1JV4ROP;P4PXf@,>:RXC51R;?R\P;P?fB,2:/D9,>:P9CS%_\3^9]I1R\'='='=X==,A=X>B,AB[[[[[[[[[^:G^5;^4B^6=^0?^1?^2>^8;^7;^3=g00S1R9%;1R]%;4R^P0%;3?7411223122457?R0[1234123157?%;2?734[R_%;F?723\0A[341P1n2001000000120000000W<W;W0P_^<^^;]^09P1P:%45#9#<#3#3#3#<#9#0#6R5,>:R9A8:5UR]1Y?512:912:]57?dO4b9A7;9]P;P9g00SOR9PPPLPQCI=7NR%17#9#9#<#<#0#0#6/BTP;PDA8ASUPKC5P;PCA8A6UPVC5P;PJA8AWURWPYC5P;PPA8A@UP[C5PHPVfEPIP8DE=H9ZP;P4PWPXC5/=\,=O'=X==,A=X>B,AB[[[[\E\<[[\M\G^5;^4B^6=^0?^1?^2>^8;^7;^3=X@;P4P]P1EZb9b?o"). Qed.
End VP1.
