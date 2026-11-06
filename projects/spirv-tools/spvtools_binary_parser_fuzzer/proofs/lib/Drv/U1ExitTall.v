(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec ShapeAlg SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1ExitDefs U1Exit U1ExitT U1ExitTa U1ExitTb U1ExitTc.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1ExitTall () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2or00I59OSSVerify5KrLib3Drv7U1ExitT;exit_pre_tp00C1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC49OSSVerify5KrLib8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib9SRealizes9srealizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv8U1ExitTa<u1_exit_tp_aC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Drv8U1ExitTb<u1_exit_tp_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv8U1ExitTc<u1_exit_tp_cC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrImgWTgt_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State5event00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Theorem u1_exit_tp {fx : FPState} : forall w pend regs mem model code,
  (w = 0x12300a \/ w = 0x12300c \/ w = 0x12300e)%Z ->
  exit_pre_tp w pend regs mem model code ->
  srealizes SEGS (mkCfg (mkst regs (0xd1e54 : word) mem (seg_rom SEGS)) model)
            (t_emit (map (WriteEv (Z_to_bv 64 1)) pend) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
ltac2:(KReplay.run1 (kr_t_U1ExitTall ()) [] "h01Hh13PREh21wh32fxh44codeh53memh65modelh74pendh84regsp;1p;2p;6p;3p;5p;4p;7p10000p4p70g000^R0p4p7210p8g001:j12Tg001_j1?Tg002=j1FTg002`j1PTg003@j14Tg003ej2MTg004Qj1JTg0053j17Tg005QR1j2:Tg005kj65Tg006ij3OTg007Lj1NTg008Aj5DTg0093j2BTg009hj2ETg00:Nj1LTP0j4>Tg00;Dj3ATg00;ij1;Tg00<\j2=Tg00=Pj2CTg00>Dj3<Tg00?>j7ITg00@<j6@Tg00@Zj7KTg00AXj7HTg00BVj3GTf0R0#2#2p=1%40#2p=6%40#4p=3%20#2#2#2p=8g00C0R2f1;G0p=0%20#4p=9g00CNR3g00DER4#2R5#1R6#?#FR7#P%45#?%26#1#?R6#FR5'M%J7\5g00Djf5R8%14#6#1#3#8#8#6#6#7R9'0%14#6#1#3#8#8#3#1#7R:,08%14#6#1#3#8#8#3#6#7R;,08':':P1f6R</0910<:10<;':f7R=P<P8f4R>f3R?f2E5g00E`R@f9RAP<%44#9#1#9#3#6#9#9#9#1#7g00G?5O6RBP8%N@RCDD/B>P7g00G[RD%74,E6#LREP=C>%44#3#3#3#7,E6R49A6?%;>'='C3<[P010=9P2P9P0f8RFP=P<P8P>E5f;RGPFPBP=PCDD/B<P7PDPEPAC>AA684%;<'='C5<@RH[X22P9P=P<P8P>P?E5f:R?PFP=P<P8P>P0FIW1PFP0E@W0P0O110=:10=;':P110F:10F;PAPFP=P<P8P>E5PH[P010A:P2P:P0P?PAPFP=P<E5f=P?PBPAPCDD/BFP7PDPEPGC>AA6=4%;F'='C5<@[X22R@P:PAPFP=P<P8E5f<R:P?PAPFP=P<P0FKW1P?P0E@W0P0O110A;P2P;P@P;PAPFP=P<P8E5P:P?PAPFP=P<P0FHW1P?P0E@W0P0O1n200100000021100011000W0P0O1n200100000021100011000W0X45W6W5W8W7X22X33P0O1W3o"). Qed.
