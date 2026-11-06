(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SpinAlgX () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8wr_indexC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_nodeC13~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6fdchanC13~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall4fd32C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim;buf_modeledC13~~~I47Corelib4Init5Peano2le00C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02I47Corelib4Init5Logic3and00C47Corelib4Init6Specif9proj1_sigC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7wr_fullC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg=node_write_chC13~~~K47Corelib4Init6Specif3sig01K47Corelib4Init5Logic3and01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg:t_write_chC13~~~C47Corelib4Init9Datatypes6lengthI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init6Specif3sig00".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section BmKitW. Context {bmK : BMode}.   (* [comment removed for export] *)
Lemma srz_write_ch : forall segs scfg ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes segs scfg
       (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes segs scfg (mkCfg ms model) (t_write_ch ch buf T).
Proof.
ltac2:(KReplay.run1 (kr_t_SpinAlgX ()) ["BmKitW"] "p'0h01nh11ih23H32h33Hbmh42Hch54Hfdch62Hgh72Hhh85Hlazyh93Hn1h:3Hn2h;3Hnbh<3Hnoh=2Hrh>4Hsvch?1Th@1ai001ahA3bufhB2chhC2fdhD5modelhE2mshF4scfghG4segshH2x8i011li021si031xp;1p;3p;2p;5p;4p;Bp;;p10000p4p70g000^R0p4p7210p8g001:R1p4p711g002FR2p4p7511110p8g003Qj1=Tg0041j12Tg004Vj1>Tg0054j1@Tg005Wj1CTg0069j1UTg0070j1NTg007Rj31Tg007lj2ITg008Lj1HTg009Dj1GTg009dj3ETg00:lj1DTg00;ej1XTg00<kj2BTg00=Mj2VTg00>7j1TTg00>Uj2<Tg00?Sj1?Tg00@2j3MTg00A7j1LTg00BDj28Tg00B^j39Tg00C=j24Tg00D5j25Tg00E5j16Tg00F2j23Tg00Fgj57TP1j1JTg00H3j1KTg00HiR1j2:Tg00IDj3;TP0j4FTg00Idj2OTg00JolBPTg00L@j4ATg00L\j4QTP2l;RTg00M7j3STg00NEj2WTf2R2f1R0f0R3'W'8p=0g00Ne#=g00Odg00P^g00Qeg00R[#2#2#2R4#2#2#2R5#>R6#@R7%>4#@R4#=R8g00S@%C7R9f5R:#U%N7311I77R;#=f6R<#H%G;31f7R;9E<:%D;=17;f:R=#X1B7<519g00TH1V6;%T531f<R5g00TfR6'<=17=%C8f=R9%?6R6,<9%?6,<93Mf8R>,B831f9R8#LA064=g00UER?1863R@A0049p,3bmKRAfERBfDRCfCRDf>RE9942,44'5#6fBRF'3P9D7[[]0PAPDPFfARGf@RH'3RI%J5RJP4g00Udf?RK#KA034E,:@X0?RL=;?3=949RMCFX1J144M,5F#6/3GX1JP5VJ1O50PFPDPGPHPKPEP9P5P=P8P>P;P<P:f4R<f3R;P2P0MBPg00VZP?PLPAPBPCA034K,:@X0?=;?3=94E,44,5D#6/3FP9D7P3A034H,:@P11860A004GPAfIR1fHfGA034D,:@X0?RHP?PHP2P3CA5;?=94F,44'5#6fFR2'3PGD7P3186;A0<4CP8P:P0P3O3PAfLfKfJA0342,:@X0?R@P?P@P:186:A0:4BP0P3CQCA5;?=94B,44'5#6/31PCD7eW:W9P0P3O2n2001100000120101101W@X0?P0P3O2n2001102000121103100X1JM;RPAPDPFPIf;9SE5D7eW4W;W3W=W6W<W>W2W5W8W7W?WAXH7XB7WCWDWEWFWGo"). Qed.

(* [comment removed for export] *)
End BmKitW.
