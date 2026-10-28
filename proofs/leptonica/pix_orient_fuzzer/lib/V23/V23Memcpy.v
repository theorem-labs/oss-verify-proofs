(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Memcpy.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocCode V23MemcpyBase.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Memcpy () := "C6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memcpy:ref_memcpyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I6ARocqVerifyHarness?AgentSubmission6Common4Musl:MemcpyBase3mcH00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC5ARocqVerifyHarness?AgentSubmission6Common5Hoare6ret_okK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfC45stdpp9bitvector;definitions7Z_to_bvC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc2rlC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4mkstC5ARocqVerifyHarness?AgentSubmission6Common7CatExec6wbytesI5ARocqVerifyHarness?AgentSubmission6Common6CatSim6msteps00C5ARocqVerifyHarness?AgentSubmission6Common<RefMemcpyLib5keepsI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4getrC5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23<V23RelocCode8v23_codeK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00C5ARocqVerifyHarness@ProcessOversightKTgt_pix_orient_fuzzer_ubsan1M?loaded_segments____________________".
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section Contract.
  Context {fx : FPState}.

  Theorem ref_memcpy : forall (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte)
      (rom : word -> option byte) (HOK : mcH mem0 dst src n bs) regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x11e154 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Memcpy ()) ["Contract"] "h01nh11Hh23HOKh32b1h42b2h52bsh63dsth74mem0h84regsh95regs'h:3reth;3romh<3srch=3RLTh>1bp;3p;1p;6p;2p;5g0000j3PTg0012j16Tg001Wj1;Tg0025j15Tg002Xj1NTg003:j1JTg003Zj6FTg004[j10Tg005@j2DTg005lj1CTg006dj17Tg007Bj29Tg007ej2ATg008Kj1OTg009Jj2MTg00:Jj2ITg00;Dj5:Tg00<=j3GTg00=7j3>Tg00>2j2ETg00?0R0j2@Tg00?Kj2=Tg00?ej33Tg00@?j28Tg00@ij3HTg00AMj3?Tg00B0j2KTg00BJj6BTg00Bfj2LTf0R1#6#6p=1f5R2f4R3f3R4f2R5f1R63?'L;31p=2%01#6p=<%61#0p=4p,2fxR7g00C_R8g00DZ3Pg00EXR9#6R:#1R;#6#1#;R<#5R=%;;#5R>#N[R?g00F=R@%J>R>P8P2P3P4P5P6EFRA%0:R:#;RB/D=RC%C1RDP=P5PB%79REg00F[RF19BEdP6E2P=P4PB%6:#7RGPF19BGdf9RHE2P=P3PB%0:#7R:PF19B:dPHE2P=P2PB%09RI#1#7RJPF19BJd1A<HRKE2%O8P7f7RL%0;#1#1#<,M8%0I#1#<#4#0#4#0#4#1#7'If>RIPHD:P7P1f6f=f:5GIPHD:R83>1EL1R;'@X9C,=C[[[[[^:=]8]2^;?]5]0^<=^6=]7g00G7RM%51RN%56ROP0%55?3611845184653@R0[1856185153@%54?356[RP%53?345\0AH561P1n2001000000120000000W4W3W0PP^4O^3N^0MP1P<%19#4#0#0#<#1#4#4#4#4#1#7R9,A<RMA?<9FRN1K@918<M18<N53@dO4b1A3=MNP=PMP=P5PBPEPFP6E2P=P4PBPGPFPHE2P=P3PBP:PFPHE2P=P2PBPJPFPKE2g00GUP7PLf?PIPHD:;>8/@;X9C,=C[[[[\D^:=^8C^2A^;?^5>^0@^<=^6=^7?X>=P6PNP1EBb1b=o"). Qed.
End Contract.
