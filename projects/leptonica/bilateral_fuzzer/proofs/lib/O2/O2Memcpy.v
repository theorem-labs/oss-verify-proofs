(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Memcpy.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc O2RelocCode O2MemcpyBase.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Memcpy () := "C69OSSVerify5KrLib6Common4Musl6Memcpy:ref_memcpyC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I69OSSVerify5KrLib6Common4Musl:MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfC45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2RelocCode7o2_codeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section Contract.
  Context {fx : FPState}.

  Theorem ref_memcpy : forall (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte)
      (rom : word -> option byte) (HOK : mcH mem0 dst src n bs) regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x36a58 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Memcpy ()) ["Contract"] "h01nh11Hh23HOKh32b1h42b2h52bsh63dsth74mem0h84regsh95regs'h:3reth;3romh<3srch=3RLTh>1bp;3p;1p;6p;2p;5g0000j3PTg0012j15Tg001Wj1<Tg0025j14Tg002Xj1NTg003:j1JTg003Zj6FTg004[j10Tg005@j2DTg005lj1CTg006dj16Tg007Bj2:Tg007ej2ATg008Kj1OTg009Jj2MTg00:Jj2ITg00;Dj5;Tg00<=j3GTg00=7j3>Tg00>2j2ETg00?0R0j2@Tg00?Kj2=Tg00?ej31Tg00@?j28Tg00@ij3HTg00AMj3?Tg00B0j2KTg00BJj6BTg00Bfj2LTf0R1#5#5p=3f5R2f4R3f3R4f2R5f1R63?'L;11p=2%01#5p=7%51#0p=9p,2fxR7g00C_R8g00DW3Pg00ERR9#5R:#3R;#5#3#<R<#4R=%<;#4R>#N[R?g00F7R@%J>R>P8P2P3P4P5P6EFRA%0:R:#<RB/D=RC%C1RDP=P5PB%69REg00FURF1:BEdP6E2P=P4PB%5:#6RGPF1:BGdf9RHE2P=P3PB%0:#6R:PF1:B:dPHE2P=P2PB%09RI#3#6RJPF1:BJd1A<HRKE2%O8P7f7RL%0;#3#3#7,M8%0I#3#7#9#0#9#0#9#3#6'If>RIPHD;P7P1f6f=f:5GIPHD;R83>1EL1R;'@X9C,=C[[[[[^:=]8]2^;?]5]0^<=^6=]7g00G1RM%41RN%46ROP0%45?1611845184651@R0[1856185151@%44?156[RP%43?145\0AH561P1n2001000000120000000W4W3W0PP^4O^3N^0MP1P<%09#9#7#7#7#9#9#7#3#6R9,A<RMA?<9FRN1K@918<M18<N51@dO4b1A1=MNP=PMP=P5PBPEPFP6E2P=P4PBPGPFPHE2P=P3PBP:PFPHE2P=P2PBPJPFPKE2g00GOP7PLf?PIPHD;;>8/@;X9C,=C[[[[\D^:=^8C^2A^;?^5>^0@^<=^6=^7?X>=P6PNP1EBb1b=o"). Qed.
End Contract.
