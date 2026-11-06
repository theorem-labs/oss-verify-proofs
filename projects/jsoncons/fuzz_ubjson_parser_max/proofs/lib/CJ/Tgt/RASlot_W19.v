(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RASlot_W19 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RASlot_W2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1list"; "1option"; "2and"; "2eq"; "2ex"; "3Z"; "0F"; "4machine_state"; "5bvmap"; "0RUNp"; "6evt"; "7mkR"; "7stk"; "8MS"; "8ret_pc"]; ["9mem_inv"; ":alloc_ceiling"; ";rw_cells"; "<mstate"; "=rsegs"; ">rta_frame"; "?RSSP_GUARD"; "?rmrep"; "@seg_rom"; "Aadd"; "Ale"; "Asub"; "0a0"; "0a1"; "0a1'"; "0a2"]; ["0a2'"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0gp"; "0junk"; "0lo"; "0m"; "0ms'"; "0rav"; "0s0"; "0s0v"; "0s1"]; ["0s10"; "0s11"; "0s1v"; "0s2"; "0s2v"; "0s3"; "0s3v"; "0s4v"; "0s5"; "0s5v"; "0s6"; "0s6v"; "0s7"; "0s7v"; "0s8"; "0s8v"]; ["0s9"; "0s9v"; "0sp"; "0st'"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma ras_ret0 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RASlot_W19 "UL'R5yR0%211&9y5%2213yQ0%711'2y8%:11%311p0:1'1%114'C'6&Gv:r2r4%43321&@&Dr5%3221&Br6&I&R6rQA%22N1-T@%5221&ErCrBrAr@r?r>r=r<r;r:r9%<=LF;:987654321%E4HD>1&=r7rQB%F2QB1%H21D%54N4Q11&J&A%11Q6%321Q1&KrQD%O2QK1+T@%4221%92Q41&;'8'5'3'4r3&>&<rQHrQGrQFrQErQCrQ@r1rQ=rQ<rQ;rQ:rQ9rDrErFrGrHrIrJrQ1rQ0rOrNrMrL%JOQKIHGFQ6EQLQMDR>CBA@?>QN=<;:987654321&?%11QM(0%11S3&H%11R@%Q277R15R03QO1%Q53Q8Q41%R=2S9Q2%QK4RDR2QO1%Q9231qR2S;1%Q<2S<1qQNS=1%Q>2S>1qRHQ@1&R4%RF2SBQ8%RH21RD%32SD1rQ?rQ>rQ8rQ7rQ6rQ5rQ4&F%<2SM1rQ3rQ2rK%QKOQ:=R7QFR@S4QE<;QCQBQAQ@Q?:9876432Q7Q6Q5Q4Q3Q21Q8Q9+cdj8%B2T31%QO73RK1RJQ0RIN%R63S?E1p0R81p0R?1p0RD1p0RK1p0SB1p0SG1pRDSM1pT8SO1pRBT11pRFT41pR>T:1p@T=1pRJTA1pRNTB1pS6TC1pS:TD1pS>TE1pS@TF1pSDTG1pSHTH1pSLTI1pT0TJ1pT4TK1pU0TL1pTLTM1pTJTN1pTHTO1pTFU01pS4U11pS2U21pT2U31pSNU41pSJU51pSFU61pSBU71pS<U81pS8U91pR<U:1pR:U;1pR8U<1pR6U=1pR4U>1pR0U?1pQLU@1pQJUA1pS0UB1pRLUC1pTDUD1pTBUE1pT@UF1pTNUG1pR@UH1pT6UI1").
Proof.
intros until lo. intros MR' MI FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
(pose_ceil; unfold RSSP_GUARD, rta_frame in *).
step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
step. step. step. step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 2 eexists. split; [reflexivity| exact ST].
Qed.
End CEIL_WRAP_1.
