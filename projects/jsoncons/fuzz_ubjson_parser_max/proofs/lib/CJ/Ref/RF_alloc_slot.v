(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocTree MallocFacts_A MallocHINV Malloc_fp MallocFacts_AS ASlot_I ASlot_M0 MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMalloc_fp RAllocSlot_iface RASlot_I RF_am_P RF_alloc_meta RASlot_M6.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_alloc_slot () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RAllocSlot_iface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."], [["1list"; "2and"; "3N"; "3Z"; "0LB"; "0RUNp"; "4as_inv2"; "5AREACH_from"; "5block"; "6MFACTS_g"; "7ras_pre2"; "8ralloc_slot_stmt"; "9ref_reserved"; ":FUEL"; ":mstate"; ":s_tick"]; [":set_tick"; ":size_class"; ";lt"; "<add"; "<le"; "<lt"; "<mul"; "<pow"; "0n"; "0sc"; "0st"; "0t"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma ras_pre2_intro : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_alloc_slot "QN'>'0&8%211'2'3'7v5&<r5r4%544321'9r6%23615&B&?r7%211%421:'1&Dz%221>&E+Q@%22A1%7241&G+2+Q0%3221%82G1%=2:1&C+4%22G1&F+@&A%11G%4231%E261&:r;&@r9%2213r8&=%76Q;632Q11p091p0C1p0J1p0Q31p0Q91p0Q=1pQBQD1pQDQE1pQHQG1p:QI1pQFQM1").
Proof.
intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
- exists LB. split; [exact AR| apply ist_top; exact TT].
- apply ER_refl_tick.
- apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.
Theorem ralloc_slot_spec : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_alloc_slot "6&;v5&:%112'6%53421").
Proof.
unfold ralloc_slot_stmt. intros fuel.
exact (ralloc_slot_ok ram_pre ralloc_meta_spec MallocFacts_inv4.ist_ampre_proof fuel).
Qed.
End CEIL_WRAP_1.
