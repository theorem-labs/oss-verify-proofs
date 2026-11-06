(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocTree MallocFacts_A MallocHINV Malloc_fp MallocFacts_AS ASlot_I ASlot_M0 MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RF_am_P HP_RF_alloc_meta HP_RASlot_M6.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_alloc_slot () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.MallocBlocks.block"; "Corelib.Numbers.BinNums.N"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.MallocBlocks.AREACH_from"; "OSSVerify.KrLib.U.HP_RMallocRep.ref_reserved"; "OSSVerify.KrLib.Heap.MallocFacts_A.MFACTS_g"; "Stdlib.NArith.BinNat.N.lt"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "OSSVerify.KrLib.U.HP_RASlot_I.ras_pre2"; "OSSVerify.KrLib.Heap.Malloc.set_tick"; "OSSVerify.KrLib.Heap.Malloc.FUEL"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma ras_pre2_intro : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_slot ()) "Pst,$0.PLB,(1.$2.)Pt,$3.Psc,$4.Pn,$4.P,(5.$6.R5.R4.)P,(7.$6.R6.R5.)P,(8.(9.R7.)R5.)P,(:.(;.=R5.)(<.R5.+30.))P,(:.(;.=R5.)(<.R5.(=.+2.+20.)))P,(;.(>.R6.+4.)(?.+10.(10.R7.)))(11.R;.(12.R9.R;.)R8.R7.$13.)")
(* [comment removed for export] *).
Proof.
  intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
  - exists LB. split; [exact AR| apply ist_top; exact TT].
  - apply ER_refl_tick.
  - apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

#[using="Type"] Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof.
  unfold ralloc_slot_stmt. intros fuel.
  exact (ralloc_slot_ok ram_pre ralloc_meta_spec MallocFacts_inv4.ist_ampre_proof fuel).
Qed.

End RP_1.
