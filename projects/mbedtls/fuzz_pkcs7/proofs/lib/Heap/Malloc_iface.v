(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep MallocHINV MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_Malloc_iface () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.MallocBlocks.block"; "Corelib.Init.Logic.and"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.strip"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "OSSVerify.KrLib.Heap.MallocRep.mrep"; "OSSVerify.KrLib.Heap.MallocHINV.HINV_from"; "OSSVerify.KrLib.Heap.MallocRep.agent_reserved"; "OSSVerify.KrLib.Heap.Prog.ps_brk"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "MEDTAB"; "medtab_cells"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AGP : Z := 0x1a800.


      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MEDTAB : Z := 0x1a060.

(* [comment removed for export] *)
Definition medtab_cells : list cell := [C1 (Z_to_bv 8 28); C1 (Z_to_bv 8 24); C1 (Z_to_bv 8 20); C1 (Z_to_bv 8 32)].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HEAP (s : PState) (LB : list block) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_Malloc_iface ()) "(0.$1.Lst,$1.(0.(2.$3.)LLB0,(2.$3.)(4.(5.$3.R1.O2.)(4.(6.$1.(7.R2.)(8.O3.))(4.(9.R2.O1.)(4.(:.$;.R2.(<.O3.)R1.)(=.$>.O1.$?.$10.)))))))")
(* [comment removed for export] *).


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition in_block (LB : list block) (a : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bptr_eqb (p q : bptr) : bool :=
  aptr_eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).
(* [comment removed for export] *)
Definition lb_remove (p : bptr) (LB : list block) : list block :=
  filter (fun b => negb (bptr_eqb (blk_id b) p)) LB.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
