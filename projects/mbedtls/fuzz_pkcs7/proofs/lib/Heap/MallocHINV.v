(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocRep MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocBlocks.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MallocHINV () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Heap.Malloc.ceil_ok"; "HINV_from"; "OSSVerify.KrLib.Heap.Malloc.minit"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Heap.MallocBlocks.block"].


(* [comment removed for export] *)
Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.
Notation HINV := (HINV_from agent_reserved).

Lemma HINV_from_init : ltac2:(CDefT.buildp (gd_tbl_MallocHINV ()) "Presv,(0.(1.$2.$2.))Ppbrk,$2.Psecret,$2.Pcanary,$2.Pceil,$2.P,(3.(4.=R3.)(5.R3.(6.+2.+40.)))P,(3.(4.=R3.)(5.R3.(6.+2.+40.)))P,(7.R3.)(8.R8.(9.R6.R5.R4.R8.)R7.(:.$;.))")
(* [comment removed for export] *).
Proof. intros. split; [exact I | apply areach_init; assumption]. Qed.


Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.
